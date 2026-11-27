module

public import SpectralGeometry.AmmannBeenkerGraph

public section

/-!
# Exact finite-pattern recurrence in the centered octagonal model

The silver-unit sequence already used to prove infinitude has physical
norm tending to infinity and internal displacement tending to zero.
The exact open window has no lattice lift on any of its four pairs of
supporting lines. Consequently every finite set of admitted and
excluded lifts eventually has its complete membership pattern preserved
under translation. No generic repetitivity assumption is needed.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- Integer linear independence of one and the internal irrational coefficient. -/
private theorem recurrence_integer_coefficients (a b : ℤ)
    (h : (a : ℝ) + alpha * b = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    apply irrational_sqrt_two.ne_rational (-2 * a) b
    apply (eq_div_iff (by exact_mod_cast hb : (b : ℝ) ≠ 0)).mpr
    dsimp [alpha] at h
    push_cast
    linarith
  subst b
  simp only [Int.cast_zero, mul_zero, add_zero] at h
  exact ⟨by exact_mod_cast h, rfl⟩

private theorem recurrence_axis_ne (a b : ℤ) :
    |(a : ℝ) + alpha * b| ≠ 1 / 2 + alpha := by
  intro h
  by_cases hs : 0 ≤ (a : ℝ) + alpha * b
  · rw [abs_of_nonneg hs] at h
    have hz := recurrence_integer_coefficients (2 * a - 1) (2 * b - 2) (by
      push_cast
      linarith)
    obtain ⟨ha, hb⟩ := hz
    omega
  · rw [abs_of_neg (lt_of_not_ge hs)] at h
    have hz := recurrence_integer_coefficients (2 * a + 1) (2 * b + 2) (by
      push_cast
      linarith)
    omega

private theorem recurrence_diagonal_ne (a b : ℤ) :
    |(a : ℝ) + alpha * (2 * (b : ℝ))| ≠ 1 + alpha := by
  intro h
  by_cases hs : 0 ≤ (a : ℝ) + alpha * (2 * (b : ℝ))
  · rw [abs_of_nonneg hs] at h
    have hz := recurrence_integer_coefficients (a - 1) (2 * b - 1) (by
      push_cast
      linarith)
    omega
  · rw [abs_of_neg (lt_of_not_ge hs)] at h
    have hz := recurrence_integer_coefficients (a + 1) (2 * b + 1) (by
      push_cast
      linarith)
    omega

/-- None of the eight supporting lines of the open window contains
the internal projection of a lattice point. This also covers excluded lifts. -/
theorem internal_window_boundary_avoided (n : Lattice) :
    |(internal n).re| ≠ 1 / 2 + alpha ∧
      |(internal n).im| ≠ 1 / 2 + alpha ∧
      |(internal n).re + (internal n).im| ≠ 1 + alpha ∧
      |(internal n).re - (internal n).im| ≠ 1 + alpha := by
  have hre : (internal n).re = (n 0 : ℝ) + alpha * (↑(n 3 - n 1) : ℝ) := by
    simp [internal] <;> ring
  have him : (internal n).im = (↑(-n 2) : ℝ) + alpha * (↑(n 1 + n 3) : ℝ) := by
    simp [internal]
  have hsum : (internal n).re + (internal n).im =
      (↑(n 0 - n 2) : ℝ) + alpha * (2 * (n 3 : ℝ)) := by
    simp [internal]
    ring
  have hdiff : (internal n).re - (internal n).im =
      (↑(n 0 + n 2) : ℝ) + alpha * (2 * (↑(-n 1) : ℝ)) := by
    simp [internal]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]
    exact recurrence_axis_ne _ _
  · rw [him]
    exact recurrence_axis_ne _ _
  · rw [hsum]
    exact recurrence_diagonal_ne _ _
  · rw [hdiff]
    exact recurrence_diagonal_ne _ _

private theorem recurrence_abs_lt_iff {x y c : ℝ}
    (hne : |x| ≠ c) (hy : |y| < abs (abs x - c)) :
    |x + y| < c ↔ |x| < c := by
  have h₁ : |x + y| ≤ |x| + |y| := abs_add_le _ _
  have h₂ : |x| ≤ |x + y| + |y| := by
    simpa using abs_add_le (x + y) (-y)
  by_cases hx : |x| < c
  · rw [abs_of_neg (sub_neg.mpr hx)] at hy
    exact iff_of_true (by linarith) hx
  · have hc : c < |x| := lt_of_le_of_ne (le_of_not_gt hx) hne.symm
    rw [abs_of_pos (sub_pos.mpr hc)] at hy
    exact iff_of_false (by linarith) hx

/-- The internal displacement of the existing inflation sequence lies on
the real axis and is an explicit contracting geometric sequence. -/
theorem internal_inflatedOriginNeighbor (k : ℕ) :
    internal (inflatedOriginNeighbor k).val = (((1 - 2 * alpha) ^ k : ℝ) : ℂ) := by
  induction k with
  | zero =>
    apply Complex.ext <;> simp [inflatedOriginNeighbor, internal, basis, Pi.single_apply]
  | succ k ih =>
    change internal (inflate (inflatedOriginNeighbor k).val) = _
    rw [internal_inflate, ih, pow_succ, Complex.ofReal_mul]
    ring

open Filter
open scoped Topology

theorem recurrence_internal_tendsto_zero :
    Tendsto (fun k : ℕ => (1 - 2 * alpha) ^ k) atTop (𝓝 0) := by
  apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
  exact abs_lt.mpr ⟨by linarith [alpha_bounds.2], by linarith [alpha_bounds.1]⟩

/-- For each lattice lift, eventual translations preserve both membership
and nonmembership of the exact window. -/
theorem eventual_admitted_translate (n : Lattice) :
    ∃ N : ℕ, ∀ k ≥ N,
      Admitted (n + (inflatedOriginNeighbor k).val) ↔ Admitted n := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := internal_window_boundary_avoided n
  let d₁ := abs (abs (internal n).re - (1 / 2 + alpha))
  let d₃ := abs (abs ((internal n).re + (internal n).im) - (1 + alpha))
  let d₄ := abs (abs ((internal n).re - (internal n).im) - (1 + alpha))
  have hd₁ : 0 < d₁ := abs_pos.mpr (sub_ne_zero.mpr h₁)
  have hd₃ : 0 < d₃ := abs_pos.mpr (sub_ne_zero.mpr h₃)
  have hd₄ : 0 < d₄ := abs_pos.mpr (sub_ne_zero.mpr h₄)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp recurrence_internal_tendsto_zero
    (min d₁ (min d₃ d₄)) (lt_min hd₁ (lt_min hd₃ hd₄))
  refine ⟨N, fun k hk => ?_⟩
  let t : ℝ := (1 - 2 * alpha) ^ k
  have ht : |t| < min d₁ (min d₃ d₄) := by
    simpa [t, Real.dist_eq] using hN k hk
  have ht₁ : |t| < d₁ := ht.trans_le (min_le_left _ _)
  have ht₃ : |t| < d₃ := ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have ht₄ : |t| < d₄ := ht.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have e₁ := recurrence_abs_lt_iff h₁ ht₁
  have e₃ := recurrence_abs_lt_iff h₃ ht₃
  have e₄ := recurrence_abs_lt_iff h₄ ht₄
  simp only [Admitted, internal_add, internal_inflatedOriginNeighbor, Window,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
  change |(internal n).re + t| < _ ∧ |(internal n).im| < _ ∧
    |(internal n).re + t + (internal n).im| < _ ∧
    |(internal n).re + t - (internal n).im| < _ ↔ _
  rw [show (internal n).re + t + (internal n).im =
      (internal n).re + (internal n).im + t by ring,
    show (internal n).re + t - (internal n).im =
      (internal n).re - (internal n).im + t by ring,
    e₁, e₃, e₄]

/-- A single sufficiently late translation preserves every membership
decision on an arbitrary finite set, including its excluded sites. -/
theorem eventual_finite_pattern_translate (F : Finset Lattice) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ n ∈ F,
      Admitted (n + (inflatedOriginNeighbor k).val) ↔ Admitted n := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert n F hn ih =>
    obtain ⟨N, hN⟩ := eventual_admitted_translate n
    obtain ⟨M, hM⟩ := ih
    refine ⟨max N M, fun k hk v hv => ?_⟩
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hN k ((le_max_left _ _).trans hk)
    · exact hM k ((le_max_right _ _).trans hk) v hv

theorem recurrence_physical_norm_tendsto_atTop :
    Tendsto (fun k : ℕ => ‖position (inflatedOriginNeighbor k)‖) atTop atTop := by
  simpa only [inflatedOriginNeighbor_norm] using
    (tendsto_pow_atTop_atTop_of_one_lt (by linarith [alpha_bounds.1] :
      (1 : ℝ) < 1 + 2 * alpha))

/-- Every finite exact membership pattern has a translated copy beyond
any prescribed physical radius. The center is itself an admitted vertex. -/
theorem finite_pattern_recurrence (F : Finset Lattice) (R : ℝ) :
    ∃ v : Vertex, R < ‖position v‖ ∧
      ∀ n ∈ F, Admitted (n + v.val) ↔ Admitted n := by
  obtain ⟨N, hN⟩ := eventual_finite_pattern_translate F
  have hfar : ∀ᶠ k in atTop, R < ‖position (inflatedOriginNeighbor k)‖ :=
    recurrence_physical_norm_tendsto_atTop.eventually (eventually_gt_atTop R)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hfar
  exact ⟨inflatedOriginNeighbor (max N M), hM _ (le_max_right _ _),
    hN _ (le_max_left _ _)⟩

/-- Arbitrarily many recurring centers beyond a prescribed radius, with
any prescribed nonnegative pairwise physical separation. -/
theorem finite_pattern_recurrence_family (F : Finset Lattice) (R D : ℝ)
    (hD : 0 ≤ D) (N : ℕ) :
    ∃ S : Finset Vertex, S.card = N ∧
      (∀ v ∈ S, R < ‖position v‖ ∧
        ∀ n ∈ F, Admitted (n + v.val) ↔ Admitted n) ∧
      (∀ v ∈ S, ∀ w ∈ S, v ≠ w → D < dist (position v) (position w)) := by
  classical
  induction N with
  | zero =>
    exact ⟨∅, by simp, by simp, by simp⟩
  | succ N ih =>
    obtain ⟨S, hcard, hpattern, hsep⟩ := ih
    let B : ℝ := max R 0 + D + ∑ w ∈ S, ‖position w‖
    obtain ⟨v, hv, hvpattern⟩ := finite_pattern_recurrence F B
    have hsum_nonneg : 0 ≤ ∑ w ∈ S, ‖position w‖ :=
      Finset.sum_nonneg (fun w _ => norm_nonneg _)
    have hvR : R < ‖position v‖ := by
      dsimp [B] at hv
      linarith [le_max_left R 0]
    have hvfar (w : Vertex) (hw : w ∈ S) :
        D < dist (position v) (position w) := by
      have hwbound : ‖position w‖ ≤ ∑ u ∈ S, ‖position u‖ :=
        Finset.single_le_sum (fun u _ => norm_nonneg (position u)) hw
      have htriangle : ‖position v‖ ≤
          dist (position v) (position w) + ‖position w‖ := by
        simpa using dist_triangle (position v) (position w) (0 : ℂ)
      dsimp [B] at hv
      linarith [le_max_right R 0]
    have hvnot : v ∉ S := by
      intro h
      have hbad := hvfar v h
      rw [dist_self] at hbad
      linarith
    refine ⟨insert v S, ?_, ?_, ?_⟩
    · simp [hvnot, hcard]
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ⟨hvR, hvpattern⟩
      · exact hpattern w hw
    · intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with hxv | hxS
      · rcases Finset.mem_insert.mp hy with hyv | hyS
        · exact (hxy (hxv.trans hyv.symm)).elim
        · rw [hxv]
          exact hvfar y hyS
      · rcases Finset.mem_insert.mp hy with hyv | hyS
        · rw [hyv, dist_comm]
          exact hvfar x hxS
        · exact hsep x hxS y hyS hxy

/-- Separation of centers by more than twice a radius separates every lift
in two translated radius-bounded patterns, including excluded lifts. -/
theorem separated_translated_lifts (v w : Vertex) (n m : Lattice) (r : ℝ)
    (hn : ‖physical n‖ ≤ r) (hm : ‖physical m‖ ≤ r)
    (hsep : 2 * r < dist (position v) (position w)) :
    n + v.val ≠ m + w.val := by
  intro heq
  have hp := congrArg physical heq
  simp only [physical_add] at hp
  change physical n + position v = physical m + position w at hp
  have hd : position v - position w = physical m - physical n := by
    calc
      position v - position w =
          (physical n + position v) - (physical n + position w) := by abel
      _ = (physical m + position w) - (physical n + position w) := by rw [hp]
      _ = physical m - physical n := by abel
  rw [dist_eq_norm, hd] at hsep
  linarith [norm_sub_le (physical m) (physical n)]

/-- Every finite membership pattern has arbitrarily many recurring copies
whose entire translated lift sets are pairwise disjoint. The caller can
include candidate neighbors and control sites in F before applying this
theorem; separation then covers those sites, not only the centers. -/
theorem finite_pattern_disjoint_copies (F : Finset Lattice) (R D : ℝ)
    (hD : 0 ≤ D) (N : ℕ) :
    ∃ S : Finset Vertex, S.card = N ∧
      (∀ v ∈ S, R < ‖position v‖ ∧
        ∀ n ∈ F, Admitted (n + v.val) ↔ Admitted n) ∧
      (∀ v ∈ S, ∀ w ∈ S, v ≠ w →
        D < dist (position v) (position w) ∧
          ∀ n ∈ F, ∀ m ∈ F, n + v.val ≠ m + w.val) := by
  classical
  let r : ℝ := ∑ n ∈ F, ‖physical n‖
  have hr : 0 ≤ r := Finset.sum_nonneg (fun n _ => norm_nonneg _)
  obtain ⟨S, hcard, hpattern, hsep⟩ :=
    finite_pattern_recurrence_family F R (D + 2 * r) (by linarith) N
  refine ⟨S, hcard, hpattern, ?_⟩
  intro v hv w hw hne
  have h := hsep v hv w hw hne
  refine ⟨by linarith, ?_⟩
  intro n hn m hm
  have hn' : ‖physical n‖ ≤ r :=
    Finset.single_le_sum (fun a _ => norm_nonneg (physical a)) hn
  have hm' : ‖physical m‖ ≤ r :=
    Finset.single_le_sum (fun a _ => norm_nonneg (physical a)) hm
  exact separated_translated_lifts v w n m r hn' hm' (by linarith)

end
end SpectralGeometry.AmmannBeenker
