module

public import SpectralGeometry.AmmannBeenkerNaturalDynamicalStability
public import Mathlib.Analysis.SpecialFunctions.Sqrt

public section

/-!
# Quadratic finite-time error bound without a spectral gap

The squared difference of the ideal and perturbed solutions obeys
a differential inequality with the square root of the error.
Regularizing that square root by a strictly positive constant and
then removing the regularization gives the sharp norm-Lipschitz
bound in the perturbation strength and elapsed time. The perturbed
trajectory is still an explicit hypothesis, not a postulated propagator.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

@[expose] def naturalTrajectoryError (r i u j : ℝ → TileHilbert Vertex) (τ : ℝ) : ℝ :=
  ‖u τ - r τ‖ ^ 2 + ‖j τ - i τ‖ ^ 2

theorem naturalTrajectoryError_nonneg (r i u j : ℝ → TileHilbert Vertex) (τ : ℝ) :
    0 ≤ naturalTrajectoryError r i u j τ := by
  unfold naturalTrajectoryError
  positivity

theorem naturalTrajectoryError_eq (r i u j : ℝ → TileHilbert Vertex) :
    naturalTrajectoryError r i u j = fun τ =>
      naturalTrajectoryWeight r i τ + naturalTrajectoryWeight u j τ -
        2 * naturalTrajectoryOverlap r i u j τ := by
  funext τ
  unfold naturalTrajectoryError naturalTrajectoryWeight naturalTrajectoryOverlap
  rw [norm_sub_sq_real, norm_sub_sq_real, real_inner_comm (r τ) (u τ),
    real_inner_comm (i τ) (j τ)]
  ring

theorem naturalTrajectoryError_deriv
    (H P : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hs : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y))
    (hp : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (r i u j : ℝ → TileHilbert Vertex) (τ : ℝ)
    (h : naturalFullSolvesAt H r i τ) (k : naturalFullSolvesAt (H + P) u j τ) :
    HasDerivAt (naturalTrajectoryError r i u j)
      (2 * (inner ℝ (i τ) (P (u τ - r τ)) -
        inner ℝ (r τ) (P (j τ - i τ)))) τ := by
  have hsym : ∀ x y, inner ℝ ((H + P) x) y = inner ℝ x ((H + P) y) := by
    intro x y
    simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right, hs x y, hp x y]
  have h1 := naturalTrajectoryWeight_deriv_zero H hs r i τ h
  have h2 := naturalTrajectoryWeight_deriv_zero (H + P) hsym u j τ k
  have h3 := naturalTrajectoryOverlap_deriv H P hs r i u j τ h k
  have hd := (h1.add h2).sub (h3.const_mul 2)
  have he : inner ℝ (i τ) (P (r τ)) = inner ℝ (r τ) (P (i τ)) := by
    rw [← hp (i τ) (r τ), real_inner_comm]
  rw [naturalTrajectoryError_eq]
  have hval : (0 : ℝ) + 0 - 2 * (inner ℝ (r τ) (P (j τ)) -
      inner ℝ (i τ) (P (u τ))) =
      2 * (inner ℝ (i τ) (P (u τ - r τ)) -
        inner ℝ (r τ) (P (j τ - i τ))) := by
    rw [map_sub, map_sub, inner_sub_right, inner_sub_right, he]
    ring
  rw [hval] at hd
  exact hd

private theorem naturalQuadratic_inner_le (P : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (x y : TileHilbert Vertex) :
    |inner ℝ x (P y)| ≤ ‖P‖ * (‖x‖ * ‖y‖) := by
  calc
    _ ≤ ‖x‖ * ‖P y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖P‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left (P.le_opNorm y) (norm_nonneg _)
    _ = _ := by ring


private theorem naturalQuadratic_cross_le (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hn : a ^ 2 + b ^ 2 = 1) :
    a * c + b * d ≤ Real.sqrt (c ^ 2 + d ^ 2) := by
  have hsq : (a * c + b * d) ^ 2 ≤ c ^ 2 + d ^ 2 := by
    calc
      _ ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
        nlinarith [sq_nonneg (a * d - b * c)]
      _ = _ := by rw [hn, one_mul]
  have hz : 0 ≤ a * c + b * d := add_nonneg (mul_nonneg ha hc) (mul_nonneg hb hd)
  have hnn : 0 ≤ c ^ 2 + d ^ 2 := by positivity
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hz] at h

theorem naturalTrajectoryError_deriv_le
    (H P : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hs : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y))
    (hp : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (r i u j : ℝ → TileHilbert Vertex) (τ : ℝ)
    (h : naturalFullSolvesAt H r i τ) (k : naturalFullSolvesAt (H + P) u j τ)
    (hn : naturalTrajectoryWeight r i τ = 1) :
    deriv (naturalTrajectoryError r i u j) τ ≤
      2 * ‖P‖ * Real.sqrt (naturalTrajectoryError r i u j τ) := by
  rw [(naturalTrajectoryError_deriv H P hs hp r i u j τ h k).deriv]
  have h1 := le_trans (le_abs_self (inner ℝ (i τ) (P (u τ - r τ))))
    (naturalQuadratic_inner_le P (i τ) (u τ - r τ))
  have h2 := le_trans (neg_le_abs (inner ℝ (r τ) (P (j τ - i τ))))
    (naturalQuadratic_inner_le P (r τ) (j τ - i τ))
  have hsqrt : ‖i τ‖ * ‖u τ - r τ‖ + ‖r τ‖ * ‖j τ - i τ‖ ≤
      Real.sqrt (naturalTrajectoryError r i u j τ) := by
    unfold naturalTrajectoryError naturalTrajectoryWeight at *
    exact naturalQuadratic_cross_le _ _ _ _ (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _) (by linarith)
  have hm := mul_le_mul_of_nonneg_left hsqrt (norm_nonneg P)
  rw [mul_add] at hm
  linarith

/-- Regularized scalar comparison. A nonnegative differentiable error
with E(0)=0 and E' <= 2*K*sqrt(E) satisfies E(t) <= K²*t².
No derivative of sqrt at zero is used. -/
theorem naturalQuadratic_comparison (E : ℝ → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hE : ∀ s, 0 ≤ E s) (h0 : E 0 = 0)
    (hD : Differentiable ℝ E)
    (hbound : ∀ s, 0 ≤ s → deriv E s ≤ 2 * K * Real.sqrt (E s))
    (τ : ℝ) (hτ : 0 ≤ τ) : E τ ≤ K ^ 2 * τ ^ 2 := by
  have hreg (ε : ℝ) (hε : 0 < ε) : Real.sqrt (E τ + ε ^ 2) ≤ K * τ + ε := by
    let f : ℝ → ℝ := fun s => Real.sqrt (E s + ε ^ 2)
    have hpos (s : ℝ) : 0 < E s + ε ^ 2 := by
      have he := hE s
      positivity
    have hd (s : ℝ) : HasDerivAt f (deriv E s / (2 * Real.sqrt (E s + ε ^ 2))) s := by
      exact ((hD s).hasDerivAt.add_const (ε ^ 2)).sqrt (ne_of_gt (hpos s))
    have hf : Differentiable ℝ f := fun s => (hd s).differentiableAt
    have hle (s : ℝ) (hs : 0 ≤ s) : deriv f s ≤ K := by
      rw [(hd s).deriv]
      apply (div_le_iff₀ (mul_pos (by norm_num) (Real.sqrt_pos.mpr (hpos s)))).2
      have hsq : Real.sqrt (E s) ≤ Real.sqrt (E s + ε ^ 2) :=
        Real.sqrt_le_sqrt (by linarith [sq_nonneg ε])
      have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2 * K by positivity)
      linarith [hbound s hs]
    have hcmp := (convex_Icc (0 : ℝ) τ).image_sub_le_mul_sub_of_deriv_le
      hf.continuous.continuousOn hf.differentiableOn (C := K)
      (fun s hs => hle s (show s ∈ Set.Icc (0 : ℝ) τ from interior_subset hs).1)
      0 ⟨le_rfl,hτ⟩ τ ⟨hτ,le_rfl⟩ hτ
    have hf0 : f 0 = ε := by
      unfold f
      rw [h0, zero_add, Real.sqrt_sq hε.le]
    rw [hf0, sub_zero] at hcmp
    change Real.sqrt (E τ + ε ^ 2) - ε ≤ K * τ at hcmp
    linarith
  have hlim : Real.sqrt (E τ) ≤ K * τ := by
    by_contra! hbad
    let ε := (Real.sqrt (E τ) - K * τ) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have h1 := hreg ε hε
    have h2 : Real.sqrt (E τ) ≤ Real.sqrt (E τ + ε ^ 2) :=
      Real.sqrt_le_sqrt (by linarith [sq_nonneg ε])
    dsimp [ε] at h1
    linarith
  have ht : 0 ≤ K * τ := mul_nonneg hK hτ
  have he := (Real.sqrt_le_left ht).mp hlim
  calc
    E τ ≤ (K * τ) ^ 2 := he
    _ = K ^ 2 * τ ^ 2 := by ring

/-- Finite-time squared error is at most ||P||²*t² for two solutions
with identical normalized initial data. No gap enters the estimate. -/
theorem naturalTrajectory_error_quadratic_le
    (H P : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hs : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y))
    (hp : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (r i u j : ℝ → TileHilbert Vertex)
    (h : ∀ s, naturalFullSolvesAt H r i s)
    (k : ∀ s, naturalFullSolvesAt (H + P) u j s)
    (hr : naturalTrajectoryWeight r i 0 = 1)
    (hR : u 0 = r 0) (hI : j 0 = i 0)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖u τ - r τ‖ ^ 2 + ‖j τ - i τ‖ ^ 2 ≤ ‖P‖ ^ 2 * τ ^ 2 := by
  have h0 : naturalTrajectoryError r i u j 0 = 0 := by
    unfold naturalTrajectoryError
    rw [hR, hI, sub_self, sub_self, norm_zero]
    norm_num
  have hD : Differentiable ℝ (naturalTrajectoryError r i u j) := fun s =>
    (naturalTrajectoryError_deriv H P hs hp r i u j s (h s) (k s)).differentiableAt
  have hbound (s : ℝ) (hs0 : 0 ≤ s) :=
    naturalTrajectoryError_deriv_le H P hs hp r i u j s (h s) (k s)
      ((naturalTrajectoryWeight_constant H hs r i h s hs0).trans hr)
  exact naturalQuadratic_comparison _ ‖P‖ (norm_nonneg _) (naturalTrajectoryError_nonneg r i u j)
    h0 hD hbound τ hτ

/-- Application to a prepared remote plane during free storage.
The reference trajectory is constructed, not assumed; only the
perturbed solution remains a hypothesis. -/
theorem naturalStorage_error_quadratic_le (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (w : ℂ × ℂ) (hw : ‖w.1‖ ^ 2 + ‖w.2‖ ^ 2 = 1)
    (P : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hp : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (u j : ℝ → TileHilbert Vertex)
    (hk : ∀ s, naturalFullSolvesAt (canonicalPlateauHamiltonian + P) u j s)
    (hR : u 0 = naturalStateReal v.val w) (hI : j 0 = naturalStateImag v.val w)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖u τ - naturalStateReal v.val (naturalStoragePair τ w)‖ ^ 2 +
      ‖j τ - naturalStateImag v.val (naturalStoragePair τ w)‖ ^ 2 ≤ ‖P‖ ^ 2 * τ ^ 2 := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    canonicalPlateau_isolated_double_eigenvalue.1
  let r := fun s => naturalStateReal v.val (naturalStoragePair s w)
  let i := fun s => naturalStateImag v.val (naturalStoragePair s w)
  have h : ∀ s, naturalFullSolvesAt canonicalPlateauHamiltonian r i s :=
    fun s => naturalStorage_full_solvesAt v hr hrec w s
  have hnorm : naturalTrajectoryWeight r i 0 = 1 := by
    change naturalStateWeight v.val (naturalStoragePair 0 w) = 1
    rw [naturalStorage_initial, naturalStateWeight_eq v.val hrec]
    exact hw
  have hri : u 0 = r 0 := by
    change u 0 = naturalStateReal v.val (naturalStoragePair 0 w)
    rw [naturalStorage_initial]
    exact hR
  have hij : j 0 = i 0 := by
    change j 0 = naturalStateImag v.val (naturalStoragePair 0 w)
    rw [naturalStorage_initial]
    exact hI
  exact naturalTrajectory_error_quadratic_le canonicalPlateauHamiltonian P hs hp r i u j
    h hk hnorm hri hij τ hτ


end
end SpectralGeometry.AmmannBeenker
