module

public import SpectralGeometry.AmmannBeenkerNaturalStorage
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

public section

/-!
# Gap-independent finite-time stability of bounded graph dynamics

We compare two full real/imaginary Schroedinger solutions with the
same initial state. Symmetry cancels the unperturbed contribution
to their real overlap derivative. If the bounded error is symmetric,
both squared weights are conserved. The resulting squared distance
bound is 2*||P||*time. It is a conservative finite-time estimate,
not a sharp small-time estimate or a uniform spectral protection
claim. Existence of the perturbed trajectory is an explicit hypothesis.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

@[expose] def naturalTrajectoryWeight (r i : ℝ → TileHilbert Vertex) (τ : ℝ) : ℝ :=
  ‖r τ‖ ^ 2 + ‖i τ‖ ^ 2

@[expose] def naturalTrajectoryOverlap (r i u j : ℝ → TileHilbert Vertex) (τ : ℝ) : ℝ :=
  inner ℝ (r τ) (u τ) + inner ℝ (i τ) (j τ)

theorem naturalTrajectoryWeight_deriv_zero
    (H : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hs : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y))
    (r i : ℝ → TileHilbert Vertex) (τ : ℝ)
    (h : naturalFullSolvesAt H r i τ) :
    HasDerivAt (naturalTrajectoryWeight r i) 0 τ := by
  unfold naturalFullSolvesAt at h
  have hd := h.1.norm_sq.add h.2.norm_sq
  have he : inner ℝ (r τ) (H (i τ)) = inner ℝ (i τ) (H (r τ)) := by
    rw [← hs (r τ) (i τ), real_inner_comm]
  rw [inner_neg_right, ← he] at hd
  have hz : 2 * inner ℝ (r τ) (H (i τ)) +
      2 * -inner ℝ (r τ) (H (i τ)) = 0 := by ring
  rw [hz] at hd
  exact hd

theorem naturalTrajectoryWeight_constant
    (H : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hs : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y))
    (r i : ℝ → TileHilbert Vertex) (h : ∀ τ, naturalFullSolvesAt H r i τ)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    naturalTrajectoryWeight r i τ = naturalTrajectoryWeight r i 0 := by
  have hd (s : ℝ) := naturalTrajectoryWeight_deriv_zero H hs r i s (h s)
  have hf : Differentiable ℝ (naturalTrajectoryWeight r i) :=
    fun s => (hd s).differentiableAt
  have hz : ∀ s, deriv (naturalTrajectoryWeight r i) s = 0 :=
    fun s => (hd s).deriv
  have hlo := mul_sub_le_image_sub_of_le_deriv hf
    (C := 0) (fun s => (hz s).ge) hτ
  have hhi := image_sub_le_mul_sub_of_deriv_le hf
    (C := 0) (fun s => (hz s).le) hτ
  linarith

theorem naturalTrajectoryOverlap_deriv
    (H P : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hs : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y))
    (r i u j : ℝ → TileHilbert Vertex) (τ : ℝ)
    (h : naturalFullSolvesAt H r i τ) (k : naturalFullSolvesAt (H + P) u j τ) :
    HasDerivAt (naturalTrajectoryOverlap r i u j)
      (inner ℝ (r τ) (P (j τ)) - inner ℝ (i τ) (P (u τ))) τ := by
  unfold naturalFullSolvesAt at h k
  have hd := (HasDerivAt.inner ℝ h.1 k.1).add (HasDerivAt.inner ℝ h.2 k.2)
  simp only [ContinuousLinearMap.add_apply, inner_add_right, inner_neg_left,
    inner_neg_right, hs (i τ) (u τ), hs (r τ) (j τ)] at hd
  have he : inner ℝ (r τ) (H (j τ)) + inner ℝ (r τ) (P (j τ)) +
      inner ℝ (i τ) (H (u τ)) +
      (-(inner ℝ (i τ) (H (u τ)) + inner ℝ (i τ) (P (u τ))) +
        -inner ℝ (r τ) (H (j τ))) =
      inner ℝ (r τ) (P (j τ)) - inner ℝ (i τ) (P (u τ)) := by ring
  rw [he] at hd
  exact hd

private theorem naturalError_inner_le (P : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (x y : TileHilbert Vertex) :
    |inner ℝ x (P y)| ≤ ‖P‖ * (‖x‖ * ‖y‖) := by
  calc
    _ ≤ ‖x‖ * ‖P y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖P‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left (P.le_opNorm y) (norm_nonneg _)
    _ = _ := by ring

theorem naturalTrajectoryOverlap_deriv_lower
    (H P : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hs : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y))
    (r i u j : ℝ → TileHilbert Vertex) (τ : ℝ)
    (h : naturalFullSolvesAt H r i τ) (k : naturalFullSolvesAt (H + P) u j τ)
    (hr : naturalTrajectoryWeight r i τ = 1)
    (hu : naturalTrajectoryWeight u j τ = 1) :
    -‖P‖ ≤ deriv (naturalTrajectoryOverlap r i u j) τ := by
  rw [(naturalTrajectoryOverlap_deriv H P hs r i u j τ h k).deriv]
  have h1 := naturalError_inner_le P (r τ) (j τ)
  have h2 := naturalError_inner_le P (i τ) (u τ)
  have hleft := le_trans (neg_le_abs (inner ℝ (r τ) (P (j τ)))) h1
  have hright := le_trans (le_abs_self (inner ℝ (i τ) (P (u τ)))) h2
  have hsum : ‖r τ‖ * ‖j τ‖ + ‖i τ‖ * ‖u τ‖ ≤ 1 := by
    unfold naturalTrajectoryWeight at hr hu
    nlinarith [sq_nonneg (‖r τ‖ - ‖j τ‖), sq_nonneg (‖i τ‖ - ‖u τ‖)]
  have hm := mul_le_mul_of_nonneg_left hsum (norm_nonneg P)
  rw [mul_add, mul_one] at hm
  linarith

/-- Squared full-state distance is bounded without an isolation
hypothesis. Both trajectories are assumed to solve the equations
for all real times; this does not assert their existence for arbitrary
initial data. -/
theorem naturalTrajectory_error_sq_le
    (H P : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hs : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y))
    (hp : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (r i u j : ℝ → TileHilbert Vertex)
    (h : ∀ s, naturalFullSolvesAt H r i s)
    (k : ∀ s, naturalFullSolvesAt (H + P) u j s)
    (hr : naturalTrajectoryWeight r i 0 = 1)
    (hR : u 0 = r 0) (hI : j 0 = i 0)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖u τ - r τ‖ ^ 2 + ‖j τ - i τ‖ ^ 2 ≤ 2 * ‖P‖ * τ := by
  have hsym : ∀ x y, inner ℝ ((H + P) x) y = inner ℝ x ((H + P) y) := by
    intro x y
    simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right, hs x y, hp x y]
  have hu : naturalTrajectoryWeight u j 0 = 1 := by
    unfold naturalTrajectoryWeight at hr ⊢
    rw [hR, hI]
    exact hr
  have hru (s : ℝ) (hs0 : 0 ≤ s) : naturalTrajectoryWeight r i s = 1 :=
    (naturalTrajectoryWeight_constant H hs r i h s hs0).trans hr
  have huu (s : ℝ) (hs0 : 0 ≤ s) : naturalTrajectoryWeight u j s = 1 :=
    (naturalTrajectoryWeight_constant (H + P) hsym u j k s hs0).trans hu
  have hd (s : ℝ) := naturalTrajectoryOverlap_deriv H P hs r i u j s (h s) (k s)
  have hf : Differentiable ℝ (naturalTrajectoryOverlap r i u j) :=
    fun s => (hd s).differentiableAt
  have hlo := (convex_Icc (0 : ℝ) τ).mul_sub_le_image_sub_of_le_deriv
    hf.continuous.continuousOn hf.differentiableOn (C := -‖P‖)
    (fun s hs' => by
      have hs'' : s ∈ Set.Icc (0 : ℝ) τ := interior_subset hs'
      exact naturalTrajectoryOverlap_deriv_lower H P hs r i u j s (h s) (k s)
        (hru s hs''.1) (huu s hs''.1))
    0 ⟨le_rfl,hτ⟩ τ ⟨hτ,le_rfl⟩ hτ
  have hinit : naturalTrajectoryOverlap r i u j 0 = 1 := by
    unfold naturalTrajectoryOverlap
    rw [hR, hI, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    exact hr
  rw [hinit, sub_zero] at hlo
  have hrτ := hru τ hτ
  have huτ := huu τ hτ
  unfold naturalTrajectoryWeight at hrτ huτ
  unfold naturalTrajectoryOverlap at hlo
  rw [norm_sub_sq_real, norm_sub_sq_real, real_inner_comm (u τ) (r τ),
    real_inner_comm (j τ) (i τ)]
  nlinarith

/-- Application to a prepared remote plane during free storage.
The reference trajectory is constructed, not assumed; only the
perturbed solution remains a hypothesis. -/
theorem naturalStorage_error_sq_le (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (w : ℂ × ℂ) (hw : ‖w.1‖ ^ 2 + ‖w.2‖ ^ 2 = 1)
    (P : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hp : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (u j : ℝ → TileHilbert Vertex)
    (hk : ∀ s, naturalFullSolvesAt (canonicalPlateauHamiltonian + P) u j s)
    (hR : u 0 = naturalStateReal v.val w) (hI : j 0 = naturalStateImag v.val w)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖u τ - naturalStateReal v.val (naturalStoragePair τ w)‖ ^ 2 +
      ‖j τ - naturalStateImag v.val (naturalStoragePair τ w)‖ ^ 2 ≤ 2 * ‖P‖ * τ := by
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
  exact naturalTrajectory_error_sq_le canonicalPlateauHamiltonian P hs hp r i u j
    h hk hnorm hri hij τ hτ

end
end SpectralGeometry.AmmannBeenker
