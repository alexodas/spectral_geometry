module

public import SpectralGeometry.AmmannBeenkerNaturalQuadraticStability

public section

/-!
# Orthogonal leakage from a natural compact plane

The normalized dark/bright basis defines a real orthogonal projection
on each recurrent cell. Applying it to both real Hilbert components
gives the exact squared weight outside the selected plane, rather
than merely the distance to a particular ideal state. The finite-time
quadratic error estimate bounds this leakage without a collective gap.
The existence of the perturbed solution remains an explicit hypothesis.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

@[expose] def naturalRemotePart (t : Lattice) (x : TileHilbert Vertex) : TileHilbert Vertex :=
  inner ℝ (naturalRemoteDark t) x • naturalRemoteDark t +
    inner ℝ (naturalRemoteBright t) x • naturalRemoteBright t

@[expose] def naturalRemoteLeakage (t : Lattice) (x : TileHilbert Vertex) : TileHilbert Vertex :=
  x - naturalRemotePart t x

theorem naturalRemoteLeakage_orthogonal (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (x : TileHilbert Vertex) :
    inner ℝ (naturalRemoteDark t) (naturalRemoteLeakage t x) = 0 ∧
    inner ℝ (naturalRemoteBright t) (naturalRemoteLeakage t x) = 0 := by
  obtain ⟨hd, hf, hdf⟩ := naturalRemoteDarkBright_orthonormal t hrec
  have hfd : inner ℝ (naturalRemoteBright t) (naturalRemoteDark t) = 0 := by
    rw [real_inner_comm, hdf]
  have hdd : inner ℝ (naturalRemoteDark t) (naturalRemoteDark t) = 1 := by
    rw [real_inner_self_eq_norm_sq, hd]
  have hff : inner ℝ (naturalRemoteBright t) (naturalRemoteBright t) = 1 := by
    rw [real_inner_self_eq_norm_sq, hf]
  constructor <;>
    simp only [naturalRemoteLeakage, naturalRemotePart, inner_sub_right, inner_add_right,
      real_inner_smul_right, hdd, hff, hdf, hfd] <;> ring

theorem naturalRemotePart_fixes (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (a b : ℝ) :
    naturalRemotePart t (a • naturalRemoteDark t + b • naturalRemoteBright t) =
      a • naturalRemoteDark t + b • naturalRemoteBright t := by
  obtain ⟨hd, hf, hdf⟩ := naturalRemoteDarkBright_orthonormal t hrec
  have hfd : inner ℝ (naturalRemoteBright t) (naturalRemoteDark t) = 0 := by
    rw [real_inner_comm, hdf]
  have hdd : inner ℝ (naturalRemoteDark t) (naturalRemoteDark t) = 1 := by
    rw [real_inner_self_eq_norm_sq, hd]
  have hff : inner ℝ (naturalRemoteBright t) (naturalRemoteBright t) = 1 := by
    rw [real_inner_self_eq_norm_sq, hf]
  simp only [naturalRemotePart, inner_add_right, real_inner_smul_right,
    hdd, hff, hdf, hfd, mul_one, mul_zero, add_zero, zero_add]

theorem naturalRemotePart_idempotent (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (x : TileHilbert Vertex) :
    naturalRemotePart t (naturalRemotePart t x) = naturalRemotePart t x :=
  naturalRemotePart_fixes t hrec _ _

theorem naturalRemoteLeakage_nearest_sq (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (x : TileHilbert Vertex) (a b : ℝ) :
    ‖x - (a • naturalRemoteDark t + b • naturalRemoteBright t)‖ ^ 2 =
      ‖naturalRemoteLeakage t x‖ ^ 2 +
      ‖naturalRemotePart t x - (a • naturalRemoteDark t + b • naturalRemoteBright t)‖ ^ 2 := by
  obtain ⟨hd, hf⟩ := naturalRemoteLeakage_orthogonal t hrec x
  let y := a • naturalRemoteDark t + b • naturalRemoteBright t
  have he : x - y = naturalRemoteLeakage t x + (naturalRemotePart t x - y) := by
    unfold naturalRemoteLeakage
    abel
  have ho : inner ℝ (naturalRemotePart t x - y) (naturalRemoteLeakage t x) = 0 := by
    simp only [y, naturalRemotePart, inner_sub_left, inner_add_left, real_inner_smul_left,
      hd, hf, mul_zero, add_zero, sub_zero]
  have ho' : inner ℝ (naturalRemoteLeakage t x) (naturalRemotePart t x - y) = 0 := by
    rw [real_inner_comm, ho]
  change ‖x - y‖ ^ 2 = _
  rw [he]
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, ho, ho']
  ring

theorem naturalRemoteLeakage_norm_sq_le (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (x : TileHilbert Vertex) (a b : ℝ) :
    ‖naturalRemoteLeakage t x‖ ^ 2 ≤
      ‖x - (a • naturalRemoteDark t + b • naturalRemoteBright t)‖ ^ 2 := by
  rw [naturalRemoteLeakage_nearest_sq t hrec x a b]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem naturalRemotePart_budget (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (x : TileHilbert Vertex) :
    ‖x‖ ^ 2 = ‖naturalRemoteLeakage t x‖ ^ 2 + ‖naturalRemotePart t x‖ ^ 2 := by
  have h := naturalRemoteLeakage_nearest_sq t hrec x 0 0
  simpa only [zero_smul, add_zero, sub_zero] using h

/-- Squared off-plane weight of a complex state represented by its
two real Hilbert components. This counts errors inside the cell that
are outside the two selected directions as well as exterior support. -/
@[expose] def naturalRemoteLeakageWeight (t : Lattice) (x y : TileHilbert Vertex) : ℝ :=
  ‖naturalRemoteLeakage t x‖ ^ 2 + ‖naturalRemoteLeakage t y‖ ^ 2

theorem naturalRemoteLeakageWeight_le_error (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (x y : TileHilbert Vertex) (w : ℂ × ℂ) :
    naturalRemoteLeakageWeight t x y ≤
      ‖x - naturalStateReal t w‖ ^ 2 + ‖y - naturalStateImag t w‖ ^ 2 := by
  unfold naturalRemoteLeakageWeight naturalStateReal naturalStateImag
  exact add_le_add (naturalRemoteLeakage_norm_sq_le t hrec x _ _)
    (naturalRemoteLeakage_norm_sq_le t hrec y _ _)

theorem naturalRemoteLeakageWeight_budget (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (x y : TileHilbert Vertex) :
    naturalRemoteLeakageWeight t x y +
      (‖naturalRemotePart t x‖ ^ 2 + ‖naturalRemotePart t y‖ ^ 2) =
      ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  unfold naturalRemoteLeakageWeight
  linarith [naturalRemotePart_budget t hrec x, naturalRemotePart_budget t hrec y]

/-- Gap-independent leakage bound under a bounded symmetric error.
It is conditional on the actual perturbed solution, and applies
to the entire selected-plane complement, not just remote vertices. -/
theorem naturalStorage_leakage_quadratic_le (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (w : ℂ × ℂ) (hw : ‖w.1‖ ^ 2 + ‖w.2‖ ^ 2 = 1)
    (P : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hp : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (u j : ℝ → TileHilbert Vertex)
    (hk : ∀ s, naturalFullSolvesAt (canonicalPlateauHamiltonian + P) u j s)
    (hR : u 0 = naturalStateReal v.val w) (hI : j 0 = naturalStateImag v.val w)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    naturalRemoteLeakageWeight v.val (u τ) (j τ) ≤ ‖P‖ ^ 2 * τ ^ 2 := by
  exact le_trans (naturalRemoteLeakageWeight_le_error v.val hrec _ _ (naturalStoragePair τ w))
    (naturalStorage_error_quadratic_le v hr hrec w hw P hp u j hk hR hI τ hτ)

/-- The retained selected-plane weight for normalized perturbed
storage is at least one minus the same quadratic error bound. -/
theorem naturalStorage_retained_weight_ge (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (w : ℂ × ℂ) (hw : ‖w.1‖ ^ 2 + ‖w.2‖ ^ 2 = 1)
    (P : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hp : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (u j : ℝ → TileHilbert Vertex)
    (hk : ∀ s, naturalFullSolvesAt (canonicalPlateauHamiltonian + P) u j s)
    (hR : u 0 = naturalStateReal v.val w) (hI : j 0 = naturalStateImag v.val w)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    1 - ‖P‖ ^ 2 * τ ^ 2 ≤
      ‖naturalRemotePart v.val (u τ)‖ ^ 2 + ‖naturalRemotePart v.val (j τ)‖ ^ 2 := by
  have hs (x y : TileHilbert Vertex) :
      inner ℝ (canonicalPlateauHamiltonian x) y = inner ℝ x (canonicalPlateauHamiltonian y) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      canonicalPlateau_isolated_double_eigenvalue.1 x y
  have hsym : ∀ x y, inner ℝ ((canonicalPlateauHamiltonian + P) x) y =
      inner ℝ x ((canonicalPlateauHamiltonian + P) y) := by
    intro x y
    simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right, hs x y, hp x y]
  have h0 : naturalTrajectoryWeight u j 0 = 1 := by
    unfold naturalTrajectoryWeight
    rw [hR, hI]
    change naturalStateWeight v.val w = 1
    rw [naturalStateWeight_eq v.val hrec]
    exact hw
  have hnorm := (naturalTrajectoryWeight_constant _ hsym u j hk τ hτ).trans h0
  unfold naturalTrajectoryWeight at hnorm
  have hbudget := naturalRemoteLeakageWeight_budget v.val hrec (u τ) (j τ)
  have hle := naturalStorage_leakage_quadratic_le v hr hrec w hw P hp u j hk hR hI τ hτ
  linarith

end
end SpectralGeometry.AmmannBeenker
