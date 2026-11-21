module

public import SpectralGeometry.AmmannBeenkerQubitLeakage

public section

/-!
# Uniform leakage bound from a nearby invariant subspace

This is an *abstract* lemma for a real normed state space. It does
not postulate a quantum propagator for the infinite Ammann–Beenker
Hamiltonian and does not use a finite-dimensional truncation.

Suppose P projects onto a desired subspace, S onto a nearby subspace,
and U is a linear norm-preserving evolution that commutes with S.
If P and S differ by at most δ in norm on every state, then starting
in the desired subspace P, the final state lies within 2δ of it,
regardless of how long U has been applied.

The future graph-specific obligations are (1) define the complex
self-adjoint dynamics, (2) construct the perturbed spectral projection
S from the certified spectral gap, and (3) quantitatively prove that
S stays close to P as the edge perturbation tends to zero.

The lemma below is intentionally conditional on those hypotheses:
it is NOT an existence or approximate-controllability theorem.
-/

namespace SpectralGeometry

/-- A nearby invariant subspace controls leakage uniformly in
evolution duration. Neither P nor S needs to be realized by a
particular Hamiltonian to prove the estimate; in applications they
are orthogonal spectral projections.

The four nontrivial hypotheses are explicit: P fixes the input,
U is norm preserving, U commutes with S, and the projections are
δ-close on every vector. -/
theorem leakage_norm_le_of_nearby_invariant_subspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P S U : E →L[ℝ] E) (x : E) (δ : ℝ)
    (hx : P x = x)
    (hU : ∀ y : E, ‖U y‖ = ‖y‖)
    (hcomm : ∀ y : E, S (U y) = U (S y))
    (hclose : ∀ y : E, ‖P y - S y‖ ≤ δ * ‖y‖) :
    ‖U x - P (U x)‖ ≤ 2 * δ * ‖x‖ := by
  have hsplit : U x - S (U x) = U (x - S x) := by
    rw [hcomm x, map_sub]
  have hfirst : ‖U x - S (U x)‖ ≤ δ * ‖x‖ := by
    rw [hsplit, hU]
    calc
      ‖x - S x‖ = ‖P x - S x‖ := by rw [hx]
      _ ≤ δ * ‖x‖ := hclose x
  have hsecond : ‖S (U x) - P (U x)‖ ≤ δ * ‖x‖ := by
    calc
      ‖S (U x) - P (U x)‖ =
          ‖P (U x) - S (U x)‖ := norm_sub_rev _ _
      _ ≤ δ * ‖U x‖ := hclose (U x)
      _ = δ * ‖x‖ := by rw [hU]
  calc
    ‖U x - P (U x)‖ =
        ‖(U x - S (U x)) + (S (U x) - P (U x))‖ := by
          congr 1
          abel
    _ ≤ ‖U x - S (U x)‖ + ‖S (U x) - P (U x)‖ :=
      norm_add_le _ _
    _ ≤ δ * ‖x‖ + δ * ‖x‖ := add_le_add hfirst hsecond
    _ = 2 * δ * ‖x‖ := by ring

/-- A normalized initial state has final off-plane squared norm
at most 4δ² under the same hypotheses. This is a squared-norm
statement; identifying it with a quantum measurement probability
requires the future complex Hilbert-space model. -/
theorem leakage_sq_le_of_nearby_invariant_subspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P S U : E →L[ℝ] E) (x : E) (δ : ℝ)
    (hx : P x = x) (hunit : ‖x‖ = 1) (hδ : 0 ≤ δ)
    (hU : ∀ y : E, ‖U y‖ = ‖y‖)
    (hcomm : ∀ y : E, S (U y) = U (S y))
    (hclose : ∀ y : E, ‖P y - S y‖ ≤ δ * ‖y‖) :
    ‖U x - P (U x)‖ ^ 2 ≤ 4 * δ ^ 2 := by
  have hbound :=
    leakage_norm_le_of_nearby_invariant_subspace
      P S U x δ hx hU hcomm hclose
  rw [hunit, mul_one] at hbound
  have hnonneg : 0 ≤ 2 * δ := mul_nonneg (by norm_num) hδ
  have hprod : 0 ≤
      (2 * δ - ‖U x - P (U x)‖) *
        (2 * δ + ‖U x - P (U x)‖) :=
    mul_nonneg (sub_nonneg.mpr hbound)
      (add_nonneg hnonneg (norm_nonneg _))
  nlinarith

end SpectralGeometry
