module

public import SpectralGeometry.DomainEigenbasis

public section

/-!
# A reduced residual bound from a genuine spectral gap

For an unbounded but symmetric linear operator on its natural domain,
a complete *domain eigenbasis* diagonalizes its action. Parseval then
turns separation of every occupied eigenvalue from a chosen energy
into a norm lower bound for the operator residual.

The proof here does not assume a finite-dimensional system, nor a
bounded Hamiltonian. It only uses Mathlib's complete Hilbert basis,
the exact domain-eigenvector relations, and the symmetry identity.

This theorem is the generic spectral ingredient needed for moving
from the known Ammann–Beenker real spectral gap to small perturbed
eigenvectors. Its graph-specific instantiation must still identify
the complete crossing eigenbasis and prove that the leakage vector
has zero component at the isolated energy.
-/

namespace SpectralGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {ι : Type*} {d : Submodule ℝ H} {A : d →ₗ[ℝ] H}
variable {ev : ι → ℝ}

/-- For a complete eigenbasis, an energy gap g>0 gives an actual
operator residual estimate on every vector whose coordinates
at energy E vanish.

This is stronger than merely excluding other eigenvalues: it controls
the *whole infinite-dimensional norm* of the off-level vector.
The symmetry and complete eigenbasis are explicit hypotheses. -/
theorem DomainEigenbasis.norm_le_residual_of_gap
    (b : DomainEigenbasis d A ev)
    (hA : ∀ x y : d,
      inner ℝ (A x) (y : H) = inner ℝ (x : H) (A y))
    (E g : ℝ) (hg : 0 < g)
    (hgap : ∀ i, ev i ≠ E → g ≤ |ev i - E|)
    (x : d)
    (hsupport : ∀ i, ev i = E →
      inner ℝ (b.basis i) (x : H) = 0) :
    g * ‖(x : H)‖ ≤ ‖A x - E • (x : H)‖ := by
  let r : H := A x - E • (x : H)
  have hcoord (i : ι) :
      inner ℝ (b.basis i) r =
        (ev i - E) * inner ℝ (b.basis i) (x : H) := by
    dsimp [r]
    rw [inner_sub_right, real_inner_smul_right, b.inner_image hA x i]
    ring
  have hn : HasSum
      (fun i => (inner ℝ (b.basis i) (x : H)) ^ 2)
      (‖(x : H)‖ ^ 2) := by
    convert b.basis.hasSum_inner_mul_inner (x : H) (x : H) using 1
    · ext i
      rw [real_inner_comm (x : H) (b.basis i)]
      ring
    · exact (real_inner_self_eq_norm_sq _).symm
  have hr : HasSum
      (fun i => (inner ℝ (b.basis i) r) ^ 2)
      (‖r‖ ^ 2) := by
    convert b.basis.hasSum_inner_mul_inner r r using 1
    · ext i
      rw [real_inner_comm r (b.basis i)]
      ring
    · exact (real_inner_self_eq_norm_sq _).symm
  have hterm (i : ι) :
      g ^ 2 * (inner ℝ (b.basis i) (x : H)) ^ 2 ≤
        (inner ℝ (b.basis i) r) ^ 2 := by
    rw [hcoord]
    by_cases hi : ev i = E
    · rw [hsupport i hi]
      simp
    · have hsq : g ^ 2 ≤ (ev i - E) ^ 2 := by
        have h :=
          (sq_le_sq₀ hg.le (abs_nonneg (ev i - E))).mpr (hgap i hi)
        simpa only [sq_abs] using h
      calc
        g ^ 2 * (inner ℝ (b.basis i) (x : H)) ^ 2 ≤
            (ev i - E) ^ 2 *
              (inner ℝ (b.basis i) (x : H)) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
        _ = ((ev i - E) * inner ℝ (b.basis i) (x : H)) ^ 2 := by
          ring
  have hbound :
      g ^ 2 * ‖(x : H)‖ ^ 2 ≤ ‖r‖ ^ 2 :=
    hasSum_le hterm (hn.mul_left (g ^ 2)) hr
  have hsq :
      (g * ‖(x : H)‖) ^ 2 ≤ ‖r‖ ^ 2 := by
    calc
      (g * ‖(x : H)‖) ^ 2 = g ^ 2 * ‖(x : H)‖ ^ 2 := by
        ring
      _ ≤ ‖r‖ ^ 2 := hbound
  exact (sq_le_sq₀
    (mul_nonneg hg.le (norm_nonneg _)) (norm_nonneg _)).mp hsq

end
end SpectralGeometry
