module

public import Mathlib
public import SpectralGeometry.AmmannBeenkerCoordinatedInvariantPlane

public section

/-!
# Two-control generator algebra (L7b)

The exact restriction has been computed in the original natural domain.
Here we certify the finite-dimensional complex generator directions.
This is not a construction of the full complex propagator.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- The exact real matrix in the ordered normalized basis (dark, bright). -/
@[expose] def coordinatedEffectiveMatrix (δ η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![crossingEnergy + δ / 2, δ / 2;
     δ / 2, crossingEnergy + δ / 2 + 2 * η]

theorem coordinatedEffectiveMatrix_pauli (δ η : ℝ) :
    coordinatedEffectiveMatrix δ η =
      (crossingEnergy + δ / 2 + η) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (δ / 2) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) -
        η • (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinatedEffectiveMatrix, Matrix.one_apply] <;> ring

/-- Scaled skew-Hermitian control directions (the sign of the
Schrödinger generator can be absorbed into the real coefficients). -/
@[expose] def coordinatedLieX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, Complex.I; Complex.I, 0]

@[expose] def coordinatedLieZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I, 0; 0, -Complex.I]

@[expose] def coordinatedLieY : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; -1, 0]

theorem coordinatedLie_XZ :
    coordinatedLieX * coordinatedLieZ - coordinatedLieZ * coordinatedLieX =
      (2 : ℂ) • coordinatedLieY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinatedLieX, coordinatedLieY, coordinatedLieZ, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.I_mul_I] <;> ring

theorem coordinatedLie_ZY :
    coordinatedLieZ * coordinatedLieY - coordinatedLieY * coordinatedLieZ =
      (2 : ℂ) • coordinatedLieX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinatedLieX, coordinatedLieY, coordinatedLieZ, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

theorem coordinatedLie_YX :
    coordinatedLieY * coordinatedLieX - coordinatedLieX * coordinatedLieY =
      (2 : ℂ) • coordinatedLieZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinatedLieX, coordinatedLieY, coordinatedLieZ, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

theorem coordinatedLie_noncommuting :
    coordinatedLieX * coordinatedLieZ ≠ coordinatedLieZ * coordinatedLieX := by
  intro h
  have hz := coordinatedLie_XZ
  rw [h, sub_self] at hz
  have h01 := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℂ => m 0 1) hz
  norm_num [coordinatedLieY] at h01

/-- The three real coordinates describe the standard traceless
skew-Hermitian 2-by-2 matrices. This is an explicit parametrization,
not a Lie-group reachability theorem. -/
theorem coordinatedLie_coordinates (x y z : ℝ) :
    (x : ℂ) • coordinatedLieX + (y : ℂ) • coordinatedLieY +
      (z : ℂ) • coordinatedLieZ =
      !![(z : ℂ) * Complex.I, (y : ℂ) + (x : ℂ) * Complex.I;
         -(y : ℂ) + (x : ℂ) * Complex.I, -(z : ℂ) * Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinatedLieX, coordinatedLieY, coordinatedLieZ] <;> ring

end
end SpectralGeometry.AmmannBeenker
