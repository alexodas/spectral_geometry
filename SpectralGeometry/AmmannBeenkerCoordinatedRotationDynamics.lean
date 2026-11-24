module

public import SpectralGeometry.AmmannBeenkerCoordinatedAxisDynamics

public section

/-!
# Exact rotation action of the two natural-domain pulses (L7c.2)

Identify the physical coefficient evolution, already constructed on
the infinite natural domain, with the X and Z rotation matrices.
The common scalar phase is retained. All strengths and times are real.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- Explicit action of a complex two-by-two matrix on a coefficient pair. -/
@[expose] def coordinatedApplyPair (M : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : ℂ) : ℂ × ℂ :=
  (M 0 0 * a + M 0 1 * b, M 1 0 * a + M 1 1 * b)

theorem coordinatedApplyPair_mul (M N : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : ℂ) :
    coordinatedApplyPair M (coordinatedApplyPair N a b).1
      (coordinatedApplyPair N a b).2 = coordinatedApplyPair (M * N) a b := by
  apply Prod.ext <;>
    simp [coordinatedApplyPair, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem coordinatedApplyPair_smul (M : Matrix (Fin 2) (Fin 2) ℂ)
    (z a b : ℂ) :
    coordinatedApplyPair (z • M) a b =
      (z * (coordinatedApplyPair M a b).1, z * (coordinatedApplyPair M a b).2) := by
  apply Prod.ext <;> simp [coordinatedApplyPair] <;> ring

theorem coordinatedApplyPair_scale_input (M : Matrix (Fin 2) (Fin 2) ℂ)
    (z a b : ℂ) :
    coordinatedApplyPair M (z * a) (z * b) =
      (z * (coordinatedApplyPair M a b).1, z * (coordinatedApplyPair M a b).2) := by
  apply Prod.ext <;> simp [coordinatedApplyPair] <;> ring

theorem coordinatedApplyPair_dark (M : Matrix (Fin 2) (Fin 2) ℂ) :
    coordinatedApplyPair M 1 0 = (M 0 0, M 1 0) := by
  simp [coordinatedApplyPair]

/-- Euler's formula for the phase convention used in L7b. -/
theorem coordinatedPhase_trig (t : ℝ) :
    coordinatedPhase t = (Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ) := by
  have hr : (coordinatedPhase t).re = Real.cos t := by
    simpa [coordinatedEigenCoeff] using coordinatedEigenCoeff_re (-t) 1 1
  have hi : (coordinatedPhase t).im = Real.sin t := by
    simpa [coordinatedEigenCoeff] using coordinatedEigenCoeff_im (-t) 1 1
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      mul_zero, sub_zero, add_zero, hr]
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      mul_zero, zero_add, add_zero, hi]

/-- Embed complex dark/bright coefficients as real infinite-space vectors. -/
@[expose] def coordinatedEmbedReal (a b : ℂ) : TileHilbert Vertex :=
  a.re • crossingDark + b.re • crossingBright

@[expose] def coordinatedEmbedImag (a b : ℂ) : TileHilbert Vertex :=
  a.im • crossingDark + b.im • crossingBright

/-- The actual detuning evolution in dark/bright coordinates, obtained
from the two compact eigenmode phases, before removing any common phase. -/
@[expose] def coordinatedXAxisMatrix (δ τ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let p := coordinatedPhase (-(crossingEnergy + δ) * τ)
  let q := coordinatedPhase (-crossingEnergy * τ)
  !![(p + q) / 2, (p - q) / 2; (p - q) / 2, (p + q) / 2]

/-- The actual coordinated-edge evolution in dark/bright coordinates. -/
@[expose] def coordinatedZAxisMatrix (η τ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![coordinatedPhase (-crossingEnergy * τ), 0;
     0, coordinatedPhase (-(crossingEnergy + 2 * η) * τ)]

private theorem coordinatedPhase_sum_diff (c t : ℝ) :
    (coordinatedPhase (c + t) + coordinatedPhase (c - t)) / 2 =
      coordinatedPhase c * (Real.cos t : ℂ) ∧
    (coordinatedPhase (c + t) - coordinatedPhase (c - t)) / 2 =
      coordinatedPhase c * (Complex.I * (Real.sin t : ℂ)) := by
  rw [coordinatedPhase_add, sub_eq_add_neg, coordinatedPhase_add,
    coordinatedPhase_trig t, coordinatedPhase_trig (-t)]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  constructor <;> ring

/-- Detuning is precisely an X rotation, times the common energy phase. -/
theorem coordinatedXAxisMatrix_rotation (δ τ : ℝ) :
    coordinatedXAxisMatrix δ τ =
      coordinatedPhase (-(crossingEnergy + δ / 2) * τ) •
        coordinatedRotationX (-δ * τ / 2) := by
  have hp : -(crossingEnergy + δ) * τ =
      -(crossingEnergy + δ / 2) * τ + (-δ * τ / 2) := by ring
  have hq : -crossingEnergy * τ =
      -(crossingEnergy + δ / 2) * τ - (-δ * τ / 2) := by ring
  have h := coordinatedPhase_sum_diff (-(crossingEnergy + δ / 2) * τ)
    (-δ * τ / 2)
  unfold coordinatedXAxisMatrix
  dsimp only
  rw [hp, hq]
  ext i j
  fin_cases i <;> fin_cases j
  · exact h.1
  · exact h.2
  · exact h.2
  · exact h.1

/-- Coordinated inter-ring changes are precisely a Z rotation, times
the common energy phase. -/
theorem coordinatedZAxisMatrix_rotation (η τ : ℝ) :
    coordinatedZAxisMatrix η τ =
      coordinatedPhase (-(crossingEnergy + η) * τ) •
        coordinatedRotationZ (η * τ) := by
  have hp : -crossingEnergy * τ =
      -(crossingEnergy + η) * τ + η * τ := by ring
  have hq : -(crossingEnergy + 2 * η) * τ =
      -(crossingEnergy + η) * τ + -(η * τ) := by ring
  unfold coordinatedZAxisMatrix
  rw [hp, hq, coordinatedPhase_add, coordinatedPhase_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coordinatedRotationZ]

/-- The coefficient pair after a detuning pulse, using the original
unnormalized compact modes with coefficients (a+b)/4 and (a-b)/4. -/
theorem coordinatedXAxisMatrix_coefficients (δ τ : ℝ) (a b : ℂ) :
    coordinatedApplyPair (coordinatedXAxisMatrix δ τ) a b =
      (2 * (coordinatedEigenCoeff (crossingEnergy + δ) ((a + b) / 4) τ +
            coordinatedEigenCoeff crossingEnergy ((a - b) / 4) τ),
       2 * (coordinatedEigenCoeff (crossingEnergy + δ) ((a + b) / 4) τ -
            coordinatedEigenCoeff crossingEnergy ((a - b) / 4) τ)) := by
  apply Prod.ext <;>
    simp [coordinatedApplyPair, coordinatedXAxisMatrix, coordinatedEigenCoeff] <;> ring

theorem coordinatedZAxisMatrix_coefficients (η τ : ℝ) (a b : ℂ) :
    coordinatedApplyPair (coordinatedZAxisMatrix η τ) a b =
      (coordinatedEigenCoeff crossingEnergy a τ,
       coordinatedEigenCoeff (crossingEnergy + 2 * η) b τ) := by
  apply Prod.ext <;>
    simp [coordinatedApplyPair, coordinatedZAxisMatrix, coordinatedEigenCoeff]

private theorem coordinatedEmbedReal_compact (a b : ℂ) :
    coordinatedEmbedReal (2 * (a + b)) (2 * (a - b)) =
      a.re • compactA + b.re • compactB := by
  have h2r : (2 : ℂ).re = 2 := by norm_num
  have h2i : (2 : ℂ).im = 0 := by norm_num
  unfold coordinatedEmbedReal crossingDark crossingBright
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, h2r, h2i, zero_mul, sub_zero]
  module

private theorem coordinatedEmbedImag_compact (a b : ℂ) :
    coordinatedEmbedImag (2 * (a + b)) (2 * (a - b)) =
      a.im • compactA + b.im • compactB := by
  have h2r : (2 : ℂ).re = 2 := by norm_num
  have h2i : (2 : ℂ).im = 0 := by norm_num
  unfold coordinatedEmbedImag crossingDark crossingBright
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, h2r, h2i, zero_mul, add_zero]
  module

/-- The physical detuning trajectory on the full infinite graph is the
embedding of the exact phase-weighted rotation coefficient pair. -/
theorem coordinatedXAxis_trajectory_matrix (δ τ : ℝ) (a b : ℂ) :
    let w := coordinatedApplyPair (coordinatedXAxisMatrix δ τ) a b
    coordinatedPairReal domainCompactA domainCompactB
      (crossingEnergy + δ) crossingEnergy ((a + b) / 4) ((a - b) / 4) τ =
      coordinatedEmbedReal w.1 w.2 ∧
    coordinatedPairImag domainCompactA domainCompactB
      (crossingEnergy + δ) crossingEnergy ((a + b) / 4) ((a - b) / 4) τ =
      coordinatedEmbedImag w.1 w.2 := by
  dsimp only
  rw [coordinatedXAxisMatrix_coefficients]
  constructor
  · rw [coordinatedEmbedReal_compact]
    rfl
  · rw [coordinatedEmbedImag_compact]
    rfl

theorem coordinatedZAxis_trajectory_matrix (η τ : ℝ) (a b : ℂ) :
    let w := coordinatedApplyPair (coordinatedZAxisMatrix η τ) a b
    coordinatedPairReal domainCrossingDark domainCrossingBright
      crossingEnergy (crossingEnergy + 2 * η) a b τ =
      coordinatedEmbedReal w.1 w.2 ∧
    coordinatedPairImag domainCrossingDark domainCrossingBright
      crossingEnergy (crossingEnergy + 2 * η) a b τ =
      coordinatedEmbedImag w.1 w.2 := by
  dsimp only
  rw [coordinatedZAxisMatrix_coefficients]
  exact ⟨rfl, rfl⟩

/-- The natural-domain trajectories from L7c.1 realize the X rotation
with its exact scalar phase, for arbitrary complex initial coefficients. -/
theorem coordinatedXAxis_trajectory_rotation (δ τ : ℝ) (a b : ℂ) :
    let w := coordinatedApplyPair
      (coordinatedPhase (-(crossingEnergy + δ / 2) * τ) •
        coordinatedRotationX (-δ * τ / 2)) a b
    coordinatedPairReal domainCompactA domainCompactB
      (crossingEnergy + δ) crossingEnergy ((a + b) / 4) ((a - b) / 4) τ =
      coordinatedEmbedReal w.1 w.2 ∧
    coordinatedPairImag domainCompactA domainCompactB
      (crossingEnergy + δ) crossingEnergy ((a + b) / 4) ((a - b) / 4) τ =
      coordinatedEmbedImag w.1 w.2 := by
  simpa only [coordinatedXAxisMatrix_rotation] using
    coordinatedXAxis_trajectory_matrix δ τ a b

theorem coordinatedZAxis_trajectory_rotation (η τ : ℝ) (a b : ℂ) :
    let w := coordinatedApplyPair
      (coordinatedPhase (-(crossingEnergy + η) * τ) •
        coordinatedRotationZ (η * τ)) a b
    coordinatedPairReal domainCrossingDark domainCrossingBright
      crossingEnergy (crossingEnergy + 2 * η) a b τ =
      coordinatedEmbedReal w.1 w.2 ∧
    coordinatedPairImag domainCrossingDark domainCrossingBright
      crossingEnergy (crossingEnergy + 2 * η) a b τ =
      coordinatedEmbedImag w.1 w.2 := by
  simpa only [coordinatedZAxisMatrix_rotation] using
    coordinatedZAxis_trajectory_matrix η τ a b

/-- Both physical matrices are the identity at time zero. -/
theorem coordinatedXAxisMatrix_initial (δ : ℝ) :
    coordinatedXAxisMatrix δ 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinatedXAxisMatrix, coordinatedPhase, Matrix.one_apply]

theorem coordinatedZAxisMatrix_initial (η : ℝ) :
    coordinatedZAxisMatrix η 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinatedZAxisMatrix, coordinatedPhase, Matrix.one_apply]

end
end SpectralGeometry.AmmannBeenker
