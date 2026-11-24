module

public import SpectralGeometry.AmmannBeenkerCoordinatedLieAlgebra

public section

/-!
# Real Lie generation for the coordinated two-mode controls (L7b)

The smallest real linear space closed under matrix commutators and
containing the two control directions is the traceless skew-Hermitian
2-by-2 matrix space. This characterization uses the concrete matrix
commutator and does not assume a finite-dimensional dynamical theorem.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- The concrete real vector space su(2). -/
@[expose] def coordinatedSu2 : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ) where
  carrier := { A | A.conjTranspose = -A ∧ A.trace = 0 }
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    change A.conjTranspose = -A ∧ A.trace = 0 at hA
    change B.conjTranspose = -B ∧ B.trace = 0 at hB
    change (A + B).conjTranspose = -(A + B) ∧ (A + B).trace = 0
    simp [Matrix.conjTranspose_add, Matrix.trace_add, hA.1, hA.2, hB.1, hB.2] <;> abel
  smul_mem' := by
    intro r A hA
    change A.conjTranspose = -A ∧ A.trace = 0 at hA
    change (r • A).conjTranspose = -(r • A) ∧ (r • A).trace = 0
    simp [Matrix.conjTranspose_smul, Matrix.trace_smul, hA.1, hA.2, smul_neg]

theorem coordinatedSu2_commutator (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ coordinatedSu2) (hB : B ∈ coordinatedSu2) :
    A * B - B * A ∈ coordinatedSu2 := by
  change A.conjTranspose = -A ∧ A.trace = 0 at hA
  change B.conjTranspose = -B ∧ B.trace = 0 at hB
  change (A * B - B * A).conjTranspose = -(A * B - B * A) ∧
    (A * B - B * A).trace = 0
  constructor
  · simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hA.1, hB.1,
      neg_mul_neg]
    abel
  · rw [Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self]

theorem coordinatedSu2_X : coordinatedLieX ∈ coordinatedSu2 := by
  change coordinatedLieX.conjTranspose = -coordinatedLieX ∧ coordinatedLieX.trace = 0
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinatedLieX, Matrix.conjTranspose_apply, Complex.star_def]
  · norm_num [coordinatedLieX, Matrix.trace_fin_two]

theorem coordinatedSu2_Z : coordinatedLieZ ∈ coordinatedSu2 := by
  change coordinatedLieZ.conjTranspose = -coordinatedLieZ ∧ coordinatedLieZ.trace = 0
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinatedLieZ, Matrix.conjTranspose_apply, Complex.star_def]
  · norm_num [coordinatedLieZ, Matrix.trace_fin_two]

/-- Every traceless skew-Hermitian matrix has the three real Pauli coordinates. -/
theorem coordinatedSu2_coordinates (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ coordinatedSu2) :
    A = (A 0 1).im • coordinatedLieX +
      (A 0 1).re • coordinatedLieY + (A 0 0).im • coordinatedLieZ := by
  change A.conjTranspose = -A ∧ A.trace = 0 at hA
  have h00 := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℂ => B 0 0) hA.1
  have h10 := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℂ => B 1 0) hA.1
  change star (A 0 0) = -A 0 0 at h00
  change star (A 0 1) = -A 1 0 at h10
  have hr := congrArg Complex.re h00
  have hr0 : (A 0 0).re = 0 := by
    simp [Complex.star_def] at hr
    linarith
  have h10' : A 1 0 = -star (A 0 1) := by
    rw [h10, neg_neg]
  have ht := hA.2
  rw [Matrix.trace_fin_two] at ht
  have h11 : A 1 1 = -A 0 0 := by
    calc
      A 1 1 = (A 0 0 + A 1 1) - A 0 0 := by ring
      _ = -A 0 0 := by rw [ht]; ring
  change A = ((A 0 1).im : ℂ) • coordinatedLieX +
      ((A 0 1).re : ℂ) • coordinatedLieY + ((A 0 0).im : ℂ) • coordinatedLieZ
  rw [coordinatedLie_coordinates]
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hr0]
  · apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  · change A 1 0 = -(↑(A 0 1).re : ℂ) + ↑(A 0 1).im * Complex.I
    rw [h10']
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  · change A 1 1 = -(↑(A 0 0).im : ℂ) * Complex.I
    rw [h11]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hr0]

/-- Minimality among all real linear subspaces closed under commutators. -/
theorem coordinatedSu2_le_of_controls
    (S : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ))
    (hX : coordinatedLieX ∈ S) (hZ : coordinatedLieZ ∈ S)
    (hbr : ∀ A B : Matrix (Fin 2) (Fin 2) ℂ, A ∈ S → B ∈ S → A * B - B * A ∈ S) :
    coordinatedSu2 ≤ S := by
  intro A hA
  have h := hbr coordinatedLieX coordinatedLieZ hX hZ
  rw [coordinatedLie_XZ] at h
  have hY : coordinatedLieY ∈ S := by
    have hh := S.smul_mem (1 / 2 : ℝ) h
    have he : (1 / 2 : ℝ) • ((2 : ℂ) • coordinatedLieY) = coordinatedLieY := by
      change ((1 / 2 : ℝ) : ℂ) • ((2 : ℂ) • coordinatedLieY) = coordinatedLieY
      rw [smul_smul]
      norm_num
    rw [he] at hh
    exact hh
  rw [coordinatedSu2_coordinates A hA]
  exact S.add_mem (S.add_mem (S.smul_mem _ hX) (S.smul_mem _ hY)) (S.smul_mem _ hZ)

/-- Exact generated-algebra characterization, without postulating Lie generation. -/
theorem coordinatedSu2_generated_iff (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A ∈ coordinatedSu2 ↔
      ∀ S : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ),
        coordinatedLieX ∈ S → coordinatedLieZ ∈ S →
        (∀ B C : Matrix (Fin 2) (Fin 2) ℂ, B ∈ S → C ∈ S → B * C - C * B ∈ S) →
        A ∈ S := by
  constructor
  · intro h S hX hZ hbr
    exact coordinatedSu2_le_of_controls S hX hZ hbr h
  · intro h
    exact h coordinatedSu2 coordinatedSu2_X coordinatedSu2_Z coordinatedSu2_commutator

end
end SpectralGeometry.AmmannBeenker
