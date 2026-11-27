module

public import SpectralGeometry.AmmannBeenkerPlateauMultiplicity
public import SpectralGeometry.BoundedSelfAdjointInverse

public section

/-!
# Full real spectral isolation of the bounded plateau crossing

The compact plane and its orthogonal complement reduce the bounded
Hamiltonian. A nonzero scalar shift on the plane and a shift smaller
than 1/122 on the complement give a boundedly invertible operator.
This proves exclusion from the full real Banach-algebra spectrum,
not merely absence of further eigenvectors. At the crossing, adding
the compact projection regularizes the zero eigenvalue.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

theorem plateauQubitProjection_symmetric (x y : TileHilbert Vertex) :
    inner ℝ (plateauQubitProjection x) y = inner ℝ x (plateauQubitProjection y) := by
  rw [plateauQubitProjection_apply, plateauQubitProjection_apply]
  simp only [crossingQubitPart, crossingCoeffA, crossingCoeffB,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm x compactA, real_inner_comm x compactB]
  ring

theorem plateauLeakageCLM_symmetric (x y : TileHilbert Vertex) :
    inner ℝ (plateauLeakageCLM x) y = inner ℝ x (plateauLeakageCLM y) := by
  change inner ℝ (x - plateauQubitProjection x) y =
    inner ℝ x (y - plateauQubitProjection y)
  rw [inner_sub_left, inner_sub_right, plateauQubitProjection_symmetric]

theorem plateauQubitProjection_norm_apply_le (x : TileHilbert Vertex) :
    ‖plateauQubitProjection x‖ ≤ ‖x‖ := by
  rw [plateauQubitProjection_apply]
  have h := crossingQubitPart_leakage_norm_sq x
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith only [h, sq_nonneg ‖crossingLeakage x‖]

theorem plateauLeakageCLM_norm_apply_le (x : TileHilbert Vertex) :
    ‖plateauLeakageCLM x‖ ≤ ‖x‖ := by
  rw [plateauLeakageCLM_apply]
  have h := crossingQubitPart_leakage_norm_sq x
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith only [h, sq_nonneg ‖crossingQubitPart x‖]

theorem plateauQubitProjection_idempotent_apply (x : TileHilbert Vertex) :
    plateauQubitProjection (plateauQubitProjection x) = plateauQubitProjection x := by
  rw [plateauQubitProjection_apply, plateauQubitProjection_apply]
  simp only [crossingQubitPart, crossingCoeffA_pair, crossingCoeffB_pair]

theorem plateauQubitProjection_leakage_zero (x : TileHilbert Vertex) :
    plateauQubitProjection (plateauLeakageCLM x) = 0 := by
  change plateauQubitProjection (x - plateauQubitProjection x) = 0
  rw [map_sub, plateauQubitProjection_idempotent_apply, sub_self]

theorem plateauLeakageCLM_qubit_zero (x : TileHilbert Vertex) :
    plateauLeakageCLM (plateauQubitProjection x) = 0 := by
  change plateauQubitProjection x -
    plateauQubitProjection (plateauQubitProjection x) = 0
  rw [plateauQubitProjection_idempotent_apply, sub_self]

theorem plateauLeakageCLM_idempotent_apply (x : TileHilbert Vertex) :
    plateauLeakageCLM (plateauLeakageCLM x) = plateauLeakageCLM x := by
  change plateauLeakageCLM x - plateauQubitProjection (plateauLeakageCLM x) =
    plateauLeakageCLM x
  rw [plateauQubitProjection_leakage_zero, sub_zero]

theorem plateauResidual_projection_zero (C : ℝ) (hC : 1 ≤ C)
    (hfive : 5 ≤ C) (x : TileHilbert Vertex) :
    plateauQubitProjection (plateauResidual C hC x) = 0 := by
  have ha : plateauResidual C hC compactA = 0 := by
    change plateauHamiltonian C hC compactA - crossingEnergy • compactA = 0
    rw [plateauHamiltonian_compactA C hC hfive, sub_self]
  have hb : plateauResidual C hC compactB = 0 := by
    change plateauHamiltonian C hC compactB - crossingEnergy • compactB = 0
    rw [plateauHamiltonian_compactB C hC hfive, sub_self]
  have hia : inner ℝ compactA (plateauResidual C hC x) = 0 := by
    rw [← plateauResidual_symmetric C hC compactA x, ha, inner_zero_left]
  have hib : inner ℝ compactB (plateauResidual C hC x) = 0 := by
    rw [← plateauResidual_symmetric C hC compactB x, hb, inner_zero_left]
  rw [plateauQubitProjection_apply]
  simp [crossingQubitPart, crossingCoeffA, crossingCoeffB, hia, hib]

theorem plateauResidual_leakage_projection_eq (C : ℝ) (hC : 1 ≤ C)
    (hfive : 5 ≤ C) (x : TileHilbert Vertex) :
    plateauLeakageCLM (plateauResidual C hC x) = plateauResidual C hC x := by
  change plateauResidual C hC x - plateauQubitProjection (plateauResidual C hC x) =
    plateauResidual C hC x
  rw [plateauResidual_projection_zero C hC hfive, sub_zero]

/-- Independent shifts of the compact plane and its orthogonal
complement. The compact-plane shift can regularize the crossing. -/
@[expose] def plateauBlockShift (C : ℝ) (hC : 1 ≤ C) (a b : ℝ) :
    TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  plateauResidual C hC + a • plateauQubitProjection + b • plateauLeakageCLM

theorem plateauBlockShift_isSelfAdjoint (C : ℝ) (hC : 1 ≤ C) (a b : ℝ) :
    IsSelfAdjoint (plateauBlockShift C hC a b) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℝ (plateauResidual C hC x + a • plateauQubitProjection x +
      b • plateauLeakageCLM x) y =
    inner ℝ x (plateauResidual C hC y + a • plateauQubitProjection y +
      b • plateauLeakageCLM y)
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, plateauResidual_symmetric C hC x y,
    plateauQubitProjection_symmetric x y, plateauLeakageCLM_symmetric x y]

theorem plateauBlockShift_projection_apply (C : ℝ) (hC : 1 ≤ C)
    (hfive : 5 ≤ C) (a b : ℝ) (x : TileHilbert Vertex) :
    plateauQubitProjection (plateauBlockShift C hC a b x) =
      a • plateauQubitProjection x := by
  change plateauQubitProjection (plateauResidual C hC x +
      a • plateauQubitProjection x + b • plateauLeakageCLM x) = _
  simp only [map_add, map_smul, plateauResidual_projection_zero C hC hfive,
    plateauQubitProjection_idempotent_apply, plateauQubitProjection_leakage_zero,
    smul_zero, zero_add, add_zero]

theorem plateauBlockShift_leakage_apply (C : ℝ) (hC : 1 ≤ C)
    (hfive : 5 ≤ C) (a b : ℝ) (x : TileHilbert Vertex) :
    plateauLeakageCLM (plateauBlockShift C hC a b x) =
      plateauResidual C hC x + b • plateauLeakageCLM x := by
  change plateauLeakageCLM (plateauResidual C hC x +
      a • plateauQubitProjection x + b • plateauLeakageCLM x) = _
  simp only [map_add, map_smul, plateauResidual_leakage_projection_eq C hC hfive,
    plateauLeakageCLM_qubit_zero, plateauLeakageCLM_idempotent_apply, smul_zero,
    add_zero]

/-- Both block components are bounded by the norm of the shifted
operator. This is an estimate on all states, not just eigenvectors. -/
theorem plateauBlockShift_component_bounds (C : ℝ) (hC : 1 ≤ C)
    (hheight : canonicalPlateauHeight ≤ C) (a b : ℝ) (x : TileHilbert Vertex) :
    |a| * ‖plateauQubitProjection x‖ ≤ ‖plateauBlockShift C hC a b x‖ ∧
    (1 / 122 - |b|) * ‖plateauLeakageCLM x‖ ≤ ‖plateauBlockShift C hC a b x‖ := by
  have hfive := canonicalPlateauHeight_ge_five.trans hheight
  constructor
  · have h := plateauQubitProjection_norm_apply_le (plateauBlockShift C hC a b x)
    rw [plateauBlockShift_projection_apply C hC hfive a b x, norm_smul,
      Real.norm_eq_abs] at h
    exact h
  · have h := plateauLeakageCLM_norm_apply_le (plateauBlockShift C hC a b x)
    rw [plateauBlockShift_leakage_apply C hC hfive a b x] at h
    have hr := plateauResidual_leakage_bound C hC hheight x
    rw [← plateauLeakageCLM_apply] at hr
    have ht : ‖plateauResidual C hC x‖ ≤
        ‖plateauResidual C hC x + b • plateauLeakageCLM x‖ +
          |b| * ‖plateauLeakageCLM x‖ := by
      calc
        ‖plateauResidual C hC x‖ =
            ‖(plateauResidual C hC x + b • plateauLeakageCLM x) -
              b • plateauLeakageCLM x‖ := by rw [add_sub_cancel_right]
        _ ≤ _ := by
          simpa only [norm_smul, Real.norm_eq_abs] using
            (norm_sub_le (plateauResidual C hC x + b • plateauLeakageCLM x)
              (b • plateauLeakageCLM x))
    linarith only [h, hr, ht]

/-- Full bounded invertibility for a nonzero plane shift and any
complement shift strictly smaller than the certified residual radius. -/
theorem plateauBlockShift_isUnit (C : ℝ) (hC : 1 ≤ C)
    (hheight : canonicalPlateauHeight ≤ C) (a b : ℝ)
    (ha : a ≠ 0) (hb : |b| < (1 / 122 : ℝ)) :
    IsUnit (plateauBlockShift C hC a b) := by
  let m : ℝ := min |a| (1 / 122 - |b|)
  have hm : 0 < m := lt_min (abs_pos.mpr ha) (sub_pos.mpr hb)
  apply boundedSelfAdjoint_isUnit_of_norm_lower _
    (plateauBlockShift_isSelfAdjoint C hC a b) (2 / m) (by positivity)
  intro x
  obtain ⟨hp, hq⟩ := plateauBlockShift_component_bounds C hC hheight a b x
  have hp' : m * ‖plateauQubitProjection x‖ ≤ ‖plateauBlockShift C hC a b x‖ :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)).trans hp
  have hq' : m * ‖plateauLeakageCLM x‖ ≤ ‖plateauBlockShift C hC a b x‖ :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)).trans hq
  have hsum : plateauQubitProjection x + plateauLeakageCLM x = x := by
    rw [plateauQubitProjection_apply, plateauLeakageCLM_apply, crossingQubitPart_add_leakage]
  have hx : ‖x‖ ≤ ‖plateauQubitProjection x‖ + ‖plateauLeakageCLM x‖ := by
    calc
      ‖x‖ = ‖plateauQubitProjection x + plateauLeakageCLM x‖ := by rw [hsum]
      _ ≤ _ := norm_add_le _ _
  have hx' := mul_le_mul_of_nonneg_left hx hm.le
  have hbound : ‖x‖ * m ≤ 2 * ‖plateauBlockShift C hC a b x‖ := by
    linarith only [hp', hq', hx']
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hm).mpr hbound

/-- The regularized residual has a bounded inverse even at the
crossing. On the orthogonal complement it agrees with the residual. -/
theorem plateauResidual_regularized_isUnit (C : ℝ) (hC : 1 ≤ C)
    (hheight : canonicalPlateauHeight ≤ C) :
    IsUnit (plateauResidual C hC + plateauQubitProjection) := by
  have h := plateauBlockShift_isUnit C hC hheight 1 0 (by norm_num)
    (by norm_num)
  have he : plateauBlockShift C hC 1 0 =
      plateauResidual C hC + plateauQubitProjection := by
    apply ContinuousLinearMap.ext
    intro x
    change plateauResidual C hC x + (1 : ℝ) • plateauQubitProjection x +
      (0 : ℝ) • plateauLeakageCLM x =
      plateauResidual C hC x + plateauQubitProjection x
    rw [one_smul, zero_smul, add_zero]
  rw [he] at h
  exact h

/-- Every different real energy in the open radius 1/122 lies in
the bounded resolvent set of the full plateau Hamiltonian. -/
theorem plateauHamiltonian_notMem_spectrum_of_near (C : ℝ) (hC : 1 ≤ C)
    (hheight : canonicalPlateauHeight ≤ C) (energy : ℝ)
    (hne : energy ≠ crossingEnergy) (hnear : |energy - crossingEnergy| < (1 / 122 : ℝ)) :
    energy ∉ spectrum ℝ (plateauHamiltonian C hC) := by
  let d := crossingEnergy - energy
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hdb : |d| < (1 / 122 : ℝ) := by
    dsimp [d]
    rwa [abs_sub_comm]
  have hu := plateauBlockShift_isUnit C hC hheight d d hd hdb
  have he : plateauBlockShift C hC d d =
      plateauHamiltonian C hC - energy • (1 : TileHilbert Vertex →L[ℝ] TileHilbert Vertex) := by
    apply ContinuousLinearMap.ext
    intro x
    change plateauHamiltonian C hC x - crossingEnergy • x +
      d • plateauQubitProjection x + d • (x - plateauQubitProjection x) =
      plateauHamiltonian C hC x - energy • x
    dsimp [d]
    module
  rw [he] at hu
  apply spectrum.notMem_iff.mpr
  rw [Algebra.algebraMap_eq_smul_one, ← neg_sub]
  exact hu.neg

/-- Explicit full-real-spectrum separation from every other energy. -/
theorem plateauHamiltonian_realSpectrum_gap (C : ℝ) (hC : 1 ≤ C)
    (hheight : canonicalPlateauHeight ≤ C) (energy : ℝ)
    (hspec : energy ∈ spectrum ℝ (plateauHamiltonian C hC))
    (hne : energy ≠ crossingEnergy) :
    (1 / 122 : ℝ) ≤ |energy - crossingEnergy| := by
  by_contra hn
  exact plateauHamiltonian_notMem_spectrum_of_near C hC hheight energy hne
    (lt_of_not_ge hn) hspec

end
end SpectralGeometry.AmmannBeenker
