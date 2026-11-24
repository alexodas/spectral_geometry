module

public import SpectralGeometry.AmmannBeenkerCoordinatedPairDynamics
public import SpectralGeometry.AmmannBeenkerPulseSelfAdjoint

public section

/-!
# Exact natural-domain dynamics for the two pure control axes (L7c)

Both controls admit a complete pair of exact compact eigenvectors on
the original plane. For X use compact A/B; for Z use dark/bright.
The constructed trajectories solve the coupled real/imaginary equations
of the full graph and preserve their norm and zero leakage at all times.
The real self-adjoint operator is also certified for both controls together.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

@[expose] def coordinatedCorrection (δ η : ℝ) : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  ringInteraction (crossingParameter + δ) + η • coordinatedRingControl

theorem coordinatedCorrection_symmetric (δ η : ℝ) :
    ∀ x y : TileHilbert Vertex,
      inner ℝ (coordinatedCorrection δ η x) y =
        inner ℝ x (coordinatedCorrection δ η y) := by
  have hring : ∀ x y : TileHilbert Vertex,
      inner ℝ ((ringInteraction (crossingParameter + δ)) x) y =
        inner ℝ x ((ringInteraction (crossingParameter + δ)) y) := by
    simpa only [ringInteraction] using
      (finiteSectorCorrection_symmetric interaction interaction_symmetric
        (neighbors origin) (crossingParameter + δ))
  have hedge : ∀ x y : TileHilbert Vertex,
      inner ℝ ((η • coordinatedRingControl) x) y =
        inner ℝ x ((η • coordinatedRingControl) y) := by
    intro x y
    simp only [smul_apply, real_inner_smul_left, real_inner_smul_right]
    rw [coordinatedRingControl_symmetric x y]
  exact boundedCorrection_add_symmetric _ _ hring hedge

@[expose] def coordinatedHamiltonianPMap (δ η : ℝ) :
    TileHilbert Vertex →ₗ.[ℝ] TileHilbert Vertex :=
  infiniteLocalShiftedPerturbedPMap 0 potential
    (fun i : Fin 0 => Fin.elim0 i) (fun _ => 0)
    (coordinatedCorrection δ η) 1 0

theorem coordinatedHamiltonianPMap_domain (δ η : ℝ) :
    (coordinatedHamiltonianPMap δ η).domain = infiniteOnsiteDomain potential := rfl

theorem coordinatedHamiltonianPMap_apply (δ η : ℝ)
    (x : infiniteOnsiteDomain potential) :
    coordinatedHamiltonianPMap δ η x =
      onsitePlusBounded potential (coordinatedCorrection δ η) x := by
  let σ : Fin 0 → Vertex ≃ Vertex := fun i => Fin.elim0 i
  let w : Fin 0 → ℝ := fun _ => 0
  let B := coordinatedCorrection δ η
  have hzero : infiniteLocalBoundedCorrection 0 σ w B 1 0 = B :=
    zeroMatching_correction B
  have hoperator : infiniteLocalShiftedPerturbedOperator 0 potential σ w B 1 0 =
      onsitePlusBounded potential B := by
    have h := (onsitePlusBounded_eq_local 0 potential σ w B 1 0).symm
    simpa only [hzero] using h
  change infiniteLocalShiftedPerturbedOperator 0 potential σ w B 1 0 x =
    onsitePlusBounded potential B x
  rw [hoperator]

theorem coordinatedHamiltonianPMap_isSelfAdjoint (δ η : ℝ) :
    IsSelfAdjoint (coordinatedHamiltonianPMap δ η) := by
  change IsSelfAdjoint (infiniteLocalShiftedPerturbedPMap 0 potential
    (fun i : Fin 0 => Fin.elim0 i) (fun _ => 0) (coordinatedCorrection δ η) 1 0)
  apply infiniteLocalShiftedPerturbedPMap_isSelfAdjoint
  · intro i t
    exact Fin.elim0 i
  · intro x y
    exact (coordinatedCorrection_symmetric δ η x y).symm

theorem coordinatedXAxis_eigenA (δ : ℝ) :
    onsitePlusBounded potential (coordinatedCorrection δ 0) domainCompactA =
      (crossingEnergy + δ) • compactA := by
  simpa [coordinatedCorrection] using ring_compactA_detuning δ

theorem coordinatedXAxis_eigenB (δ : ℝ) :
    onsitePlusBounded potential (coordinatedCorrection δ 0) domainCompactB =
      crossingEnergy • compactB := by
  simpa [coordinatedCorrection] using ring_compactB_detuning δ

theorem coordinatedZAxis_eigenDark (η : ℝ) :
    onsitePlusBounded potential (coordinatedCorrection 0 η) domainCrossingDark =
      crossingEnergy • crossingDark := by
  simpa [coordinatedCorrection] using
    (coordinatedControls_dark_bright_action 0 η 1 0)

theorem coordinatedZAxis_eigenBright (η : ℝ) :
    onsitePlusBounded potential (coordinatedCorrection 0 η) domainCrossingBright =
      (crossingEnergy + 2 * η) • crossingBright := by
  simpa [coordinatedCorrection] using
    (coordinatedControls_dark_bright_action 0 η 0 1)

theorem coordinatedDarkBright_orthogonal : inner ℝ crossingDark crossingBright = 0 := by
  have hba : inner ℝ compactB compactA = 0 := by
    rw [real_inner_comm, compactA_inner_compactB]
  simp only [crossingDark, crossingBright, inner_add_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right,
    compactA_inner_self, compactB_inner_self, compactA_inner_compactB, hba]
  norm_num

theorem coordinatedBright_leakage_zero : crossingLeakage crossingBright = 0 := by
  have h : crossingBright = (1 / 4 : ℝ) • compactA + (-1 / 4 : ℝ) • compactB := by
    unfold crossingBright
    module
  rw [h]
  exact crossingLeakage_pair_zero _ _

/-- Exact Schrödinger equations for any complex A/B coefficients under
the X-axis (pure first-ring detuning) pulse. -/
theorem coordinatedXAxis_Schrodinger (δ : ℝ) (a b : ℂ) (τ : ℝ) :
    HasDerivAt (coordinatedPairReal domainCompactA domainCompactB
      (crossingEnergy + δ) crossingEnergy a b)
      (onsitePlusBounded potential (coordinatedCorrection δ 0)
        (domainCoordinatedPairImag domainCompactA domainCompactB
          (crossingEnergy + δ) crossingEnergy a b τ)) τ ∧
    HasDerivAt (coordinatedPairImag domainCompactA domainCompactB
      (crossingEnergy + δ) crossingEnergy a b)
      (-(onsitePlusBounded potential (coordinatedCorrection δ 0)
        (domainCoordinatedPairReal domainCompactA domainCompactB
          (crossingEnergy + δ) crossingEnergy a b τ))) τ :=
  coordinatedPair_Schrodinger _ _ _ _ _
    (coordinatedXAxis_eigenA δ) (coordinatedXAxis_eigenB δ) a b τ

/-- Exact Schrödinger equations for any complex dark/bright coefficients
under the Z-axis (pure coordinated inter-ring) pulse. -/
theorem coordinatedZAxis_Schrodinger (η : ℝ) (a b : ℂ) (τ : ℝ) :
    HasDerivAt (coordinatedPairReal domainCrossingDark domainCrossingBright
      crossingEnergy (crossingEnergy + 2 * η) a b)
      (onsitePlusBounded potential (coordinatedCorrection 0 η)
        (domainCoordinatedPairImag domainCrossingDark domainCrossingBright
          crossingEnergy (crossingEnergy + 2 * η) a b τ)) τ ∧
    HasDerivAt (coordinatedPairImag domainCrossingDark domainCrossingBright
      crossingEnergy (crossingEnergy + 2 * η) a b)
      (-(onsitePlusBounded potential (coordinatedCorrection 0 η)
        (domainCoordinatedPairReal domainCrossingDark domainCrossingBright
          crossingEnergy (crossingEnergy + 2 * η) a b τ))) τ :=
  coordinatedPair_Schrodinger _ _ _ _ _
    (coordinatedZAxis_eigenDark η) (coordinatedZAxis_eigenBright η) a b τ

theorem coordinatedXAxis_norm_sq (δ : ℝ) (a b : ℂ) (τ : ℝ) :
    ‖coordinatedPairReal domainCompactA domainCompactB
      (crossingEnergy + δ) crossingEnergy a b τ‖ ^ 2 +
    ‖coordinatedPairImag domainCompactA domainCompactB
      (crossingEnergy + δ) crossingEnergy a b τ‖ ^ 2 =
    8 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := coordinatedPair_norm_sq domainCompactA domainCompactB
    compactA_inner_compactB (crossingEnergy + δ) crossingEnergy a b τ
  change _ = ‖a‖ ^ 2 * ‖compactA‖ ^ 2 + ‖b‖ ^ 2 * ‖compactB‖ ^ 2 at h
  rw [← real_inner_self_eq_norm_sq compactA, ← real_inner_self_eq_norm_sq compactB,
    compactA_inner_self, compactB_inner_self] at h
  rw [h]
  ring

theorem coordinatedZAxis_norm_sq (η : ℝ) (a b : ℂ) (τ : ℝ) :
    ‖coordinatedPairReal domainCrossingDark domainCrossingBright
      crossingEnergy (crossingEnergy + 2 * η) a b τ‖ ^ 2 +
    ‖coordinatedPairImag domainCrossingDark domainCrossingBright
      crossingEnergy (crossingEnergy + 2 * η) a b τ‖ ^ 2 =
    ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h := coordinatedPair_norm_sq domainCrossingDark domainCrossingBright
    coordinatedDarkBright_orthogonal crossingEnergy (crossingEnergy + 2 * η) a b τ
  change _ = ‖a‖ ^ 2 * ‖crossingDark‖ ^ 2 + ‖b‖ ^ 2 * ‖crossingBright‖ ^ 2 at h
  simpa only [crossingDark_norm_sq, crossingBright_norm_sq, mul_one] using h

theorem coordinatedXAxis_leakage_zero (δ : ℝ) (a b : ℂ) (τ : ℝ) :
    crossingLeakage (coordinatedPairReal domainCompactA domainCompactB
      (crossingEnergy + δ) crossingEnergy a b τ) = 0 ∧
    crossingLeakage (coordinatedPairImag domainCompactA domainCompactB
      (crossingEnergy + δ) crossingEnergy a b τ) = 0 := by
  have ha : crossingLeakage compactA = 0 := by
    simpa using crossingLeakage_pair_zero 1 0
  have hb : crossingLeakage compactB = 0 := by
    simpa using crossingLeakage_pair_zero 0 1
  exact coordinatedPair_leakage_zero domainCompactA domainCompactB ha hb _ _ _ _ _

theorem coordinatedZAxis_leakage_zero (η : ℝ) (a b : ℂ) (τ : ℝ) :
    crossingLeakage (coordinatedPairReal domainCrossingDark domainCrossingBright
      crossingEnergy (crossingEnergy + 2 * η) a b τ) = 0 ∧
    crossingLeakage (coordinatedPairImag domainCrossingDark domainCrossingBright
      crossingEnergy (crossingEnergy + 2 * η) a b τ) = 0 :=
  coordinatedPair_leakage_zero domainCrossingDark domainCrossingBright
    crossingDark_leakage_zero coordinatedBright_leakage_zero _ _ _ _ _

end
end SpectralGeometry.AmmannBeenker
