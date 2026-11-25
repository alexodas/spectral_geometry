module

public import SpectralGeometry.AmmannBeenkerCoordinatedPairDynamics
public import SpectralGeometry.AmmannBeenkerPulseSelfAdjoint
public import SpectralGeometry.AmmannBeenkerNearCrossingEigenvectors

public section

/-!
# Exact natural-domain dynamics for the two pure control axes (L7c)

Both controls have a complete pair of exact compact eigenvectors on
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


/-!
## L8a.2 — Exact controlled plane levels and reduction on the natural domain

The spectral characterization below concerns eigenvectors in the original
compact plane. No claim about separation from exterior levels is made here.
-/

/-- The midpoint of the two controlled compact-plane energies. -/
@[expose] def coordinatedLevelCenter (δ η : ℝ) : ℝ :=
  crossingEnergy + δ / 2 + η

/-- The nonnegative half-spacing of the controlled compact-plane energies. -/
@[expose] def coordinatedLevelRadius (δ η : ℝ) : ℝ :=
  Real.sqrt ((δ / 2) ^ 2 + η ^ 2)

theorem coordinatedLevelRadius_sq (δ η : ℝ) :
    coordinatedLevelRadius δ η ^ 2 = (δ / 2) ^ 2 + η ^ 2 := by
  unfold coordinatedLevelRadius
  exact Real.sq_sqrt (by positivity)

theorem coordinatedLevelRadius_eq_zero_iff (δ η : ℝ) :
    coordinatedLevelRadius δ η = 0 ↔ δ = 0 ∧ η = 0 := by
  constructor
  · intro h
    have hs := coordinatedLevelRadius_sq δ η
    rw [h] at hs
    constructor <;> nlinarith [sq_nonneg (δ / 2), sq_nonneg η]
  · rintro ⟨rfl, rfl⟩
    simp [coordinatedLevelRadius]

/-- Elementary real symmetric traceless two-by-two eigenvalue equation,
including the case in which both matrix entries vanish. -/
private theorem coordinated_traceless_eigen_iff (a b z : ℝ) :
    (∃ r s : ℝ, (r ≠ 0 ∨ s ≠ 0) ∧
      a * r + b * s = z * r ∧ b * r - a * s = z * s) ↔
      z ^ 2 = a ^ 2 + b ^ 2 := by
  constructor
  · rintro ⟨r, s, hn, h₁, h₂⟩
    have hr : (z ^ 2 - (a ^ 2 + b ^ 2)) * r = 0 := by
      linear_combination -(a + z) * h₁ - b * h₂
    have hs : (z ^ 2 - (a ^ 2 + b ^ 2)) * s = 0 := by
      linear_combination -b * h₁ + (a - z) * h₂
    rcases hn with hn | hn
    · exact sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_right hn)
    · exact sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_right hn)
  · intro hz
    by_cases hb : b = 0
    · subst b
      have hprod : (z - a) * (z + a) = 0 := by nlinarith only [hz]
      rcases mul_eq_zero.mp hprod with h | h
      · have he : z = a := sub_eq_zero.mp h
        subst z
        exact ⟨1, 0, Or.inl one_ne_zero, by ring, by ring⟩
      · have he : z = -a := by linarith
        subst z
        exact ⟨0, 1, Or.inr one_ne_zero, by ring, by ring⟩
    · refine ⟨b, z - a, Or.inl hb, ?_, ?_⟩
      · ring
      · linear_combination -hz

/-- Coefficient characterization of an exact full-Hamiltonian eigenpair
with input in the compact A/B plane. -/
theorem coordinatedCompact_eigen_iff (δ η energy r s : ℝ) :
    onsitePlusBounded potential (coordinatedCorrection δ η)
      (r • domainCompactA + s • domainCompactB) =
        energy • (r • compactA + s • compactB) ↔
      (δ / 2) * r + (-η) * s =
        (energy - coordinatedLevelCenter δ η) * r ∧
      (-η) * r - (δ / 2) * s =
        (energy - coordinatedLevelCenter δ η) * s := by
  change onsitePlusBounded potential
    (ringInteraction (crossingParameter + δ) + η • coordinatedRingControl)
    (r • domainCompactA + s • domainCompactB) = _ ↔ _
  rw [coordinatedControls_compact_action, smul_add, smul_smul, smul_smul]
  constructor
  · intro h
    have ha := congrArg crossingCoeffA h
    have hb := congrArg crossingCoeffB h
    simp only [crossingCoeffA_pair] at ha
    simp only [crossingCoeffB_pair] at hb
    unfold coordinatedLevelCenter
    constructor <;> linarith only [ha, hb]
  · rintro ⟨ha, hb⟩
    unfold coordinatedLevelCenter at ha hb
    have h₁ : (crossingEnergy + δ + η) * r - η * s = energy * r := by
      linarith only [ha]
    have h₂ : (crossingEnergy + η) * s - η * r = energy * s := by
      linarith only [hb]
    rw [h₁, h₂]

/-- Precisely the two explicit energies occur as eigenvalues of the
full natural-domain Hamiltonian on the original compact plane.
The statement is valid also when the two energies coincide. -/
theorem coordinatedPlane_eigenvalue_iff (δ η energy : ℝ) :
    (∃ x : infiniteOnsiteDomain potential,
      (x : TileHilbert Vertex) ≠ 0 ∧
      crossingLeakage (x : TileHilbert Vertex) = 0 ∧
      onsitePlusBounded potential (coordinatedCorrection δ η) x =
        energy • (x : TileHilbert Vertex)) ↔
      energy = coordinatedLevelCenter δ η - coordinatedLevelRadius δ η ∨
      energy = coordinatedLevelCenter δ η + coordinatedLevelRadius δ η := by
  have hscalar := coordinated_traceless_eigen_iff (δ / 2) (-η)
    (energy - coordinatedLevelCenter δ η)
  have hs := coordinatedLevelRadius_sq δ η
  constructor
  · rintro ⟨x, hn, hq, he⟩
    let r := crossingCoeffA (x : TileHilbert Vertex)
    let s := crossingCoeffB (x : TileHilbert Vertex)
    have hx : (x : TileHilbert Vertex) = r • compactA + s • compactB :=
      (crossingLeakage_eq_zero_iff _).mp hq
    have hd : x = r • domainCompactA + s • domainCompactB := by
      apply Subtype.ext
      exact hx
    have hne : r ≠ 0 ∨ s ≠ 0 := by
      by_contra! hh
      apply hn
      rw [hx, hh.1, hh.2, zero_smul, zero_smul, add_zero]
    have hcoeff := (coordinatedCompact_eigen_iff δ η energy r s).mp
      (by
        rw [← hd, ← hx]
        exact he)
    have hz := hscalar.mp ⟨r, s, hne, hcoeff⟩
    have hp : (energy - coordinatedLevelCenter δ η -
        coordinatedLevelRadius δ η) *
        (energy - coordinatedLevelCenter δ η +
          coordinatedLevelRadius δ η) = 0 := by
      nlinarith only [hz, hs]
    rcases mul_eq_zero.mp hp with h | h
    · right
      linarith only [h]
    · left
      linarith only [h]
  · intro he
    have hz : (energy - coordinatedLevelCenter δ η) ^ 2 =
        (δ / 2) ^ 2 + (-η) ^ 2 := by
      rcases he with h | h <;> rw [h] <;> nlinarith only [hs]
    obtain ⟨r, s, hn, hcoeff⟩ := hscalar.mpr hz
    refine ⟨r • domainCompactA + s • domainCompactB, ?_, ?_, ?_⟩
    · change r • compactA + s • compactB ≠ 0
      intro h
      have ha := congrArg crossingCoeffA h
      have hb := congrArg crossingCoeffB h
      have hzeroA : crossingCoeffA (0 : TileHilbert Vertex) = 0 := by
        simp [crossingCoeffA]
      have hzeroB : crossingCoeffB (0 : TileHilbert Vertex) = 0 := by
        simp [crossingCoeffB]
      rw [crossingCoeffA_pair, hzeroA] at ha
      rw [crossingCoeffB_pair, hzeroB] at hb
      rcases hn with hn | hn
      · exact hn ha
      · exact hn hb
    · exact crossingLeakage_pair_zero r s
    · exact (coordinatedCompact_eigen_iff δ η energy r s).mpr hcoeff

/-- Natural-domain lifts of the orthogonal projections onto the original
compact plane and its complement. -/
@[expose] def coordinatedPlaneDomainPart (x : infiniteOnsiteDomain potential) :
    infiniteOnsiteDomain potential :=
  crossingCoeffA (x : TileHilbert Vertex) • domainCompactA +
    crossingCoeffB (x : TileHilbert Vertex) • domainCompactB

@[expose] def coordinatedComplementDomainPart (x : infiniteOnsiteDomain potential) :
    infiniteOnsiteDomain potential :=
  x - coordinatedPlaneDomainPart x

theorem coordinatedPlaneDomainPart_coe (x : infiniteOnsiteDomain potential) :
    (coordinatedPlaneDomainPart x : TileHilbert Vertex) =
      crossingQubitPart (x : TileHilbert Vertex) := rfl

theorem coordinatedComplementDomainPart_coe (x : infiniteOnsiteDomain potential) :
    (coordinatedComplementDomainPart x : TileHilbert Vertex) =
      crossingLeakage (x : TileHilbert Vertex) := rfl

/-- The full Hamiltonian commutes with the compact-plane projection,
where the projected input is lifted to the original natural domain. -/
theorem coordinatedHamiltonian_plane_commutes (δ η : ℝ)
    (x : infiniteOnsiteDomain potential) :
    crossingQubitPart (onsitePlusBounded potential (coordinatedCorrection δ η) x) =
      onsitePlusBounded potential (coordinatedCorrection δ η)
        (coordinatedPlaneDomainPart x) := by
  let H := onsitePlusBounded potential (coordinatedCorrection δ η)
  have hA : H domainCompactA =
      (crossingEnergy + δ + η) • compactA + (-η) • compactB := by
    simpa [H, coordinatedCorrection] using
      coordinatedControls_compact_action δ η 1 0
  have hB : H domainCompactB =
      (-η) • compactA + (crossingEnergy + η) • compactB := by
    simpa [H, coordinatedCorrection] using
      coordinatedControls_compact_action δ η 0 1
  have hsA : inner ℝ (H domainCompactA) (x : TileHilbert Vertex) =
      inner ℝ compactA (H x) :=
    onsitePlusBounded_symmetric potential (coordinatedCorrection δ η)
      (coordinatedCorrection_symmetric δ η) domainCompactA x
  have hsB : inner ℝ (H domainCompactB) (x : TileHilbert Vertex) =
      inner ℝ compactB (H x) :=
    onsitePlusBounded_symmetric potential (coordinatedCorrection δ η)
      (coordinatedCorrection_symmetric δ η) domainCompactB x
  have ha : crossingCoeffA (H x) =
      (crossingEnergy + δ + η) * crossingCoeffA (x : TileHilbert Vertex) -
        η * crossingCoeffB (x : TileHilbert Vertex) := by
    unfold crossingCoeffA crossingCoeffB
    rw [← hsA, hA, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  have hb : crossingCoeffB (H x) =
      (crossingEnergy + η) * crossingCoeffB (x : TileHilbert Vertex) -
        η * crossingCoeffA (x : TileHilbert Vertex) := by
    unfold crossingCoeffA crossingCoeffB
    rw [← hsB, hB, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  change crossingQubitPart (H x) = H (coordinatedPlaneDomainPart x)
  unfold crossingQubitPart coordinatedPlaneDomainPart
  rw [ha, hb, map_add, map_smul, map_smul, hA, hB]
  module

/-- The orthogonal complement is reducing as well; the statement
includes domain preservation through the explicit projected input. -/
theorem coordinatedHamiltonian_complement_commutes (δ η : ℝ)
    (x : infiniteOnsiteDomain potential) :
    crossingLeakage (onsitePlusBounded potential (coordinatedCorrection δ η) x) =
      onsitePlusBounded potential (coordinatedCorrection δ η)
        (coordinatedComplementDomainPart x) := by
  rw [crossingLeakage, coordinatedHamiltonian_plane_commutes,
    coordinatedComplementDomainPart, map_sub]

/-- Every domain vector already in the complement has a full
Hamiltonian image orthogonal to both compact modes. -/
theorem coordinatedHamiltonian_complement_invariant (δ η : ℝ)
    (x : infiniteOnsiteDomain potential)
    (ha : inner ℝ compactA (x : TileHilbert Vertex) = 0)
    (hb : inner ℝ compactB (x : TileHilbert Vertex) = 0) :
    inner ℝ compactA (onsitePlusBounded potential (coordinatedCorrection δ η) x) = 0 ∧
      inner ℝ compactB (onsitePlusBounded potential (coordinatedCorrection δ η) x) = 0 := by
  have hp : coordinatedPlaneDomainPart x = 0 := by
    simp [coordinatedPlaneDomainPart, crossingCoeffA, crossingCoeffB, ha, hb]
  have hq : coordinatedComplementDomainPart x = x := by
    simp [coordinatedComplementDomainPart, hp]
  have h := coordinatedHamiltonian_complement_commutes δ η x
  rw [hq] at h
  constructor
  · rw [← h]
    exact crossingLeakage_inner_compactA _
  · rw [← h]
    exact crossingLeakage_inner_compactB _



/-!
## L8a.3 — Quantitative exclusion of exterior real spectral levels

The baseline reduced-gap estimate is transferred to the controlled
Hamiltonian by a bounded perturbation on the unchanged natural domain.
Compact resolvent then connects genuine eigenvectors to the complete
real bounded-inverse spectrum.
-/

/-- Uniform full-space bound for the applied perturbation on a vector. -/
theorem coordinatedControlPerturbation_apply_norm_le (δ η : ℝ)
    (x : TileHilbert Vertex) :
    ‖coordinatedControlPerturbation δ η x‖ ≤
      (|δ| + 2 * |η|) * ‖x‖ := by
  calc
    _ ≤ ‖coordinatedControlPerturbation δ η‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (coordinatedControlPerturbation_norm_le δ η) (norm_nonneg _)

/-- An arbitrary real energy residual on the exterior domain has the
baseline gap lower bound minus both the control budget and the energy
displacement. The lower bound remains valid even when it is nonpositive. -/
theorem coordinatedComplement_residual_lower (δ η energy : ℝ)
    (x : infiniteOnsiteDomain potential)
    (ha : inner ℝ compactA (x : TileHilbert Vertex) = 0)
    (hb : inner ℝ compactB (x : TileHilbert Vertex) = 0) :
    (crossingGapCandidate - (|δ| + 2 * |η|) -
      |energy - crossingEnergy|) * ‖(x : TileHilbert Vertex)‖ ≤
      ‖onsitePlusBounded potential (coordinatedCorrection δ η) x -
        energy • (x : TileHilbert Vertex)‖ := by
  have hq : crossingLeakage (x : TileHilbert Vertex) =
      (x : TileHilbert Vertex) := by
    simp [crossingLeakage, crossingQubitPart, crossingCoeffA,
      crossingCoeffB, ha, hb]
  have hg := crossingReducedGapResidualEstimate_full x
  rw [hq] at hg
  have hdecomp :
      onsitePlusBounded potential (coordinatedCorrection δ η) x =
        onsitePlusBounded potential (ringInteraction crossingParameter) x +
          coordinatedControlPerturbation δ η (x : TileHilbert Vertex) :=
    coordinatedControlHamiltonian_decomposition δ η x
  have hres :
      onsitePlusBounded potential (ringInteraction crossingParameter) x -
        crossingEnergy • (x : TileHilbert Vertex) =
      (onsitePlusBounded potential (coordinatedCorrection δ η) x -
        energy • (x : TileHilbert Vertex)) +
      ((energy - crossingEnergy) • (x : TileHilbert Vertex) -
        coordinatedControlPerturbation δ η (x : TileHilbert Vertex)) := by
    rw [hdecomp]
    module
  rw [hres] at hg
  have ht := norm_add_le
    (onsitePlusBounded potential (coordinatedCorrection δ η) x -
      energy • (x : TileHilbert Vertex))
    ((energy - crossingEnergy) • (x : TileHilbert Vertex) -
      coordinatedControlPerturbation δ η (x : TileHilbert Vertex))
  have hs := norm_sub_le
    ((energy - crossingEnergy) • (x : TileHilbert Vertex))
    (coordinatedControlPerturbation δ η (x : TileHilbert Vertex))
  rw [norm_smul, Real.norm_eq_abs] at hs
  have hB := coordinatedControlPerturbation_apply_norm_le δ η
    (x : TileHilbert Vertex)
  linarith only [hg, ht, hs, hB]

/-- Every genuine nonzero exterior eigenvector is outside the open
baseline-centered window of radius g minus the control budget. -/
theorem coordinatedComplement_eigenvalue_distance (δ η energy : ℝ)
    (x : infiniteOnsiteDomain potential)
    (hn : (x : TileHilbert Vertex) ≠ 0)
    (ha : inner ℝ compactA (x : TileHilbert Vertex) = 0)
    (hb : inner ℝ compactB (x : TileHilbert Vertex) = 0)
    (he : onsitePlusBounded potential (coordinatedCorrection δ η) x =
      energy • (x : TileHilbert Vertex)) :
    crossingGapCandidate ≤ |δ| + 2 * |η| + |energy - crossingEnergy| := by
  have h := coordinatedComplement_residual_lower δ η energy x ha hb
  rw [he, sub_self, norm_zero] at h
  by_contra! hlt
  have hp : 0 < crossingGapCandidate - (|δ| + 2 * |η|) -
      |energy - crossingEnergy| := by linarith only [hlt]
  have hpos := mul_pos hp (norm_pos_iff.mpr hn)
  exact (not_lt_of_ge h) hpos

/-- Any full eigenvector with a nonzero exterior component supplies a
genuine nonzero eigenvector in the reducing orthogonal complement. -/
theorem coordinatedEigenvector_complement_distance (δ η energy : ℝ)
    (x : infiniteOnsiteDomain potential)
    (he : onsitePlusBounded potential (coordinatedCorrection δ η) x =
      energy • (x : TileHilbert Vertex))
    (hq : crossingLeakage (x : TileHilbert Vertex) ≠ 0) :
    crossingGapCandidate ≤ |δ| + 2 * |η| + |energy - crossingEnergy| := by
  let q := coordinatedComplementDomainPart x
  have hc : (q : TileHilbert Vertex) =
      crossingLeakage (x : TileHilbert Vertex) :=
    coordinatedComplementDomainPart_coe x
  have heq : onsitePlusBounded potential (coordinatedCorrection δ η) q =
      energy • (q : TileHilbert Vertex) := by
    change onsitePlusBounded potential (coordinatedCorrection δ η)
      (coordinatedComplementDomainPart x) = _
    rw [← coordinatedHamiltonian_complement_commutes, he,
      crossingLeakage_smul, hc]
  apply coordinatedComplement_eigenvalue_distance δ η energy q
  · rwa [hc]
  · rw [hc]
    exact crossingLeakage_inner_compactA _
  · rw [hc]
    exact crossingLeakage_inner_compactB _
  · exact heq

/-- Properness of the confining potential gives the complete real
bounded-inverse spectral characterization at arbitrary coordinated
control strengths, not just the baseline or the pure axes. -/
theorem coordinatedRealSpectrum_iff_full_eigenvector (δ η energy : ℝ) :
    energy ∈ infiniteBoundedOnsiteRealSpectrum potential
      (coordinatedCorrection δ η) ↔
      ∃ x : infiniteOnsiteDomain potential,
        (x : TileHilbert Vertex) ≠ 0 ∧
        onsitePlusBounded potential (coordinatedCorrection δ η) x =
          energy • (x : TileHilbert Vertex) := by
  let B := coordinatedCorrection δ η
  let σ : Fin 0 → Vertex ≃ Vertex := fun i => Fin.elim0 i
  let w : Fin 0 → ℝ := fun _ => 0
  have hB : infiniteLocalBoundedCorrection 0 σ w B 1 0 = B :=
    zeroMatching_correction B
  obtain ⟨a, hunit, hsmall, _⟩ :=
    infiniteBoundedOnsite_exists_compact_shift
      potential 1 potential_lower potential_proper B
  have hs :
      ‖(infiniteLocalBoundedCorrection 0 σ w B 1 0).comp
        (infiniteOnsiteResolventCLM potential a hunit)‖ < 1 := by
    simpa only [hB] using hsmall
  have hspectrum :=
    infiniteLocalMatching_fullRealSpectrum_iff_hasFullEigenvalue
      0 potential σ w B 1 0 a hunit potential_proper hs energy
  rw [hB] at hspectrum
  change energy ∈ infiniteBoundedOnsiteRealSpectrum potential B ↔
    (∃ x : infiniteOnsiteDomain potential,
      (x : TileHilbert Vertex) ≠ 0 ∧
      infiniteLocalShiftedPerturbedOperator 0 potential σ w B 1 0 x =
        energy • (x : TileHilbert Vertex)) at hspectrum
  have hoperator :
      infiniteLocalShiftedPerturbedOperator 0 potential σ w B 1 0 =
        onsitePlusBounded potential B := by
    have h := (onsitePlusBounded_eq_local 0 potential σ w B 1 0).symm
    simpa only [hB] using h
  rw [hoperator] at hspectrum
  exact hspectrum

/-- All eigenvectors in the explicit open window lie in the original
plane, even if the two controlled levels are degenerate. -/
theorem coordinatedEigenvector_leakage_zero_of_near (δ η energy : ℝ)
    (x : infiniteOnsiteDomain potential)
    (he : onsitePlusBounded potential (coordinatedCorrection δ η) x =
      energy • (x : TileHilbert Vertex))
    (hnear : |δ| + 2 * |η| + |energy - crossingEnergy| <
      crossingGapCandidate) :
    crossingLeakage (x : TileHilbert Vertex) = 0 := by
  by_contra hn
  exact (not_le_of_gt hnear)
    (coordinatedEigenvector_complement_distance δ η energy x he hn)

/-- Exact characterization of the complete real bounded-inverse
spectrum inside the explicit baseline-centered open window.
No point-spectrum-only hypothesis is imposed on the energy. -/
theorem coordinatedRealSpectrum_near_iff (δ η energy : ℝ)
    (hnear : |δ| + 2 * |η| + |energy - crossingEnergy| <
      crossingGapCandidate) :
    energy ∈ infiniteBoundedOnsiteRealSpectrum potential
      (coordinatedCorrection δ η) ↔
      energy = coordinatedLevelCenter δ η - coordinatedLevelRadius δ η ∨
      energy = coordinatedLevelCenter δ η + coordinatedLevelRadius δ η := by
  rw [coordinatedRealSpectrum_iff_full_eigenvector]
  constructor
  · rintro ⟨x, hn, he⟩
    exact (coordinatedPlane_eigenvalue_iff δ η energy).mp
      ⟨x, hn, coordinatedEigenvector_leakage_zero_of_near δ η energy x he hnear, he⟩
  · intro h
    obtain ⟨x, hn, _, he⟩ :=
      (coordinatedPlane_eigenvalue_iff δ η energy).mpr h
    exact ⟨x, hn, he⟩



/-!
## L8a.4 — Consolidated quantitative isolation of the controlled cluster

The shift of either compact-plane level is bounded by the perturbation
norm on its genuine full-domain eigenvector. Together with the verified
exterior exclusion, this gives a positive separation in the complete
real bounded-inverse spectrum throughout an explicit control range.
-/

/-- Membership in the exact two-level set; at zero controls it is a
singleton, not an artificially distinct pair. -/
@[expose] def CoordinatedPlaneLevel (δ η e : ℝ) : Prop :=
  e = coordinatedLevelCenter δ η - coordinatedLevelRadius δ η ∨
  e = coordinatedLevelCenter δ η + coordinatedLevelRadius δ η

/-- The actual eigenvectors of the full operator give the displacement
bound directly, without an additional scalar square-root estimate. -/
theorem coordinatedPlaneLevel_shift_le (δ η e : ℝ)
    (hl : CoordinatedPlaneLevel δ η e) :
    |e - crossingEnergy| ≤ |δ| + 2 * |η| := by
  obtain ⟨x, hn, hq, he⟩ :=
    (coordinatedPlane_eigenvalue_iff δ η e).mpr hl
  have hx : (x : TileHilbert Vertex) =
      crossingQubitPart (x : TileHilbert Vertex) :=
    (crossingLeakage_eq_zero_iff _).mp hq
  have hd : x = coordinatedPlaneDomainPart x := by
    apply Subtype.ext
    rw [coordinatedPlaneDomainPart_coe]
    exact hx
  have hbase :
      onsitePlusBounded potential (ringInteraction crossingParameter) x =
        crossingEnergy • (x : TileHilbert Vertex) := by
    calc
      _ = onsitePlusBounded potential (ringInteraction crossingParameter)
          (coordinatedPlaneDomainPart x) := congrArg
            (onsitePlusBounded potential (ringInteraction crossingParameter)) hd
      _ = crossingEnergy • crossingQubitPart (x : TileHilbert Vertex) :=
        crossingQubitPart_restored_eigenvector (x : TileHilbert Vertex)
      _ = _ := congrArg (fun y : TileHilbert Vertex => crossingEnergy • y) hx.symm
  have hdecomp :
      onsitePlusBounded potential (coordinatedCorrection δ η) x =
        onsitePlusBounded potential (ringInteraction crossingParameter) x +
          coordinatedControlPerturbation δ η (x : TileHilbert Vertex) :=
    coordinatedControlHamiltonian_decomposition δ η x
  have hB :
      coordinatedControlPerturbation δ η (x : TileHilbert Vertex) =
        (e - crossingEnergy) • (x : TileHilbert Vertex) := by
    calc
      _ = onsitePlusBounded potential (coordinatedCorrection δ η) x -
          crossingEnergy • (x : TileHilbert Vertex) := by
        rw [hdecomp, hbase]
        abel
      _ = _ := by
        rw [he]
        module
  have h := coordinatedControlPerturbation_apply_norm_le δ η (x : TileHilbert Vertex)
  rw [hB, norm_smul, Real.norm_eq_abs] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hn)

/-- Every plane energy belongs to the complete real spectrum. -/
theorem coordinatedPlaneLevel_mem_realSpectrum (δ η e : ℝ)
    (hl : CoordinatedPlaneLevel δ η e) :
    e ∈ infiniteBoundedOnsiteRealSpectrum potential (coordinatedCorrection δ η) := by
  obtain ⟨x, hn, _, he⟩ :=
    (coordinatedPlane_eigenvalue_iff δ η e).mpr hl
  exact (coordinatedRealSpectrum_iff_full_eigenvector δ η e).mpr ⟨x, hn, he⟩

/-- At either exact plane level the exterior residual is bounded below
by the uniform cluster gap candidate, for every exterior domain vector. -/
theorem coordinatedPlaneLevel_complement_residual_lower (δ η e : ℝ)
    (hl : CoordinatedPlaneLevel δ η e)
    (x : infiniteOnsiteDomain potential)
    (ha : inner ℝ compactA (x : TileHilbert Vertex) = 0)
    (hb : inner ℝ compactB (x : TileHilbert Vertex) = 0) :
    (crossingGapCandidate - 2 * (|δ| + 2 * |η|)) *
        ‖(x : TileHilbert Vertex)‖ ≤
      ‖onsitePlusBounded potential (coordinatedCorrection δ η) x -
        e • (x : TileHilbert Vertex)‖ := by
  calc
    _ ≤ (crossingGapCandidate - (|δ| + 2 * |η|) -
          |e - crossingEnergy|) * ‖(x : TileHilbert Vertex)‖ :=
      mul_le_mul_of_nonneg_right
        (by linarith only [coordinatedPlaneLevel_shift_le δ η e hl])
        (norm_nonneg _)
    _ ≤ _ := coordinatedComplement_residual_lower δ η e x ha hb

/-- A full eigenvector with nonzero leakage is separated from each
plane energy by the uniform cluster gap candidate. -/
theorem coordinatedPlaneLevel_exterior_distance (δ η e level : ℝ)
    (hl : CoordinatedPlaneLevel δ η level)
    (x : infiniteOnsiteDomain potential)
    (he : onsitePlusBounded potential (coordinatedCorrection δ η) x =
      e • (x : TileHilbert Vertex))
    (hq : crossingLeakage (x : TileHilbert Vertex) ≠ 0) :
    crossingGapCandidate - 2 * (|δ| + 2 * |η|) ≤ |e - level| := by
  have h := coordinatedEigenvector_complement_distance δ η e x he hq
  have hshift := coordinatedPlaneLevel_shift_le δ η level hl
  have ht : |e - crossingEnergy| ≤ |e - level| + |level - crossingEnergy| :=
    abs_sub_le e level crossingEnergy
  linarith only [h, hshift, ht]

/-- Separation from every other point of the complete real spectrum,
not just a supplied exterior eigenvalue. -/
theorem coordinatedPlaneLevel_otherRealSpectrum_distance (δ η e level : ℝ)
    (hl : CoordinatedPlaneLevel δ η level)
    (he : e ∈ infiniteBoundedOnsiteRealSpectrum potential (coordinatedCorrection δ η))
    (hne : ¬ CoordinatedPlaneLevel δ η e) :
    crossingGapCandidate - 2 * (|δ| + 2 * |η|) ≤ |e - level| := by
  have hshift := coordinatedPlaneLevel_shift_le δ η level hl
  have ht : |e - crossingEnergy| ≤ |e - level| + |level - crossingEnergy| :=
    abs_sub_le e level crossingEnergy
  by_contra! hlt
  have hnear : |δ| + 2 * |η| + |e - crossingEnergy| <
      crossingGapCandidate := by linarith only [hshift, ht, hlt]
  exact hne ((coordinatedRealSpectrum_near_iff δ η e hnear).mp he)

/-- Both plane energies lie in the explicit open window for small
controls, and every full-domain eigenvector there has zero leakage. -/
theorem coordinatedPlaneLevel_in_protected_window (δ η e : ℝ)
    (hsmall : 2 * (|δ| + 2 * |η|) < crossingGapCandidate)
    (hl : CoordinatedPlaneLevel δ η e) :
    |δ| + 2 * |η| + |e - crossingEnergy| < crossingGapCandidate := by
  linarith only [hsmall, coordinatedPlaneLevel_shift_le δ η e hl]

/-- Consolidated full-infinite-operator isolation theorem with explicit
numerical admissible controls and separation. Both compact levels belong
to the full real spectrum, are the entire spectrum in the closed
control-budget window, and have no exterior eigenvectors. Every other
spectral energy and every eigenvector with nonzero exterior component
are separated from each plane level by the stated positive constant.
The zero-control case is included. -/
theorem coordinatedCluster_isolation (δ η : ℝ)
    (hsmall : |δ| + 2 * |η| < 1 / 256) :
    0 < (1 / 128 : ℝ) - 2 * (|δ| + 2 * |η|) ∧
    (∀ level : ℝ, CoordinatedPlaneLevel δ η level →
      level ∈ infiniteBoundedOnsiteRealSpectrum potential
        (coordinatedCorrection δ η) ∧
      |level - crossingEnergy| ≤ |δ| + 2 * |η| ∧
      ∀ x : infiniteOnsiteDomain potential,
        onsitePlusBounded potential (coordinatedCorrection δ η) x =
          level • (x : TileHilbert Vertex) →
        crossingLeakage (x : TileHilbert Vertex) = 0) ∧
    (∀ e : ℝ, |e - crossingEnergy| ≤ |δ| + 2 * |η| →
      (e ∈ infiniteBoundedOnsiteRealSpectrum potential
        (coordinatedCorrection δ η) ↔ CoordinatedPlaneLevel δ η e)) ∧
    (∀ e level : ℝ, CoordinatedPlaneLevel δ η level →
      e ∈ infiniteBoundedOnsiteRealSpectrum potential
        (coordinatedCorrection δ η) →
      ¬ CoordinatedPlaneLevel δ η e →
      (1 / 128 : ℝ) - 2 * (|δ| + 2 * |η|) ≤ |e - level|) ∧
    (∀ e level : ℝ, CoordinatedPlaneLevel δ η level →
      ∀ x : infiniteOnsiteDomain potential,
        onsitePlusBounded potential (coordinatedCorrection δ η) x =
          e • (x : TileHilbert Vertex) →
        crossingLeakage (x : TileHilbert Vertex) ≠ 0 →
        (1 / 128 : ℝ) - 2 * (|δ| + 2 * |η|) ≤ |e - level|) := by
  have hs : 2 * (|δ| + 2 * |η|) < crossingGapCandidate := by
    change 2 * (|δ| + 2 * |η|) < (1 / 128 : ℝ)
    linarith only [hsmall]
  refine ⟨by linarith only [hsmall], ?_, ?_, ?_, ?_⟩
  · intro level hl
    refine ⟨coordinatedPlaneLevel_mem_realSpectrum δ η level hl,
      coordinatedPlaneLevel_shift_le δ η level hl, ?_⟩
    intro x he
    exact coordinatedEigenvector_leakage_zero_of_near δ η level x he
      (coordinatedPlaneLevel_in_protected_window δ η level hs hl)
  · intro e hnear
    exact coordinatedRealSpectrum_near_iff δ η e (by linarith only [hs, hnear])
  · intro e level hl he hne
    exact coordinatedPlaneLevel_otherRealSpectrum_distance δ η e level hl he hne
  · intro e level hl x he hq
    exact coordinatedPlaneLevel_exterior_distance δ η e level hl x he hq



/-!
## L8a refinement — Centered control estimates

Subtracting the midpoint shift from the bounded perturbation avoids
counting the same scalar displacement twice. Each centered individual
control is a scaled isometry on the full real Hilbert space.
-/

private theorem coordinated_eq_of_nonneg_sq (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) : a = b := by
  have hp : (a - b) * (a + b) = 0 := by nlinarith only [h]
  rcases mul_eq_zero.mp hp with h₁ | h₂
  · exact sub_eq_zero.mp h₁
  · linarith only [ha, hb, h₂]

/-- Centering the first-ring orthogonal projection gives an exact
half-isometry on every vector, including exterior vectors. -/
theorem coordinatedOnsite_centered_norm (x : TileHilbert Vertex) :
    ‖finiteSectorProjection (neighbors origin) x - (1 / 2 : ℝ) • x‖ =
      (1 / 2 : ℝ) * ‖x‖ := by
  let y := finiteSectorProjection (neighbors origin) x
  have hi : inner ℝ x y = ‖y‖ ^ 2 :=
    finiteSectorProjection_inner (neighbors origin) x
  have hj : inner ℝ y x = ‖y‖ ^ 2 := by
    rw [real_inner_comm, hi]
  change ‖y - (1 / 2 : ℝ) • x‖ = (1 / 2 : ℝ) * ‖x‖
  apply coordinated_eq_of_nonneg_sq _ _ (norm_nonneg _) (by positivity)
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hi, hj]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  ring

/-- M-I is an exact isometry because the matching operator is
symmetric and satisfies M²=2M. -/
theorem coordinatedRing_centered_norm (x : TileHilbert Vertex) :
    ‖coordinatedRingControl x - x‖ = ‖x‖ := by
  have hi : ‖coordinatedRingControl x‖ ^ 2 =
      2 * inner ℝ x (coordinatedRingControl x) := by
    rw [← real_inner_self_eq_norm_sq,
      ← coordinatedRingControl_symmetric x (coordinatedRingControl x),
      coordinatedRingControl_sq_apply, real_inner_smul_right]
  have hj : inner ℝ (coordinatedRingControl x) x =
      inner ℝ x (coordinatedRingControl x) := real_inner_comm _ _
  apply coordinated_eq_of_nonneg_sq _ _ (norm_nonneg _) (norm_nonneg _)
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq, hj]
  linarith only [hi]

/-- Centered perturbation force bound: half the original control
budget, uniformly on the whole Hilbert space. -/
theorem coordinatedControl_centered_apply_norm_le (δ η : ℝ)
    (x : TileHilbert Vertex) :
    ‖coordinatedControlPerturbation δ η x - (δ / 2 + η) • x‖ ≤
      ((|δ| + 2 * |η|) / 2) * ‖x‖ := by
  have he : coordinatedControlPerturbation δ η x - (δ / 2 + η) • x =
      δ • (finiteSectorProjection (neighbors origin) x - (1 / 2 : ℝ) • x) +
        η • (coordinatedRingControl x - x) := by
    simp only [coordinatedControlPerturbation, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply]
    module
  rw [he]
  calc
    _ ≤ ‖δ • (finiteSectorProjection (neighbors origin) x - (1 / 2 : ℝ) • x)‖ +
        ‖η • (coordinatedRingControl x - x)‖ := norm_add_le _ _
    _ = _ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        coordinatedOnsite_centered_norm, coordinatedRing_centered_norm]
      ring

theorem coordinatedLevelRadius_le_half_budget (δ η : ℝ) :
    coordinatedLevelRadius δ η ≤ (|δ| + 2 * |η|) / 2 := by
  have hs := coordinatedLevelRadius_sq δ η
  have hδ : |δ| ^ 2 = δ ^ 2 := sq_abs δ
  have hη : |η| ^ 2 = η ^ 2 := sq_abs η
  have hp := mul_nonneg (abs_nonneg δ) (abs_nonneg η)
  have hsq : coordinatedLevelRadius δ η ^ 2 ≤
      ((|δ| + 2 * |η|) / 2) ^ 2 := by
    nlinarith only [hs, hδ, hη, hp]
  have hr : 0 ≤ coordinatedLevelRadius δ η := Real.sqrt_nonneg _
  have hb : 0 ≤ (|δ| + 2 * |η|) / 2 := by positivity
  by_contra! hn
  have ht := mul_pos (sub_pos.mpr hn)
    (show 0 < coordinatedLevelRadius δ η + (|δ| + 2 * |η|) / 2 by
      linarith only [hn, hb])
  nlinarith only [ht, hsq]

theorem coordinatedPlaneLevel_center_distance (δ η e : ℝ)
    (hl : CoordinatedPlaneLevel δ η e) :
    |e - coordinatedLevelCenter δ η| = coordinatedLevelRadius δ η := by
  have hr : 0 ≤ coordinatedLevelRadius δ η := Real.sqrt_nonneg _
  rcases hl with h | h
  · rw [h]
    have he : coordinatedLevelCenter δ η - coordinatedLevelRadius δ η -
        coordinatedLevelCenter δ η = -coordinatedLevelRadius δ η := by ring
    rw [he, abs_neg, abs_of_nonneg hr]
  · rw [h]
    have he : coordinatedLevelCenter δ η + coordinatedLevelRadius δ η -
        coordinatedLevelCenter δ η = coordinatedLevelRadius δ η := by ring
    rw [he, abs_of_nonneg hr]

/-- The centered residual bound for every exterior domain vector. -/
theorem coordinatedComplement_centered_residual_lower (δ η energy : ℝ)
    (x : infiniteOnsiteDomain potential)
    (ha : inner ℝ compactA (x : TileHilbert Vertex) = 0)
    (hb : inner ℝ compactB (x : TileHilbert Vertex) = 0) :
    (crossingGapCandidate - (|δ| + 2 * |η|) / 2 -
      |energy - coordinatedLevelCenter δ η|) * ‖(x : TileHilbert Vertex)‖ ≤
      ‖onsitePlusBounded potential (coordinatedCorrection δ η) x -
        energy • (x : TileHilbert Vertex)‖ := by
  have hq : crossingLeakage (x : TileHilbert Vertex) =
      (x : TileHilbert Vertex) := by
    simp [crossingLeakage, crossingQubitPart, crossingCoeffA,
      crossingCoeffB, ha, hb]
  have hg := crossingReducedGapResidualEstimate_full x
  rw [hq] at hg
  have hdecomp :
      onsitePlusBounded potential (coordinatedCorrection δ η) x =
        onsitePlusBounded potential (ringInteraction crossingParameter) x +
          coordinatedControlPerturbation δ η (x : TileHilbert Vertex) :=
    coordinatedControlHamiltonian_decomposition δ η x
  have hres :
      onsitePlusBounded potential (ringInteraction crossingParameter) x -
        crossingEnergy • (x : TileHilbert Vertex) =
      (onsitePlusBounded potential (coordinatedCorrection δ η) x -
        energy • (x : TileHilbert Vertex)) +
      ((energy - coordinatedLevelCenter δ η) • (x : TileHilbert Vertex) -
        (coordinatedControlPerturbation δ η (x : TileHilbert Vertex) -
          (δ / 2 + η) • (x : TileHilbert Vertex))) := by
    rw [hdecomp]
    unfold coordinatedLevelCenter
    module
  rw [hres] at hg
  have ht := norm_add_le
    (onsitePlusBounded potential (coordinatedCorrection δ η) x -
      energy • (x : TileHilbert Vertex))
    ((energy - coordinatedLevelCenter δ η) • (x : TileHilbert Vertex) -
      (coordinatedControlPerturbation δ η (x : TileHilbert Vertex) -
        (δ / 2 + η) • (x : TileHilbert Vertex)))
  have hs := norm_sub_le
    ((energy - coordinatedLevelCenter δ η) • (x : TileHilbert Vertex))
    (coordinatedControlPerturbation δ η (x : TileHilbert Vertex) -
      (δ / 2 + η) • (x : TileHilbert Vertex))
  rw [norm_smul, Real.norm_eq_abs] at hs
  have hB := coordinatedControl_centered_apply_norm_le δ η
    (x : TileHilbert Vertex)
  linarith only [hg, ht, hs, hB]

/-- Nonzero leakage forces an eigenvalue outside the centered window. -/
theorem coordinatedEigenvector_centered_complement_distance (δ η energy : ℝ)
    (x : infiniteOnsiteDomain potential)
    (he : onsitePlusBounded potential (coordinatedCorrection δ η) x =
      energy • (x : TileHilbert Vertex))
    (hq : crossingLeakage (x : TileHilbert Vertex) ≠ 0) :
    crossingGapCandidate ≤ (|δ| + 2 * |η|) / 2 +
      |energy - coordinatedLevelCenter δ η| := by
  let q := coordinatedComplementDomainPart x
  have hc : (q : TileHilbert Vertex) =
      crossingLeakage (x : TileHilbert Vertex) :=
    coordinatedComplementDomainPart_coe x
  have heq : onsitePlusBounded potential (coordinatedCorrection δ η) q =
      energy • (q : TileHilbert Vertex) := by
    change onsitePlusBounded potential (coordinatedCorrection δ η)
      (coordinatedComplementDomainPart x) = _
    rw [← coordinatedHamiltonian_complement_commutes, he,
      crossingLeakage_smul, hc]
  have ha : inner ℝ compactA (q : TileHilbert Vertex) = 0 := by
    rw [hc]
    exact crossingLeakage_inner_compactA _
  have hb : inner ℝ compactB (q : TileHilbert Vertex) = 0 := by
    rw [hc]
    exact crossingLeakage_inner_compactB _
  have hn : (q : TileHilbert Vertex) ≠ 0 := by rwa [hc]
  have h := coordinatedComplement_centered_residual_lower δ η energy q ha hb
  rw [heq, sub_self, norm_zero] at h
  by_contra! hlt
  have hp : 0 < crossingGapCandidate - (|δ| + 2 * |η|) / 2 -
      |energy - coordinatedLevelCenter δ η| := by linarith only [hlt]
  exact (not_lt_of_ge h) (mul_pos hp (norm_pos_iff.mpr hn))

theorem coordinatedRealSpectrum_centered_near_iff (δ η energy : ℝ)
    (hnear : (|δ| + 2 * |η|) / 2 +
      |energy - coordinatedLevelCenter δ η| < crossingGapCandidate) :
    energy ∈ infiniteBoundedOnsiteRealSpectrum potential
      (coordinatedCorrection δ η) ↔ CoordinatedPlaneLevel δ η energy := by
  rw [coordinatedRealSpectrum_iff_full_eigenvector]
  constructor
  · rintro ⟨x, hn, he⟩
    have hq : crossingLeakage (x : TileHilbert Vertex) = 0 := by
      by_contra h
      exact (not_le_of_gt hnear)
        (coordinatedEigenvector_centered_complement_distance δ η energy x he h)
    exact (coordinatedPlane_eigenvalue_iff δ η energy).mp ⟨x, hn, hq, he⟩
  · intro h
    obtain ⟨x, hn, _, he⟩ := (coordinatedPlane_eigenvalue_iff δ η energy).mpr h
    exact ⟨x, hn, he⟩

/-- Improved cluster separation, with the exact half-spacing and the
centered half-budget. The old theorem is retained unchanged. -/
theorem coordinatedCluster_centered_isolation (δ η : ℝ)
    (hsmall : (|δ| + 2 * |η|) / 2 + coordinatedLevelRadius δ η < 1 / 128) :
    0 < (1 / 128 : ℝ) - (|δ| + 2 * |η|) / 2 - coordinatedLevelRadius δ η ∧
    (∀ level : ℝ, CoordinatedPlaneLevel δ η level →
      level ∈ infiniteBoundedOnsiteRealSpectrum potential (coordinatedCorrection δ η) ∧
      ∀ x : infiniteOnsiteDomain potential,
        onsitePlusBounded potential (coordinatedCorrection δ η) x =
          level • (x : TileHilbert Vertex) →
        crossingLeakage (x : TileHilbert Vertex) = 0) ∧
    (∀ e : ℝ, |e - coordinatedLevelCenter δ η| ≤ coordinatedLevelRadius δ η →
      (e ∈ infiniteBoundedOnsiteRealSpectrum potential (coordinatedCorrection δ η) ↔
        CoordinatedPlaneLevel δ η e)) ∧
    (∀ e level : ℝ, CoordinatedPlaneLevel δ η level →
      e ∈ infiniteBoundedOnsiteRealSpectrum potential (coordinatedCorrection δ η) →
      ¬ CoordinatedPlaneLevel δ η e →
      (1 / 128 : ℝ) - (|δ| + 2 * |η|) / 2 - coordinatedLevelRadius δ η ≤
        |e - level|) ∧
    (∀ e level : ℝ, CoordinatedPlaneLevel δ η level →
      ∀ x : infiniteOnsiteDomain potential,
        onsitePlusBounded potential (coordinatedCorrection δ η) x =
          e • (x : TileHilbert Vertex) →
        crossingLeakage (x : TileHilbert Vertex) ≠ 0 →
        (1 / 128 : ℝ) - (|δ| + 2 * |η|) / 2 - coordinatedLevelRadius δ η ≤
          |e - level|) := by
  have hs : (|δ| + 2 * |η|) / 2 + coordinatedLevelRadius δ η <
      crossingGapCandidate := hsmall
  refine ⟨by linarith only [hsmall], ?_, ?_, ?_, ?_⟩
  · intro level hl
    refine ⟨coordinatedPlaneLevel_mem_realSpectrum δ η level hl, ?_⟩
    intro x he
    by_contra hq
    have h := coordinatedEigenvector_centered_complement_distance δ η level x he hq
    rw [coordinatedPlaneLevel_center_distance δ η level hl] at h
    linarith only [h, hs]
  · intro e hnear
    exact coordinatedRealSpectrum_centered_near_iff δ η e (by linarith only [hs, hnear])
  · intro e level hl he hne
    have ht := abs_sub_le e level (coordinatedLevelCenter δ η)
    rw [coordinatedPlaneLevel_center_distance δ η level hl] at ht
    by_contra! hlt
    have hnear : (|δ| + 2 * |η|) / 2 +
        |e - coordinatedLevelCenter δ η| < crossingGapCandidate := by
      change (|δ| + 2 * |η|) / 2 + |e - coordinatedLevelCenter δ η| < (1 / 128 : ℝ)
      linarith only [ht, hlt]
    exact hne ((coordinatedRealSpectrum_centered_near_iff δ η e hnear).mp he)
  · intro e level hl x he hq
    have ht := abs_sub_le e level (coordinatedLevelCenter δ η)
    rw [coordinatedPlaneLevel_center_distance δ η level hl] at ht
    have h := coordinatedEigenvector_centered_complement_distance δ η e x he hq
    change (1 / 128 : ℝ) ≤ _ at h
    linarith only [ht, h]

/-- The entire doubled control diamond is sufficient for the improved
theorem, whose exact-radius criterion can be still less restrictive. -/
theorem coordinatedCluster_centered_condition_of_budget (δ η : ℝ)
    (hsmall : |δ| + 2 * |η| < 1 / 128) :
    (|δ| + 2 * |η|) / 2 + coordinatedLevelRadius δ η < 1 / 128 := by
  linarith only [hsmall, coordinatedLevelRadius_le_half_budget δ η]

theorem coordinatedCluster_centered_gap_ge (δ η : ℝ) :
    (1 / 128 : ℝ) - (|δ| + 2 * |η|) ≤
      1 / 128 - (|δ| + 2 * |η|) / 2 - coordinatedLevelRadius δ η := by
  linarith only [coordinatedLevelRadius_le_half_budget δ η]


end
end SpectralGeometry.AmmannBeenker
