module

public import SpectralGeometry.AmmannBeenkerCoordinatedPairDynamics
public import SpectralGeometry.AmmannBeenkerPulseSelfAdjoint

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


end
end SpectralGeometry.AmmannBeenker
