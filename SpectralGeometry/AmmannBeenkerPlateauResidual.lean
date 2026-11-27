module

public import SpectralGeometry.AmmannBeenkerPlateauCrossing
public import SpectralGeometry.AmmannBeenkerCrossingGapOrthogonality
public import SpectralGeometry.AmmannBeenkerQubitLeakage

public section

/-!
# Quantitative residual estimate for the bounded plateau crossing

Reuse the certified central singular-value bound 1/24, the exterior
barrier 2 and the boundary coupling bound 1/4. The residual estimate
does not assume an eigenvalue equation. We first prove it on the old
dense natural domain; extension to all real square-summable states
is a separate obligation.
No compact-resolvent argument or spectral-exclusion claim is used.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

@[expose] def plateauResidual (C : ℝ) (hC : 1 ≤ C) :
    TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  plateauHamiltonian C hC - crossingEnergy • ContinuousLinearMap.id ℝ (TileHilbert Vertex)

theorem plateauResidual_symmetric (C : ℝ) (hC : 1 ≤ C)
    (x y : TileHilbert Vertex) :
    inner ℝ (plateauResidual C hC x) y = inner ℝ x (plateauResidual C hC y) := by
  change inner ℝ (plateauHamiltonian C hC x - crossingEnergy • x) y =
    inner ℝ x (plateauHamiltonian C hC y - crossingEnergy • y)
  rw [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    plateauHamiltonian_symmetric C hC x y]

/-- The sharp exterior lower bound survives any truncation at or above
the canonical plateau height. -/
theorem plateauPotential_exterior_lower (C : ℝ) (hC : canonicalPlateauHeight ≤ C)
    (v : Vertex) (hv : v ∉ sector) :
    4 + 4 * alpha ≤ plateauPotential C v := by
  exact le_min (potential_outside_sector_sharp v hv) hC

/-- On the central coordinates the shifted action has not changed,
even for vectors with an exterior component. -/
theorem plateauResidual_projected_eq (C : ℝ) (hC : 1 ≤ C) (hfive : 5 ≤ C)
    (x : infiniteOnsiteDomain potential) :
    finiteSectorProjection sector (plateauResidual C hC x.1) =
      finiteSectorProjection sector (crossingResidual x) := by
  apply lp.ext
  funext v
  rw [finiteSectorProjection_apply, finiteSectorProjection_apply]
  by_cases hv : v ∈ sector
  · rw [if_pos hv, if_pos hv]
    rw [crossingResidual_apply, onsitePlusBounded_apply]
    change plateauOnsite C hC x.1 v + ringInteraction crossingParameter x.1 v -
        crossingEnergy * x.1 v =
      infiniteOnsiteOperator potential x v + ringInteraction crossingParameter x.1 v -
        crossingEnergy * x.1 v
    rw [plateauOnsite_apply, infiniteOnsiteOperator_apply,
      plateauPotential_eq_on_sector C hfive v hv]
  · rw [if_neg hv, if_neg hv]

theorem plateauResidual_exterior_energy_ge_two (C : ℝ) (hC : 1 ≤ C)
    (hheight : canonicalPlateauHeight ≤ C) (x : infiniteOnsiteDomain potential) :
    (2 : ℝ) * ‖(exteriorDomainPart x).1‖ ^ 2 ≤
      inner ℝ (exteriorDomainPart x).1
        (plateauResidual C hC (exteriorDomainPart x).1) := by
  let q := exteriorDomainPart x
  let y : infiniteOnsiteDomain (plateauPotential C) :=
    ⟨q.1, by rw [plateauPotential_domain_top C hC]; exact Submodule.mem_top⟩
  have h := onsitePlusNonneg_sector_form_bound (plateauPotential C)
    (ringInteraction crossingParameter) crossingInteraction_nonneg
    1 (4 + 4 * alpha) (fun v => (plateauPotential_bounds C hC v).1)
    sector (plateauPotential_exterior_lower C hheight) y
  change (4 + 4 * alpha) * ‖q.1‖ ^ 2 -
      (4 + 4 * alpha - 1) * ‖finiteSectorProjection sector q.1‖ ^ 2 ≤
    inner ℝ q.1 (onsitePlusBounded (plateauPotential C)
      (ringInteraction crossingParameter) y) at h
  rw [show finiteSectorProjection sector q.1 = 0 from exteriorDomainPart_projection x,
    norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero,
    ← plateauHamiltonian_agrees_natural C hC y] at h
  change (2 : ℝ) * ‖q.1‖ ^ 2 ≤
    inner ℝ q.1 (plateauHamiltonian C hC q.1 - crossingEnergy • q.1)
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hb : (2 : ℝ) ≤ 4 + 4 * alpha - crossingEnergy := by
    unfold crossingEnergy
    linarith [crossingExteriorCoefficient_gt_two]
  have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖q.1‖)
  nlinarith only [h, hh]

/-- Both blocks retain their original coupling estimate. -/
theorem plateauResidual_mixed_abs_bound (C : ℝ) (hC : 1 ≤ C)
    (hfive : 5 ≤ C) (x : infiniteOnsiteDomain potential) :
    |inner ℝ (centralDomainPart x).1
        (plateauResidual C hC (exteriorDomainPart x).1)| ≤
      (1 / 4 : ℝ) * ‖(centralDomainPart x).1‖ * ‖(exteriorDomainPart x).1‖ := by
  have he : inner ℝ (centralDomainPart x).1
      (plateauResidual C hC (exteriorDomainPart x).1) =
      inner ℝ (centralDomainPart x).1 (crossingResidual (exteriorDomainPart x)) := by
    change inner ℝ (finiteSectorProjection sector x.1)
        (plateauResidual C hC (exteriorDomainPart x).1) =
      inner ℝ (finiteSectorProjection sector x.1)
        (crossingResidual (exteriorDomainPart x))
    rw [finiteSectorProjection_symmetric, finiteSectorProjection_symmetric,
      plateauResidual_projected_eq C hC hfive (exteriorDomainPart x)]
  rw [he]
  exact crossingResidual_central_exterior_inner_abs_bound x x

theorem plateauResidual_central_norm_lower (C : ℝ) (hC : 1 ≤ C)
    (hfive : 5 ≤ C) (x : infiniteOnsiteDomain potential)
    (ha : inner ℝ x.1 compactA = 0) (hb : inner ℝ x.1 compactB = 0) :
    (1 / 24 : ℝ) * ‖(centralDomainPart x).1‖ ≤
      ‖finiteSectorProjection sector (plateauResidual C hC (centralDomainPart x).1)‖ := by
  rw [plateauResidual_projected_eq C hC hfive (centralDomainPart x)]
  have hsq := crossingCentralResidual_projected_norm_sq_lower x
    (by simpa only [crossingCentralPart_centralVertex_apply,
      ← crossingCompactA_inner_coordinates x] using ha)
    (by simpa only [crossingCentralPart_centralVertex_apply,
      ← crossingCompactB_inner_coordinates x] using hb)
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  calc
    ((1 / 24 : ℝ) * ‖(centralDomainPart x).1‖) ^ 2 =
        (1 / 576 : ℝ) * ‖(centralDomainPart x).1‖ ^ 2 := by ring
    _ ≤ _ := hsq

/-- The two inhomogeneous Schur inequalities for an arbitrary
orthogonal state in the old natural domain. -/
theorem plateauResidual_block_bounds (C : ℝ) (hC : 1 ≤ C)
    (hheight : canonicalPlateauHeight ≤ C) (x : infiniteOnsiteDomain potential)
    (ha : inner ℝ x.1 compactA = 0) (hb : inner ℝ x.1 compactB = 0) :
    (1 / 24 : ℝ) * ‖(centralDomainPart x).1‖ ≤
        ‖plateauResidual C hC x.1‖ + (1 / 4 : ℝ) * ‖(exteriorDomainPart x).1‖ ∧
      (2 : ℝ) * ‖(exteriorDomainPart x).1‖ ≤
        ‖plateauResidual C hC x.1‖ + (1 / 4 : ℝ) * ‖(centralDomainPart x).1‖ := by
  let c := centralDomainPart x
  let q := exteriorDomainPart x
  let T := plateauResidual C hC
  have hfive := canonicalPlateauHeight_ge_five.trans hheight
  have hsum : x.1 = c.1 + q.1 := by
    change x.1 = (centralDomainPart x).1 + (x.1 - (centralDomainPart x).1)
    abel
  have hTc : T c.1 = T x.1 - T q.1 := by
    calc
      T c.1 = T (x.1 - q.1) := by rw [hsum]; congr 1; abel
      _ = _ := map_sub T _ _
  have hTq : T q.1 = T x.1 - T c.1 := by
    calc
      T q.1 = T (x.1 - c.1) := by rw [hsum]; congr 1; abel
      _ = _ := map_sub T _ _
  have hproj : ‖finiteSectorProjection sector (T x.1)‖ ≤ ‖T x.1‖ := by
    calc
      _ ≤ ‖finiteSectorProjection sector‖ * ‖T x.1‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖T x.1‖ := mul_le_mul_of_nonneg_right
        (finiteSectorProjection_norm_le sector) (norm_nonneg _)
      _ = _ := one_mul _
  have hqproj : ‖finiteSectorProjection sector (T q.1)‖ ≤ (1 / 4 : ℝ) * ‖q.1‖ := by
    change ‖finiteSectorProjection sector (plateauResidual C hC (exteriorDomainPart x).1)‖ ≤ _
    rw [plateauResidual_projected_eq C hC hfive (exteriorDomainPart x)]
    exact crossingResidual_exterior_projected_norm_le x
  constructor
  · calc
      (1 / 24 : ℝ) * ‖c.1‖ ≤ ‖finiteSectorProjection sector (T c.1)‖ :=
        plateauResidual_central_norm_lower C hC hfive x ha hb
      _ ≤ ‖finiteSectorProjection sector (T x.1)‖ +
          ‖finiteSectorProjection sector (T q.1)‖ := by
        rw [hTc, map_sub]
        exact norm_sub_le _ _
      _ ≤ _ := add_le_add hproj hqproj
  · have hmixed : |inner ℝ q.1 (T c.1)| ≤ (1 / 4 : ℝ) * ‖c.1‖ * ‖q.1‖ := by
      rw [← plateauResidual_symmetric C hC q.1 c.1, real_inner_comm]
      exact plateauResidual_mixed_abs_bound C hC hfive x
    have henergy := plateauResidual_exterior_energy_ge_two C hC hheight x
    change (2 : ℝ) * ‖q.1‖ ^ 2 ≤ inner ℝ q.1 (T q.1) at henergy
    rw [hTq, inner_sub_right] at henergy
    have hcs := real_inner_le_norm q.1 (T x.1)
    have hmix := (abs_le.mp hmixed).1
    have hsquared : (2 : ℝ) * ‖q.1‖ ^ 2 ≤
        (‖T x.1‖ + (1 / 4 : ℝ) * ‖c.1‖) * ‖q.1‖ := by
      nlinarith only [henergy, hcs, hmix]
    by_cases hz : ‖q.1‖ = 0
    · change (2 : ℝ) * ‖q.1‖ ≤ ‖T x.1‖ + (1 / 4 : ℝ) * ‖c.1‖
      rw [hz, mul_zero]
      positivity
    · have hp : 0 < ‖q.1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      apply (mul_le_mul_right₀ hp).mp
      nlinarith only [hsquared]

/-- A rational certificate for the inhomogeneous block inequalities.
It gives a conservative bound without spectral theory. -/
theorem plateauResidual_scalar_bound (u v s : ℝ)
    (hcentral : u / 24 ≤ s + v / 4)
    (hexterior : 2 * v ≤ s + u / 4) : u + v ≤ 122 * s := by
  linarith

theorem plateauResidual_norm_lower_on_old_domain (C : ℝ) (hC : 1 ≤ C)
    (hheight : canonicalPlateauHeight ≤ C) (x : infiniteOnsiteDomain potential)
    (ha : inner ℝ x.1 compactA = 0) (hb : inner ℝ x.1 compactB = 0) :
    ‖x.1‖ ≤ 122 * ‖plateauResidual C hC x.1‖ := by
  obtain ⟨hc, hq⟩ := plateauResidual_block_bounds C hC hheight x ha hb
  have hs := plateauResidual_scalar_bound ‖(centralDomainPart x).1‖
    ‖(exteriorDomainPart x).1‖ ‖plateauResidual C hC x.1‖
    (by linarith only [hc]) (by linarith only [hq])
  have hsum : x.1 = (centralDomainPart x).1 + (exteriorDomainPart x).1 := by
    change x.1 = (centralDomainPart x).1 + (x.1 - (centralDomainPart x).1)
    abel
  calc
    ‖x.1‖ ≤ ‖(centralDomainPart x).1‖ + ‖(exteriorDomainPart x).1‖ := by
      rw [hsum]
      exact norm_add_le _ _
    _ ≤ _ := hs

end
end SpectralGeometry.AmmannBeenker
