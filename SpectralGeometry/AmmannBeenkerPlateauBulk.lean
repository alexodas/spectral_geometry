module

public import SpectralGeometry.AmmannBeenkerPlateauSpectrum

public section

/-!
# Uniform bulk, finite-rank defect and isolated double eigenvalue

The uniform reference operator is C I + interaction on the same full
infinite graph. Its real spectrum is enclosed in [C,C+1], without a
claim that it fills that interval. At the canonical plateau height
the actual Hamiltonian differs from this reference by a defect whose
range is supported within the prescribed central sector (at most
seventeen dimensions). The final theorem combines the certified
crossing properties with these bulk and finite-rank conclusions.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

@[expose] def plateauBulk (C : ℝ) : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  C • ContinuousLinearMap.id ℝ (TileHilbert Vertex) + interaction

theorem plateauBulk_isSelfAdjoint (C : ℝ) : IsSelfAdjoint (plateauBulk C) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℝ (C • x + interaction x) y = inner ℝ x (C • y + interaction y)
  rw [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    interaction_symmetric]

theorem plateauBulk_form_bounds (C : ℝ) (x : TileHilbert Vertex) :
    C * ‖x‖ ^ 2 ≤ inner ℝ x (plateauBulk C x) ∧
      inner ℝ x (plateauBulk C x) ≤ (C + 1) * ‖x‖ ^ 2 := by
  have hnorm : ‖interaction x‖ ≤ ‖x‖ := by
    calc
      _ ≤ ‖interaction‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right interaction_norm_le (norm_nonneg _)
      _ = _ := one_mul _
  have hupper : inner ℝ x (interaction x) ≤ ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖x‖ * ‖interaction x‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ = _ := by ring
  change C * ‖x‖ ^ 2 ≤ inner ℝ x (C • x + interaction x) ∧
    inner ℝ x (C • x + interaction x) ≤ (C + 1) * ‖x‖ ^ 2
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  constructor <;> nlinarith only [interaction_nonneg x, hupper]

/-- Full bounded-inverse spectral enclosure of the uniform bulk. -/
theorem plateauBulk_realSpectrum_subset (C : ℝ) :
    spectrum ℝ (plateauBulk C) ⊆ Set.Icc C (C + 1) := by
  intro energy hs
  by_contra hn
  have hout : energy < C ∨ C + 1 < energy := by
    change ¬ (C ≤ energy ∧ energy ≤ C + 1) at hn
    push Not at hn
    exact hn
  let T : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
    plateauBulk C - energy • (1 : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
  have hT : IsSelfAdjoint T := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    have hb := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (plateauBulk_isSelfAdjoint C)) x y
    change inner ℝ (plateauBulk C x - energy • x) y =
      inner ℝ x (plateauBulk C y - energy • y)
    rw [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hb]
  let d : ℝ := max (C - energy) (energy - (C + 1))
  have hd : 0 < d := by
    rcases hout with hl | hr
    · exact lt_of_lt_of_le (sub_pos.mpr hl) (le_max_left _ _)
    · exact lt_of_lt_of_le (sub_pos.mpr hr) (le_max_right _ _)
  have hbound (x : TileHilbert Vertex) : ‖x‖ ≤ (1 / d) * ‖T x‖ := by
    obtain ⟨hl, hu⟩ := plateauBulk_form_bounds C x
    have hform : inner ℝ x (T x) =
        inner ℝ x (plateauBulk C x) - energy * ‖x‖ ^ 2 := by
      change inner ℝ x (plateauBulk C x - energy • x) = _
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have hpos : d * ‖x‖ ^ 2 ≤ ‖x‖ * ‖T x‖ := by
      rcases hout with hbelow | habove
      · have hde : d = C - energy := by
          dsimp [d]
          apply max_eq_left
          linarith
        have hcs := real_inner_le_norm x (T x)
        rw [hform] at hcs
        rw [hde]
        nlinarith only [hl, hcs]
      · have hde : d = energy - (C + 1) := by
          dsimp [d]
          apply max_eq_right
          linarith
        have hcs := real_inner_le_norm x (-(T x))
        rw [inner_neg_right, hform, norm_neg] at hcs
        rw [hde]
        nlinarith only [hu, hcs]
    have hc : d * ‖x‖ ≤ ‖T x‖ := by
      by_cases hz : ‖x‖ = 0
      · rw [hz, mul_zero]
        exact norm_nonneg _
      · have hp : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
        by_contra hh
        have hh' := mul_lt_mul_of_pos_right (lt_of_not_ge hh) hp
        nlinarith only [hpos, hh']
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).mpr
    nlinarith only [hc]
  have hu := boundedSelfAdjoint_isUnit_of_norm_lower T hT (1 / d) (by positivity) hbound
  have hnot : energy ∉ spectrum ℝ (plateauBulk C) := by
    apply spectrum.notMem_iff.mpr
    rw [Algebra.algebraMap_eq_smul_one, ← neg_sub]
    exact hu.neg
  exact hnot hs

@[expose] def canonicalPlateauHamiltonian : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  plateauHamiltonian canonicalPlateauHeight
    (le_trans (by norm_num : (1 : ℝ) ≤ 5) canonicalPlateauHeight_ge_five)

@[expose] def canonicalPlateauDefect : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  canonicalPlateauHamiltonian - plateauBulk canonicalPlateauHeight

/-- The bulk hopping cancels exactly; the remaining difference
vanishes on every exterior coordinate, for every input state. -/
theorem canonicalPlateauDefect_zero_outside (x : TileHilbert Vertex)
    (v : Vertex) (hv : v ∉ sector) :
    canonicalPlateauDefect x v = 0 := by
  have hn : v ∉ neighbors origin := by
    intro h
    exact hv (origin_neighbors_mem_sector ((mem_neighbors_iff origin v).mp h))
  change (plateauOnsite canonicalPlateauHeight
      (le_trans (by norm_num : (1 : ℝ) ≤ 5) canonicalPlateauHeight_ge_five) x v +
      (interaction x v + crossingParameter * finiteSectorProjection (neighbors origin) x v)) -
      (canonicalPlateauHeight * x v + interaction x v) = 0
  rw [plateauOnsite_apply, canonicalPlateauPotential_outside v hv,
    finiteSectorProjection_apply, if_neg hn]
  ring

/-- Restriction to the finite central coordinate set is injective on
the range of the canonical defect. -/
@[expose] def canonicalPlateauDefectRestriction :
    canonicalPlateauDefect.toLinearMap.range →ₗ[ℝ] (sector → ℝ) where
  toFun x v := x.1 v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem canonicalPlateauDefectRestriction_injective :
    Function.Injective canonicalPlateauDefectRestriction := by
  intro x y h
  obtain ⟨u, hu⟩ := x.property
  obtain ⟨w, hw⟩ := y.property
  apply Subtype.ext
  apply lp.ext
  funext v
  by_cases hv : v ∈ sector
  · exact congrFun h ⟨v, hv⟩
  · have hx : x.1 v = 0 := by
      rw [← hu]
      exact canonicalPlateauDefect_zero_outside u v hv
    have hy : y.1 v = 0 := by
      rw [← hw]
      exact canonicalPlateauDefect_zero_outside w v hv
    rw [hx, hy]

theorem canonicalPlateauDefect_finiteDimensional :
    FiniteDimensional ℝ canonicalPlateauDefect.toLinearMap.range :=
  FiniteDimensional.of_injective canonicalPlateauDefectRestriction
    canonicalPlateauDefectRestriction_injective

theorem canonicalPlateauDefect_finrank_le :
    Module.finrank ℝ canonicalPlateauDefect.toLinearMap.range ≤ 17 := by
  have h := LinearMap.finrank_le_finrank_of_injective
    canonicalPlateauDefectRestriction_injective
  simpa [sector_card] using h

theorem canonicalPlateau_energy_below_bulk :
    crossingEnergy < canonicalPlateauHeight := by
  unfold crossingEnergy canonicalPlateauHeight
  linarith [alpha_bounds.1]

/-- The central compact pair, the full real spectral gap, and the
finite-rank realization relative to the uniform bulk, in one result.
No assumption of discrete spectrum and no compact-resolvent argument. -/
theorem canonicalPlateau_isolated_double_eigenvalue :
    IsSelfAdjoint canonicalPlateauHamiltonian ∧
    LinearIndependent ℝ ![compactA, compactB] ∧
    canonicalPlateauHamiltonian compactA = crossingEnergy • compactA ∧
    canonicalPlateauHamiltonian compactB = crossingEnergy • compactB ∧
    Module.finrank ℝ
      (Module.End.eigenspace canonicalPlateauHamiltonian.toLinearMap crossingEnergy) = 2 ∧
    (∀ energy ∈ spectrum ℝ canonicalPlateauHamiltonian,
      energy ≠ crossingEnergy → (1 / 122 : ℝ) ≤ |energy - crossingEnergy|) ∧
    crossingEnergy < canonicalPlateauHeight ∧
    spectrum ℝ (plateauBulk canonicalPlateauHeight) ⊆
      Set.Icc canonicalPlateauHeight (canonicalPlateauHeight + 1) ∧
    FiniteDimensional ℝ canonicalPlateauDefect.toLinearMap.range ∧
    Module.finrank ℝ canonicalPlateauDefect.toLinearMap.range ≤ 17 := by
  obtain ⟨hi, ha, hb⟩ := canonicalPlateau_compact_crossing
  refine ⟨plateauHamiltonian_isSelfAdjoint _ _, hi, ha, hb,
    plateauCrossingEigenspace_finrank _ _ le_rfl,
    ?_, canonicalPlateau_energy_below_bulk, plateauBulk_realSpectrum_subset _,
    canonicalPlateauDefect_finiteDimensional, canonicalPlateauDefect_finrank_le⟩
  intro energy hs hne
  exact plateauHamiltonian_realSpectrum_gap _ _ le_rfl energy hs hne

end
end SpectralGeometry.AmmannBeenker
