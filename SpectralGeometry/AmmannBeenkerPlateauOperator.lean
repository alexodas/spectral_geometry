module

public import SpectralGeometry.AmmannBeenkerCrossingMultiplicity
public import SpectralGeometry.InfiniteLocalResolventSpectrum

public section

/-!
# Bounded plateau Hamiltonian on the full infinite graph

L9.1: truncate the onsite potential at a height C >= 1, keeping the
original crossing correction. The canonical height is the previously
certified sharp exterior barrier. No spectral isolation is asserted.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- C = 1 + R² gives the radial plateau of radius R >= 0. -/
@[expose] def plateauPotential (C : ℝ) (v : Vertex) : ℝ :=
  min (potential v) C

theorem plateauPotential_bounds (C : ℝ) (hC : 1 ≤ C) (v : Vertex) :
    1 ≤ plateauPotential C v ∧ plateauPotential C v ≤ C :=
  ⟨le_min (potential_lower v) hC, min_le_right _ _⟩

theorem plateauPotential_eq_on_sector (C : ℝ) (hC : 5 ≤ C)
    (v : Vertex) (hv : v ∈ sector) :
    plateauPotential C v = potential v := by
  have hr := (mem_sector v).mp hv
  have hn := norm_nonneg (position v)
  have hs : ‖position v‖ ^ 2 ≤ 4 := by nlinarith
  apply min_eq_left
  unfold potential
  linarith

@[expose] def canonicalPlateauHeight : ℝ := 4 + 4 * alpha

theorem canonicalPlateauHeight_ge_five : 5 ≤ canonicalPlateauHeight := by
  unfold canonicalPlateauHeight
  linarith [alpha_bounds.1]

theorem canonicalPlateauPotential_on_sector (v : Vertex) (hv : v ∈ sector) :
    plateauPotential canonicalPlateauHeight v = potential v :=
  plateauPotential_eq_on_sector _ canonicalPlateauHeight_ge_five v hv

theorem canonicalPlateauPotential_outside (v : Vertex) (hv : v ∉ sector) :
    plateauPotential canonicalPlateauHeight v = canonicalPlateauHeight :=
  min_eq_right (potential_outside_sector_sharp v hv)

theorem plateauPotential_normalized_norm_le (C : ℝ) (hC : 1 ≤ C)
    (v : Vertex) : ‖plateauPotential C v / C‖ ≤ 1 := by
  have hb := plateauPotential_bounds C hC v
  have hp : 0 < C := by linarith
  have hv : 0 ≤ plateauPotential C v := by linarith [hb.1]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hv hp.le)]
  exact (div_le_iff₀ hp).mpr (by simpa using hb.2)

/-- Scale the existing diagonal contraction on the same real Hilbert space. -/
@[expose] def plateauOnsite (C : ℝ) (hC : 1 ≤ C) :
    TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  C • infiniteOnsiteDiagonalContraction
    (fun v => plateauPotential C v / C)
    (plateauPotential_normalized_norm_le C hC)

@[simp] theorem plateauOnsite_apply (C : ℝ) (hC : 1 ≤ C)
    (x : TileHilbert Vertex) (v : Vertex) :
    plateauOnsite C hC x v = plateauPotential C v * x v := by
  have hn : C ≠ 0 := by linarith
  change C * (infiniteOnsiteDiagonalContraction
    (fun v => plateauPotential C v / C)
    (plateauPotential_normalized_norm_le C hC) x v) = _
  rw [infiniteOnsiteDiagonalContraction_apply]
  field_simp [hn]

theorem plateauPotential_domain_top (C : ℝ) (hC : 1 ≤ C) :
    infiniteOnsiteDomain (plateauPotential C) = ⊤ := by
  apply top_unique
  intro x _
  change Memℓp (fun v : Vertex => plateauPotential C v * x v) 2
  have he : (fun v : Vertex => plateauPotential C v * x v) =
      (fun v : Vertex => plateauOnsite C hC x v) := by
    funext v
    rw [plateauOnsite_apply]
  rw [he]
  exact (plateauOnsite C hC x).property

theorem plateauOnsite_norm_le (C : ℝ) (hC : 1 ≤ C) :
    ‖plateauOnsite C hC‖ ≤ C := by
  have hC0 : 0 ≤ C := by linarith
  apply ContinuousLinearMap.opNorm_le_bound _ hC0
  intro x
  calc
    ‖plateauOnsite C hC x‖ ≤ ‖C • x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro v
      rw [plateauOnsite_apply]
      change ‖plateauPotential C v * x v‖ ≤ ‖C * x v‖
      have hb := plateauPotential_bounds C hC v
      have hv : 0 ≤ plateauPotential C v := by linarith [hb.1]
      calc
        ‖plateauPotential C v * x v‖ = plateauPotential C v * ‖x v‖ := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hv]
        _ ≤ C * ‖x v‖ := mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)
        _ = ‖C * x v‖ := by rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hC0]
    _ = C * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC0]

theorem plateauOnsite_symmetric (C : ℝ) (hC : 1 ≤ C)
    (x y : TileHilbert Vertex) :
    inner ℝ (plateauOnsite C hC x) y = inner ℝ x (plateauOnsite C hC y) := by
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro v
  rw [plateauOnsite_apply, plateauOnsite_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

@[expose] def plateauHamiltonian (C : ℝ) (hC : 1 ≤ C) :
    TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  plateauOnsite C hC + ringInteraction crossingParameter

theorem plateauHamiltonian_norm_le (C : ℝ) (hC : 1 ≤ C) :
    ‖plateauHamiltonian C hC‖ ≤ C + 1 + |crossingParameter| := by
  unfold plateauHamiltonian ringInteraction
  calc
    ‖plateauOnsite C hC +
        (interaction + crossingParameter • finiteSectorProjection (neighbors origin))‖
      ≤ ‖plateauOnsite C hC‖ +
        ‖interaction + crossingParameter • finiteSectorProjection (neighbors origin)‖ :=
      norm_add_le _ _
    _ ≤ ‖plateauOnsite C hC‖ + (‖interaction‖ +
        ‖crossingParameter • finiteSectorProjection (neighbors origin)‖) :=
      add_le_add_left (norm_add_le _ _) _
    _ ≤ C + 1 + |crossingParameter| := by
      rw [norm_smul, Real.norm_eq_abs]
      have hh := mul_le_mul_of_nonneg_left
        (finiteSectorProjection_norm_le (neighbors origin)) (abs_nonneg crossingParameter)
      linarith [plateauOnsite_norm_le C hC, interaction_norm_le]

theorem plateauHamiltonian_symmetric (C : ℝ) (hC : 1 ≤ C)
    (x y : TileHilbert Vertex) :
    inner ℝ (plateauHamiltonian C hC x) y =
      inner ℝ x (plateauHamiltonian C hC y) := by
  change inner ℝ (plateauOnsite C hC x +
      (interaction x + crossingParameter • finiteSectorProjection (neighbors origin) x)) y =
    inner ℝ x (plateauOnsite C hC y +
      (interaction y + crossingParameter • finiteSectorProjection (neighbors origin) y))
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    plateauOnsite_symmetric C hC x y, interaction_symmetric x y,
    finiteSectorProjection_symmetric (neighbors origin) x y]

theorem plateauHamiltonian_isSelfAdjoint (C : ℝ) (hC : 1 ≤ C) :
    IsSelfAdjoint (plateauHamiltonian C hC) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  exact plateauHamiltonian_symmetric C hC x y

theorem plateauHamiltonian_agrees_natural (C : ℝ) (hC : 1 ≤ C)
    (x : infiniteOnsiteDomain (plateauPotential C)) :
    plateauHamiltonian C hC x.1 =
      onsitePlusBounded (plateauPotential C) (ringInteraction crossingParameter) x := by
  have he : plateauOnsite C hC x.1 = infiniteOnsiteOperator (plateauPotential C) x := by
    apply lp.ext
    funext v
    rw [plateauOnsite_apply, infiniteOnsiteOperator_apply]
  change plateauOnsite C hC x.1 + ringInteraction crossingParameter x.1 = _
  rw [onsitePlusBounded_apply, he]

end
end SpectralGeometry.AmmannBeenker
