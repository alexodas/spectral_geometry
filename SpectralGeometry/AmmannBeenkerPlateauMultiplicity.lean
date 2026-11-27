module

public import SpectralGeometry.AmmannBeenkerPlateauResidual

public section

/-!
# Full-space plateau residual bound and exact crossing multiplicity

The old natural domain is dense in the entire real Hilbert space.
Its compact-mode projection remains in that domain. Applying the
certified residual estimate to the orthogonal remainder and using
continuity extends the estimate to every square-summable state.

As a consequence, every plateau crossing eigenvector lies in the
original compact plane. This proves exact geometric multiplicity two.
Bounded invertibility on the complement and full spectral isolation
are separate obligations.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- The existing compact-mode projection, packaged as a bounded map
using the two orthogonal rank-one operators. -/
@[expose] def plateauQubitProjection : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  (1 / 8 : ℝ) • InnerProductSpace.rankOne ℝ compactA compactA +
  (1 / 8 : ℝ) • InnerProductSpace.rankOne ℝ compactB compactB

theorem plateauQubitProjection_apply (x : TileHilbert Vertex) :
    plateauQubitProjection x = crossingQubitPart x := by
  simp only [plateauQubitProjection, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply,
    crossingQubitPart, crossingCoeffA, crossingCoeffB, smul_smul]
  module

@[expose] def plateauLeakageCLM : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  ContinuousLinearMap.id ℝ (TileHilbert Vertex) - plateauQubitProjection

theorem plateauLeakageCLM_apply (x : TileHilbert Vertex) :
    plateauLeakageCLM x = crossingLeakage x := by
  change x - plateauQubitProjection x = crossingLeakage x
  rw [plateauQubitProjection_apply, crossingLeakage]

/-- Subtracting the compact projection preserves the old natural
domain, since both compact modes already belong to it. -/
theorem plateauLeakage_mem_old_domain (x : infiniteOnsiteDomain potential) :
    crossingLeakage x.1 ∈ infiniteOnsiteDomain potential := by
  unfold crossingLeakage crossingQubitPart
  apply Submodule.sub_mem _ x.property
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ domainCompactA.property
  · exact Submodule.smul_mem _ _ domainCompactB.property

theorem plateauResidual_qubitPart_zero (C : ℝ) (hC : 1 ≤ C)
    (hfive : 5 ≤ C) (x : TileHilbert Vertex) :
    plateauResidual C hC (crossingQubitPart x) = 0 := by
  change plateauHamiltonian C hC (crossingQubitPart x) -
    crossingEnergy • crossingQubitPart x = 0
  unfold crossingQubitPart
  rw [plateauHamiltonian_pair_action C hC hfive, sub_self]

theorem plateauResidual_leakage_eq (C : ℝ) (hC : 1 ≤ C)
    (hfive : 5 ≤ C) (x : TileHilbert Vertex) :
    plateauResidual C hC (crossingLeakage x) = plateauResidual C hC x := by
  unfold crossingLeakage
  rw [map_sub, plateauResidual_qubitPart_zero C hC hfive, sub_zero]

/-- On the dense old domain, the residual bounds the leakage of
every state, without an orthogonality hypothesis on that state. -/
theorem plateauResidual_leakage_bound_on_old_domain (C : ℝ) (hC : 1 ≤ C)
    (hheight : canonicalPlateauHeight ≤ C) (x : infiniteOnsiteDomain potential) :
    ‖crossingLeakage x.1‖ ≤ 122 * ‖plateauResidual C hC x.1‖ := by
  let y : infiniteOnsiteDomain potential :=
    ⟨crossingLeakage x.1, plateauLeakage_mem_old_domain x⟩
  have ha : inner ℝ y.1 compactA = 0 := by
    change inner ℝ (crossingLeakage x.1) compactA = 0
    rw [real_inner_comm, crossingLeakage_inner_compactA]
  have hb : inner ℝ y.1 compactB = 0 := by
    change inner ℝ (crossingLeakage x.1) compactB = 0
    rw [real_inner_comm, crossingLeakage_inner_compactB]
  have h := plateauResidual_norm_lower_on_old_domain C hC hheight y ha hb
  change ‖crossingLeakage x.1‖ ≤
    122 * ‖plateauResidual C hC (crossingLeakage x.1)‖ at h
  rw [plateauResidual_leakage_eq C hC (canonicalPlateauHeight_ge_five.trans hheight)] at h
  exact h

/-- The quantitative bound holds for all real Hilbert states, even
those outside the old unbounded potential's natural domain. -/
theorem plateauResidual_leakage_bound (C : ℝ) (hC : 1 ≤ C)
    (hheight : canonicalPlateauHeight ≤ C) (x : TileHilbert Vertex) :
    ‖crossingLeakage x‖ ≤ 122 * ‖plateauResidual C hC x‖ := by
  let S : Set (TileHilbert Vertex) :=
    {z | ‖plateauLeakageCLM z‖ ≤ 122 * ‖plateauResidual C hC z‖}
  have hc : IsClosed S :=
    isClosed_le plateauLeakageCLM.continuous.norm
      (continuous_const.mul (plateauResidual C hC).continuous.norm)
  have hs : (infiniteOnsiteDomain potential : Set (TileHilbert Vertex)) ⊆ S := by
    intro z hz
    change ‖plateauLeakageCLM z‖ ≤ 122 * ‖plateauResidual C hC z‖
    rw [plateauLeakageCLM_apply]
    exact plateauResidual_leakage_bound_on_old_domain C hC hheight ⟨z, hz⟩
  have hclosure := closure_minimal hs hc
  rw [(infiniteOnsiteDomain_dense potential).closure_eq] at hclosure
  have hx : x ∈ S := hclosure (Set.mem_univ x)
  change ‖plateauLeakageCLM x‖ ≤ 122 * ‖plateauResidual C hC x‖ at hx
  rwa [plateauLeakageCLM_apply] at hx

/-- Uniform coercivity on the full orthogonal complement. -/
theorem plateauResidual_norm_lower (C : ℝ) (hC : 1 ≤ C)
    (hheight : canonicalPlateauHeight ≤ C) (x : TileHilbert Vertex)
    (ha : inner ℝ compactA x = 0) (hb : inner ℝ compactB x = 0) :
    (1 / 122 : ℝ) * ‖x‖ ≤ ‖plateauResidual C hC x‖ := by
  have h := plateauResidual_leakage_bound C hC hheight x
  have hz : crossingLeakage x = x := by
    simp [crossingLeakage, crossingQubitPart, crossingCoeffA, crossingCoeffB, ha, hb]
  rw [hz] at h
  linarith only [h]

/-- Every full-space crossing eigenvector belongs to the original
compact plane; no extra kernel vectors survive the truncation. -/
theorem plateau_crossing_eigenvector_representation (C : ℝ) (hC : 1 ≤ C)
    (hheight : canonicalPlateauHeight ≤ C) (x : TileHilbert Vertex)
    (hx : plateauHamiltonian C hC x = crossingEnergy • x) :
    x = crossingCoeffA x • compactA + crossingCoeffB x • compactB := by
  have hz : plateauResidual C hC x = 0 := by
    change plateauHamiltonian C hC x - crossingEnergy • x = 0
    rw [hx, sub_self]
  have h := plateauResidual_leakage_bound C hC hheight x
  rw [hz, norm_zero, mul_zero] at h
  have hl : crossingLeakage x = 0 :=
    norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  exact (crossingLeakage_eq_zero_iff x).mp hl

/-- Exact eigenspace of the bounded Hamiltonian, on the full Hilbert
space rather than a domain submodule. -/
@[expose] def plateauCrossingEigenspace (C : ℝ) (hC : 1 ≤ C) :
    Submodule ℝ (TileHilbert Vertex) :=
  Module.End.eigenspace (plateauHamiltonian C hC).toLinearMap crossingEnergy

theorem mem_plateauCrossingEigenspace (C : ℝ) (hC : 1 ≤ C)
    (x : TileHilbert Vertex) :
    x ∈ plateauCrossingEigenspace C hC ↔
      plateauHamiltonian C hC x = crossingEnergy • x :=
  Module.End.mem_eigenspace_iff

/-- Compact-mode coefficients are exact linear coordinates of the
entire eigenspace of the bounded operator. -/
@[expose] def plateauCrossingEigenspaceCoordinates (C : ℝ) (hC : 1 ≤ C)
    (hheight : canonicalPlateauHeight ≤ C) :
    plateauCrossingEigenspace C hC ≃ₗ[ℝ] (ℝ × ℝ) := by
  let f : plateauCrossingEigenspace C hC →ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun x => (crossingCoeffA x.1, crossingCoeffB x.1)
      map_add' := by
        intro x y
        change (crossingCoeffA (x.1 + y.1), crossingCoeffB (x.1 + y.1)) =
          (crossingCoeffA x.1 + crossingCoeffA y.1,
            crossingCoeffB x.1 + crossingCoeffB y.1)
        rw [crossingCoeffA_add, crossingCoeffB_add]
      map_smul' := by
        intro r x
        change (crossingCoeffA (r • x.1), crossingCoeffB (r • x.1)) =
          (r * crossingCoeffA x.1, r * crossingCoeffB x.1)
        rw [crossingCoeffA_smul, crossingCoeffB_smul] }
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    have hx := plateau_crossing_eigenvector_representation C hC hheight x.1
      ((mem_plateauCrossingEigenspace C hC x.1).mp x.property)
    have hy := plateau_crossing_eigenvector_representation C hC hheight y.1
      ((mem_plateauCrossingEigenspace C hC y.1).mp y.property)
    have ha : crossingCoeffA x.1 = crossingCoeffA y.1 := congrArg Prod.fst h
    have hb : crossingCoeffB x.1 = crossingCoeffB y.1 := congrArg Prod.snd h
    apply Subtype.ext
    calc
      x.1 = crossingCoeffA x.1 • compactA + crossingCoeffB x.1 • compactB := hx
      _ = crossingCoeffA y.1 • compactA + crossingCoeffB y.1 • compactB := by rw [ha, hb]
      _ = y.1 := hy.symm
  · rintro ⟨a, b⟩
    let z := a • compactA + b • compactB
    have hz : z ∈ plateauCrossingEigenspace C hC :=
      (mem_plateauCrossingEigenspace C hC z).mpr
        (plateauHamiltonian_pair_action C hC
          (canonicalPlateauHeight_ge_five.trans hheight) a b)
    refine ⟨⟨z, hz⟩, ?_⟩
    change (crossingCoeffA z, crossingCoeffB z) = (a, b)
    simp only [z, crossingCoeffA_pair, crossingCoeffB_pair]

/-- Exact geometric multiplicity two on the full infinite graph. -/
theorem plateauCrossingEigenspace_finrank (C : ℝ) (hC : 1 ≤ C)
    (hheight : canonicalPlateauHeight ≤ C) :
    Module.finrank ℝ (plateauCrossingEigenspace C hC) = 2 := by
  calc
    _ = Module.finrank ℝ (ℝ × ℝ) :=
      (plateauCrossingEigenspaceCoordinates C hC hheight).finrank_eq
    _ = 2 := by simp

end
end SpectralGeometry.AmmannBeenker
