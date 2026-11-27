module

public import SpectralGeometry.AmmannBeenkerPlateauOperator

public section

/-!
# Exact compact crossing for the bounded plateau model

The original and truncated onsite potentials coincide on the entire
central sector for C >= 5. Hence their full infinite-graph Hamiltonian
actions agree on every state supported there. In particular both
original compact modes survive, with their original common energy
and linear independence. Exact multiplicity and spectral isolation
remain separate obligations.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- Equality of the full onsite action on states supported in the
central sector. The original natural domain is retained on the right. -/
theorem plateauOnsite_eq_original_on_supported (C : ℝ) (hC : 1 ≤ C)
    (hfive : 5 ≤ C) (x : infiniteOnsiteDomain potential)
    (hx : ∀ v : Vertex, v ∉ sector → x.1 v = 0) :
    plateauOnsite C hC x.1 = infiniteOnsiteOperator potential x := by
  apply lp.ext
  funext v
  rw [plateauOnsite_apply, infiniteOnsiteOperator_apply]
  by_cases hv : v ∈ sector
  · rw [plateauPotential_eq_on_sector C hfive v hv]
  · rw [hx v hv, mul_zero, mul_zero]

/-- Full graph equality, including the unchanged interaction and
fixed crossing correction, not merely the central compression. -/
theorem plateauHamiltonian_eq_original_on_supported (C : ℝ) (hC : 1 ≤ C)
    (hfive : 5 ≤ C) (x : infiniteOnsiteDomain potential)
    (hx : ∀ v : Vertex, v ∉ sector → x.1 v = 0) :
    plateauHamiltonian C hC x.1 =
      onsitePlusBounded potential (ringInteraction crossingParameter) x := by
  change plateauOnsite C hC x.1 + ringInteraction crossingParameter x.1 = _
  rw [onsitePlusBounded_apply, plateauOnsite_eq_original_on_supported C hC hfive x hx]

theorem compactA_zero_outside_sector (v : Vertex) (hv : v ∉ sector) :
    compactA v = 0 := by
  by_contra hn
  obtain ⟨i, hi⟩ := compactA_support hn
  rw [hi] at hv
  exact hv (firstRing_mem_sector i)

theorem compactB_zero_outside_sector (v : Vertex) (hv : v ∉ sector) :
    compactB v = 0 := by
  by_contra hn
  obtain ⟨i, hi⟩ := compactB_support hn
  rw [hi] at hv
  exact hv (secondRing_mem_sector i)

theorem plateauHamiltonian_compactA (C : ℝ) (hC : 1 ≤ C)
    (hfive : 5 ≤ C) :
    plateauHamiltonian C hC compactA = crossingEnergy • compactA := by
  have he := plateauHamiltonian_eq_original_on_supported C hC hfive
    domainCompactA compactA_zero_outside_sector
  exact he.trans compact_crossing.2.1

theorem plateauHamiltonian_compactB (C : ℝ) (hC : 1 ≤ C)
    (hfive : 5 ≤ C) :
    plateauHamiltonian C hC compactB = crossingEnergy • compactB := by
  have he := plateauHamiltonian_eq_original_on_supported C hC hfive
    domainCompactB compactB_zero_outside_sector
  exact he.trans compact_crossing.2.2

/-- Two independent exact eigenvectors at the original energy.
This does not assert that the eigenspace has dimension exactly two. -/
theorem plateauHamiltonian_compact_crossing (C : ℝ) (hC : 1 ≤ C)
    (hfive : 5 ≤ C) :
    LinearIndependent ℝ ![compactA, compactB] ∧
      plateauHamiltonian C hC compactA = crossingEnergy • compactA ∧
      plateauHamiltonian C hC compactB = crossingEnergy • compactB :=
  ⟨compact_pair_linearIndependent, plateauHamiltonian_compactA C hC hfive,
    plateauHamiltonian_compactB C hC hfive⟩

/-- The entire original two-mode plane is an eigenspace subspace. -/
theorem plateauHamiltonian_pair_action (C : ℝ) (hC : 1 ≤ C)
    (hfive : 5 ≤ C) (r s : ℝ) :
    plateauHamiltonian C hC (r • compactA + s • compactB) =
      crossingEnergy • (r • compactA + s • compactB) := by
  rw [map_add, map_smul, map_smul,
    plateauHamiltonian_compactA C hC hfive,
    plateauHamiltonian_compactB C hC hfive]
  module

/-- The canonical plateau preserves both original compact eigenvectors. -/
theorem canonicalPlateau_compact_crossing :
    LinearIndependent ℝ ![compactA, compactB] ∧
      plateauHamiltonian canonicalPlateauHeight
        (le_trans (by norm_num : (1 : ℝ) ≤ 5) canonicalPlateauHeight_ge_five)
        compactA = crossingEnergy • compactA ∧
      plateauHamiltonian canonicalPlateauHeight
        (le_trans (by norm_num : (1 : ℝ) ≤ 5) canonicalPlateauHeight_ge_five)
        compactB = crossingEnergy • compactB :=
  plateauHamiltonian_compact_crossing _ _ canonicalPlateauHeight_ge_five

end
end SpectralGeometry.AmmannBeenker
