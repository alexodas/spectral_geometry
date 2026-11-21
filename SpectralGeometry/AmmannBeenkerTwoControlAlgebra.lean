module

public import SpectralGeometry.AmmannBeenkerEdgeControl

public section

/-!
# Exact response of the compact crossing to the two available controls

Changing the eight-site parameter produces an *exact* diagonal energy
response in the compact-mode basis. Changing the single connecting edge
introduces off-diagonal matrix elements and leaves the normalized dark
state fixed. These identities hold for the complete infinite operator
on its natural domain; no two-level dynamical approximation is assumed.

Time-dependent Schrödinger evolution and quantitative leakage estimates
are separate, still-open tasks.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- Detuning the eight-site control shifts the first compact eigenvalue
by exactly the detuning, without changing that eigenvector. -/
theorem ring_compactA_detuning (δ : ℝ) :
    onsitePlusBounded potential (ringInteraction (crossingParameter + δ))
      domainCompactA = (crossingEnergy + δ) • compactA := by
  rw [ring_compactA]
  congr 1
  dsimp [crossingParameter, crossingEnergy]
  ring

/-- The second compact eigenvalue remains fixed under detuning. -/
theorem ring_compactB_detuning (δ : ℝ) :
    onsitePlusBounded potential (ringInteraction (crossingParameter + δ))
      domainCompactB = crossingEnergy • compactB :=
  ring_compactB _

/-- Every detuning preserves the entire two-dimensional span of the
compact eigenvectors. This uses the exact infinite-domain equations,
not an effective two-level approximation. -/
theorem detuning_two_mode_action (δ r s : ℝ) :
    onsitePlusBounded potential (ringInteraction (crossingParameter + δ))
      (r • domainCompactA + s • domainCompactB) =
        (crossingEnergy + δ) • (r • compactA) +
          crossingEnergy • (s • compactB) := by
  simp only [map_add, map_smul, ring_compactA_detuning, ring_compactB_detuning]
  module

/-- Although edge control alone leaves the dark vector stationary, an
eight-site detuning changes its direction within the compact plane.
The result is an exact equation for the infinite natural-domain operator. -/
theorem crossingDark_detuning_response (δ : ℝ) :
    onsitePlusBounded potential (ringInteraction (crossingParameter + δ))
      domainCrossingDark =
      crossingEnergy • crossingDark +
        δ • ((1 / 4 : ℝ) • compactA) := by
  simp only [domainCrossingDark, map_smul, map_add,
    ring_compactA_detuning, ring_compactB_detuning, crossingDark]
  module

/-- Even when both controls are used, the connecting edge has no direct
action on the dark vector. Its nonstationarity comes entirely from
detuning the eight-site parameter. -/
theorem crossingDark_two_control_response (δ ε : ℝ) :
    onsitePlusBounded potential
      (ringInteraction (crossingParameter + δ) + ε • crossingEdge)
      domainCrossingDark =
      crossingEnergy • crossingDark +
        δ • ((1 / 4 : ℝ) • compactA) := by
  have h := crossingDark_detuning_response δ
  rw [onsitePlusBounded_apply] at h ⊢
  change infiniteOnsiteOperator potential domainCrossingDark +
    (ringInteraction (crossingParameter + δ) crossingDark +
      ε • crossingEdge crossingDark) = _ 
  rw [crossingEdge_dark_zero, smul_zero, add_zero]
  exact h

end
end SpectralGeometry.AmmannBeenker
