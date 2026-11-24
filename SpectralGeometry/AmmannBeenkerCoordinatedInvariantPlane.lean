module

public import SpectralGeometry.AmmannBeenkerCoordinatedRingControl
public import SpectralGeometry.AmmannBeenkerQubitLeakage

public section

/-!
# Exact coordinated control on the original crossing plane (L7a/L7b)

The full-space edge action is evaluated before restricting to the two-mode
coordinates. All Hamiltonian statements use the original natural domain.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped BigOperators Classical

private theorem coordinatedRing_vector_lattice (i : Fin 8) :
    infiniteEdgeVector (firstRingVertex i) (secondRingVertex i) =
      latticeSingle (firstRingVertex i).val -
        latticeSingle (secondRingVertex i).val := by
  simp only [infiniteEdgeVector, latticeSingle_val]

/-- Exact full-space action, not an identity for a compressed matrix. -/
theorem coordinatedRingControl_compactA :
    coordinatedRingControl compactA = compactA - compactB := by
  have ha (k : Fin 17) :
      compactA (centralVertex k) = centralCompactCoordinates 1 0 k :=
    congrFun compactA_centralCoordinates k
  simp only [coordinatedRingControl_apply, coordinatedRingEdge_apply,
    coordinatedRing_vector_lattice, firstRingVertex, secondRingVertex,
    centralVertex_val, ha, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [centralCompactCoordinates, centralLift, compactA, compactB] <;> module

theorem coordinatedRingControl_compactB :
    coordinatedRingControl compactB = compactB - compactA := by
  have hb (k : Fin 17) :
      compactB (centralVertex k) = centralCompactCoordinates 0 1 k :=
    congrFun compactB_centralCoordinates k
  simp only [coordinatedRingControl_apply, coordinatedRingEdge_apply,
    coordinatedRing_vector_lattice, firstRingVertex, secondRingVertex,
    centralVertex_val, hb, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [centralCompactCoordinates, centralLift, compactA, compactB] <;> module

theorem coordinatedRingControl_bright :
    coordinatedRingControl crossingBright = (2 : ℝ) • crossingBright := by
  simp only [crossingBright, map_smul, map_sub,
    coordinatedRingControl_compactA, coordinatedRingControl_compactB]
  module

theorem coordinatedRingControl_pair (r s : ℝ) :
    coordinatedRingControl (r • compactA + s • compactB) =
      (r - s) • compactA + (s - r) • compactB := by
  simp only [map_add, map_smul, coordinatedRingControl_compactA,
    coordinatedRingControl_compactB]
  module

/-- Q M P = 0 for the existing full-space orthogonal decomposition. -/
theorem coordinatedRingControl_offplane_zero (x : TileHilbert Vertex) :
    crossingLeakage (coordinatedRingControl (crossingQubitPart x)) = 0 := by
  rw [crossingQubitPart, coordinatedRingControl_pair]
  exact crossingLeakage_pair_zero _ _

/-- The two-control Hamiltonian preserves the original compact plane at
arbitrary real control strengths; the input lies in the natural domain. -/
theorem coordinatedControls_compact_action (δ η r s : ℝ) :
    onsitePlusBounded potential
      (ringInteraction (crossingParameter + δ) + η • coordinatedRingControl)
      (r • domainCompactA + s • domainCompactB) =
      ((crossingEnergy + δ + η) * r - η * s) • compactA +
      ((crossingEnergy + η) * s - η * r) • compactB := by
  have hdet := detuning_two_mode_action δ r s
  rw [onsitePlusBounded_apply] at hdet ⊢
  change infiniteOnsiteOperator potential
      (r • domainCompactA + s • domainCompactB) +
        ringInteraction (crossingParameter + δ)
          (r • compactA + s • compactB) = _ at hdet
  change infiniteOnsiteOperator potential
      (r • domainCompactA + s • domainCompactB) +
        (ringInteraction (crossingParameter + δ)
          (r • compactA + s • compactB) +
         η • coordinatedRingControl (r • compactA + s • compactB)) = _
  rw [← add_assoc, hdet, coordinatedRingControl_pair]
  module

theorem coordinatedControls_offplane_zero (δ η r s : ℝ) :
    crossingLeakage
      (onsitePlusBounded potential
        (ringInteraction (crossingParameter + δ) + η • coordinatedRingControl)
        (r • domainCompactA + s • domainCompactB)) = 0 := by
  rw [coordinatedControls_compact_action]
  exact crossingLeakage_pair_zero _ _

/-- Explicit natural-domain lift of the output. -/
theorem coordinatedControls_domain_invariant (δ η r s : ℝ) :
    onsitePlusBounded potential
      (ringInteraction (crossingParameter + δ) + η • coordinatedRingControl)
      (r • domainCompactA + s • domainCompactB) ∈
        infiniteOnsiteDomain potential := by
  rw [coordinatedControls_compact_action]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ compactA_mem_domain)
    (Submodule.smul_mem _ _ compactB_mem_domain)

/-- Exact restriction in the normalized dark/bright basis. The matrix
is [[E+δ/2, δ/2], [δ/2, E+δ/2+2η]], with no exterior term. -/
theorem coordinatedControls_dark_bright_action (δ η u v : ℝ) :
    onsitePlusBounded potential
      (ringInteraction (crossingParameter + δ) + η • coordinatedRingControl)
      (u • domainCrossingDark + v • domainCrossingBright) =
      ((crossingEnergy + δ / 2) * u + δ / 2 * v) • crossingDark +
      (δ / 2 * u + (crossingEnergy + δ / 2 + 2 * η) * v) • crossingBright := by
  have hinput :
      u • domainCrossingDark + v • domainCrossingBright =
        ((u + v) / 4) • domainCompactA +
        ((u - v) / 4) • domainCompactB := by
    simp only [domainCrossingDark, domainCrossingBright]
    module
  rw [hinput, coordinatedControls_compact_action]
  simp only [crossingDark, crossingBright]
  module

end
end SpectralGeometry.AmmannBeenker
