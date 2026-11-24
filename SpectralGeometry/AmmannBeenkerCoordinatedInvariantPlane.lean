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

/-- Evaluate the finite sum before doing any vertex-case simplification. -/
private theorem coordinatedRing_sum_eval (s : Finset (Fin 8))
    (x : TileHilbert Vertex) (v : Vertex) :
    (∑ i ∈ s, coordinatedRingEdge i x) v =
      ∑ i ∈ s, (coordinatedRingEdge i x) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, lp.coeFn_add, Pi.add_apply, ih]

private theorem coordinatedRing_edge_eval (i : Fin 8)
    (x : TileHilbert Vertex) (v : Vertex) :
    (coordinatedRingEdge i x) v =
      (x (firstRingVertex i) - x (secondRingVertex i)) *
        ((if v = firstRingVertex i then 1 else 0) -
          (if v = secondRingVertex i then 1 else 0)) := by
  rw [coordinatedRingEdge_apply]
  change (x (firstRingVertex i) - x (secondRingVertex i)) *
    infiniteEdgeVector (firstRingVertex i) (secondRingVertex i) v = _
  simp [infiniteEdgeVector, lp.coeFn_sub, Pi.sub_apply, lp.single_apply,
    Pi.single_apply, eq_comm]

private theorem coordinatedRing_first_eval (x : TileHilbert Vertex) (i : Fin 8) :
    (coordinatedRingControl x) (firstRingVertex i) =
      x (firstRingVertex i) - x (secondRingVertex i) := by
  rw [coordinatedRingControl_apply, coordinatedRing_sum_eval]
  rw [Finset.sum_eq_single i]
  · rw [coordinatedRing_edge_eval]
    simp [coordinatedRing_disjoint]
  · intro j _ hj
    have h := coordinatedRing_matching i j (Ne.symm hj)
    rw [coordinatedRing_edge_eval]
    simp [h.1, h.2.2.1]
  · simp

private theorem coordinatedRing_second_eval (x : TileHilbert Vertex) (i : Fin 8) :
    (coordinatedRingControl x) (secondRingVertex i) =
      x (secondRingVertex i) - x (firstRingVertex i) := by
  rw [coordinatedRingControl_apply, coordinatedRing_sum_eval]
  rw [Finset.sum_eq_single i]
  · rw [coordinatedRing_edge_eval]
    have h := (coordinatedRing_disjoint i i).symm
    simp [h] <;> ring
  · intro j _ hj
    have h := coordinatedRing_matching i j (Ne.symm hj)
    rw [coordinatedRing_edge_eval]
    simp [h.2.1, h.2.2.2]
  · simp

private theorem coordinatedRing_outside_eval (x : TileHilbert Vertex) (v : Vertex)
    (ha : ∀ i : Fin 8, v ≠ firstRingVertex i)
    (hb : ∀ i : Fin 8, v ≠ secondRingVertex i) :
    (coordinatedRingControl x) v = 0 := by
  rw [coordinatedRingControl_apply, coordinatedRing_sum_eval]
  apply Finset.sum_eq_zero
  intro i _
  rw [coordinatedRing_edge_eval]
  simp [ha i, hb i]

/-- Exact full-space action, not an identity for a compressed matrix.
The proof covers both rings and every vertex outside them. -/
theorem coordinatedRingControl_compactA :
    coordinatedRingControl compactA = compactA - compactB := by
  apply lp.ext
  funext v
  change (coordinatedRingControl compactA) v = compactA v - compactB v
  by_cases ha : ∃ i : Fin 8, v = firstRingVertex i
  · obtain ⟨i, rfl⟩ := ha
    rw [coordinatedRing_first_eval]
    obtain ⟨_, hA, hB⟩ := coordinatedRing_amplitudes i
    rw [hA, hB]
  · by_cases hb : ∃ i : Fin 8, v = secondRingVertex i
    · obtain ⟨i, rfl⟩ := hb
      rw [coordinatedRing_second_eval]
      obtain ⟨h, _, _⟩ := coordinatedRing_amplitudes i
      rw [h]
    · have hA : ∀ i : Fin 8, v ≠ firstRingVertex i :=
        fun i hi => ha ⟨i, hi⟩
      have hB : ∀ i : Fin 8, v ≠ secondRingVertex i :=
        fun i hi => hb ⟨i, hi⟩
      rw [coordinatedRing_outside_eval _ _ hA hB,
        compactA_eq_zero_of_not_ring _ hA, compactB_eq_zero_of_not_ring _ hB,
        sub_zero]

theorem coordinatedRingControl_compactB :
    coordinatedRingControl compactB = compactB - compactA := by
  apply lp.ext
  funext v
  change (coordinatedRingControl compactB) v = compactB v - compactA v
  by_cases ha : ∃ i : Fin 8, v = firstRingVertex i
  · obtain ⟨i, rfl⟩ := ha
    rw [coordinatedRing_first_eval]
    obtain ⟨h, _, _⟩ := coordinatedRing_amplitudes i
    rw [h]
  · by_cases hb : ∃ i : Fin 8, v = secondRingVertex i
    · obtain ⟨i, rfl⟩ := hb
      rw [coordinatedRing_second_eval]
      obtain ⟨_, hA, hB⟩ := coordinatedRing_amplitudes i
      rw [hA, hB]
    · have hA : ∀ i : Fin 8, v ≠ firstRingVertex i :=
        fun i hi => ha ⟨i, hi⟩
      have hB : ∀ i : Fin 8, v ≠ secondRingVertex i :=
        fun i hi => hb ⟨i, hi⟩
      rw [coordinatedRing_outside_eval _ _ hA hB,
        compactA_eq_zero_of_not_ring _ hA, compactB_eq_zero_of_not_ring _ hB,
        sub_zero]

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
