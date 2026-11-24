module

public import SpectralGeometry.AmmannBeenkerCentralKernel
public import SpectralGeometry.AmmannBeenkerTwoControlAlgebra

public section

/-!
# Coordinated inter-ring control (L7a)

Eight actual inter-ring edges, with unit increments in the same
rank-one Laplacian convention as crossingEdge. This module concerns
static real full-space algebra, not quantum state preparation.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped BigOperators Classical

/-- Pair corresponding sites in the two cyclic ring enumerations. -/
@[expose] def coordinatedRingPair (i : Fin 8) : Vertex × Vertex :=
  (firstRingVertex i, secondRingVertex i)

theorem coordinatedRingPair_adjacent (i : Fin 8) :
    Adjacent (coordinatedRingPair i).1 (coordinatedRingPair i).2 :=
  (firstRing_adjacent_secondRing i i).2 (Or.inl rfl)

theorem coordinatedRingPair_injective :
    Function.Injective coordinatedRingPair := by
  intro i j h
  exact firstRing_injective (congrArg Prod.fst h)

theorem coordinatedRing_disjoint (i j : Fin 8) :
    firstRingVertex i ≠ secondRingVertex j := by
  intro h
  have hi := congrArg Fin.val (centralVertex_injective h)
  change i.val + 1 = j.val + 9 at hi
  omega

/-- The eight pairs are distinct and have no shared endpoints. -/
theorem coordinatedRing_matching (i j : Fin 8) (h : i ≠ j) :
    firstRingVertex i ≠ firstRingVertex j ∧
    secondRingVertex i ≠ secondRingVertex j ∧
    firstRingVertex i ≠ secondRingVertex j ∧
    secondRingVertex i ≠ firstRingVertex j :=
  ⟨fun e => h (firstRing_injective e),
    fun e => h (secondRing_injective e),
    coordinatedRing_disjoint i j, (coordinatedRing_disjoint j i).symm⟩

/-- Unit graph-edge correction for each genuine matched pair. -/
@[expose] def coordinatedRingEdge (i : Fin 8) :
    TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  InnerProductSpace.rankOne ℝ
    (infiniteEdgeVector (firstRingVertex i) (secondRingVertex i))
    (infiniteEdgeVector (firstRingVertex i) (secondRingVertex i))

theorem coordinatedRingEdge_apply (i : Fin 8) (x : TileHilbert Vertex) :
    coordinatedRingEdge i x =
      (x (firstRingVertex i) - x (secondRingVertex i)) •
        infiniteEdgeVector (firstRingVertex i) (secondRingVertex i) := by
  simp [coordinatedRingEdge, InnerProductSpace.rankOne_apply, infiniteEdgeVector,
    inner_sub_left, lp.inner_single_left, RCLike.inner_apply]
  module

/-- Finite sum of the eight local bounded edge operators. -/
@[expose] def coordinatedRingControl : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  ∑ i : Fin 8, coordinatedRingEdge i

theorem coordinatedRingControl_apply (x : TileHilbert Vertex) :
    coordinatedRingControl x = ∑ i : Fin 8, coordinatedRingEdge i x := by
  simp only [coordinatedRingControl, ContinuousLinearMap.sum_apply]

/-- The signs coincide on corresponding ring sites. -/
theorem coordinatedRing_amplitudes (i : Fin 8) :
    compactA (firstRingVertex i) = compactB (secondRingVertex i) ∧
    compactA (secondRingVertex i) = 0 ∧
    compactB (firstRingVertex i) = 0 := by
  have ha (k : Fin 17) :
      compactA (centralVertex k) = centralCompactCoordinates 1 0 k :=
    congrFun compactA_centralCoordinates k
  have hb (k : Fin 17) :
      compactB (centralVertex k) = centralCompactCoordinates 0 1 k :=
    congrFun compactB_centralCoordinates k
  simp only [firstRingVertex, secondRingVertex, ha, hb]
  fin_cases i <;> norm_num [centralCompactCoordinates]

/-- The paired amplitudes cancel for the dark combination on every
individual edge, hence also on the complete infinite-space operator. -/
theorem coordinatedRingEdge_dark_zero (i : Fin 8) :
    coordinatedRingEdge i crossingDark = 0 := by
  rw [coordinatedRingEdge_apply]
  obtain ⟨h, ha, hb⟩ := coordinatedRing_amplitudes i
  have hz : crossingDark (firstRingVertex i) -
      crossingDark (secondRingVertex i) = 0 := by
    change (1 / 4 : ℝ) * (compactA (firstRingVertex i) +
      compactB (firstRingVertex i)) -
      (1 / 4 : ℝ) * (compactA (secondRingVertex i) +
        compactB (secondRingVertex i)) = 0
    rw [h, ha, hb]
    ring
  rw [hz, zero_smul]

theorem coordinatedRingControl_dark_zero :
    coordinatedRingControl crossingDark = 0 := by
  rw [coordinatedRingControl_apply]
  simp only [coordinatedRingEdge_dark_zero, Finset.sum_const_zero]

/-- Each edge is symmetric on the entire real Hilbert space. -/
theorem coordinatedRingEdge_symmetric (i : Fin 8) (x y : TileHilbert Vertex) :
    inner ℝ x (coordinatedRingEdge i y) =
      inner ℝ (coordinatedRingEdge i x) y := by
  rw [coordinatedRingEdge_apply, coordinatedRingEdge_apply,
    real_inner_smul_right, real_inner_smul_left]
  simp [infiniteEdgeVector, inner_sub_right, inner_sub_left,
    lp.inner_single_right, lp.inner_single_left, RCLike.inner_apply]
  ring

theorem coordinatedRingControl_symmetric (x y : TileHilbert Vertex) :
    inner ℝ x (coordinatedRingControl y) =
      inner ℝ (coordinatedRingControl x) y := by
  simp only [coordinatedRingControl_apply, inner_sum, sum_inner,
    coordinatedRingEdge_symmetric]

end
end SpectralGeometry.AmmannBeenker
