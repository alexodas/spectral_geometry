module

public import SpectralGeometry.AmmannBeenkerNaturalPlateauPairs
public import SpectralGeometry.AmmannBeenkerCentralKernel

public section

/-!
# Local completeness of the natural compact modes

The radius-two cell is not an isolated finite graph. Its true exterior
equations force alternating second-ring amplitudes. Combining these
constraints with the actual full-degree interior equations classifies
all Laplacian eigenvectors supported in the seventeen-site sector,
without fixing the eigenvalue in advance.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

/-- The eight explicit exterior vertices used in the boundary equations. -/
@[expose] def naturalThirdRingLift (i : Fin 8) : Lattice :=
  ![![1, 1, 0, -1], ![1, 1, 1, 0], ![0, 1, 1, 1], ![-1, 0, 1, 1], ![-1, -1, 0, 1], ![-1, -1, -1, 0], ![0, -1, -1, -1], ![1, 0, -1, -1]] i

theorem naturalThirdRingLift_admitted (i : Fin 8) :
    Admitted (naturalThirdRingLift i) := by
  have hl := alpha_bounds.1
  have hu := alpha_bounds.2
  fin_cases i <;> norm_num [naturalThirdRingLift, Admitted, Window, internal, abs_lt]
  all_goals repeat' constructor
  all_goals linarith

@[expose] def naturalThirdRingVertex (i : Fin 8) : Vertex :=
  latticeVertex (naturalThirdRingLift i) (naturalThirdRingLift_admitted i)

@[simp] theorem naturalThirdRingVertex_val (i : Fin 8) :
    (naturalThirdRingVertex i).val = naturalThirdRingLift i := rfl

theorem naturalThirdRingVertex_outside (i : Fin 8) :
    naturalThirdRingVertex i ∉ sector := by
  intro h
  have hr := (mem_sector _).mp h
  have hs : ‖position (naturalThirdRingVertex i)‖ ^ 2 = 3 + 4 * alpha := by
    fin_cases i <;> norm_num [position, naturalThirdRingVertex_val, naturalThirdRingLift,
      physical, Complex.sq_norm, Complex.normSq_apply]
    all_goals nlinarith [alpha_sq]
  nlinarith [norm_nonneg (position (naturalThirdRingVertex i)), alpha_bounds.1]

set_option maxHeartbeats 6000000 in
/-- Exact central-neighbor sums at the exterior witnesses, in cyclic order. -/
theorem naturalThirdRing_neighbor_sum (z : Fin 17 → ℝ) :
    (fun i : Fin 8 =>
      ∑ j : Fin 17, if Adjacent (naturalThirdRingVertex i) (centralVertex j)
        then z j else 0) =
    ![z 16 + z 9, z 9 + z 10, z 10 + z 11, z 11 + z 12, z 12 + z 13, z 13 + z 14, z 14 + z 15, z 15 + z 16] := by
  funext i
  fin_cases i <;>
    norm_num [Fin.sum_univ_succ, Adjacent, naturalThirdRingVertex_val,
      naturalThirdRingLift, centralVertex_val, centralLift, basis,
      Fin.exists_fin_succ, funext_iff, Fin.forall_fin_succ,
      Pi.single, Matrix.vecHead, Matrix.vecTail, Function.update_apply] <;> ring

/-- The degree diagonal retains the edges to exterior vertices. -/
theorem naturalCell_degree_values :
    (fun i : Fin 17 => ((neighbors (centralVertex i)).card : ℝ)) =
      ![8, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4] := by
  funext i
  fin_cases i
  · change ((neighbors (centralVertex (0 : Fin 17))).card : ℝ) = 8
    rw [centralVertex_zero, origin_neighbors_card]
    norm_num
  · change ((neighbors (firstRingVertex 0)).card : ℝ) = 3
    rw [firstRing_degree]
    norm_num
  · change ((neighbors (firstRingVertex 1)).card : ℝ) = 3
    rw [firstRing_degree]
    norm_num
  · change ((neighbors (firstRingVertex 2)).card : ℝ) = 3
    rw [firstRing_degree]
    norm_num
  · change ((neighbors (firstRingVertex 3)).card : ℝ) = 3
    rw [firstRing_degree]
    norm_num
  · change ((neighbors (firstRingVertex 4)).card : ℝ) = 3
    rw [firstRing_degree]
    norm_num
  · change ((neighbors (firstRingVertex 5)).card : ℝ) = 3
    rw [firstRing_degree]
    norm_num
  · change ((neighbors (firstRingVertex 6)).card : ℝ) = 3
    rw [firstRing_degree]
    norm_num
  · change ((neighbors (firstRingVertex 7)).card : ℝ) = 3
    rw [firstRing_degree]
    norm_num
  · change ((neighbors (secondRingVertex 0)).card : ℝ) = 4
    rw [secondRing_degree]
    norm_num
  · change ((neighbors (secondRingVertex 1)).card : ℝ) = 4
    rw [secondRing_degree]
    norm_num
  · change ((neighbors (secondRingVertex 2)).card : ℝ) = 4
    rw [secondRing_degree]
    norm_num
  · change ((neighbors (secondRingVertex 3)).card : ℝ) = 4
    rw [secondRing_degree]
    norm_num
  · change ((neighbors (secondRingVertex 4)).card : ℝ) = 4
    rw [secondRing_degree]
    norm_num
  · change ((neighbors (secondRingVertex 5)).card : ℝ) = 4
    rw [secondRing_degree]
    norm_num
  · change ((neighbors (secondRingVertex 6)).card : ℝ) = 4
    rw [secondRing_degree]
    norm_num
  · change ((neighbors (secondRingVertex 7)).card : ℝ) = 4
    rw [secondRing_degree]
    norm_num

/-- Full graph eigenvector equations on the cell and its exterior witnesses. -/
theorem naturalCell_coordinate_equations (x : TileHilbert Vertex)
    (hx : ∀ v : Vertex, v ∉ sector → x v = 0)
    (c : ℝ) (he : interaction x = c • x) :
    let z := fun i : Fin 17 => x (centralVertex i)
    (∀ i : Fin 17,
      (![8, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4] : Fin 17 → ℝ) i * z i -
        (![z 1 + z 2 + z 3 + z 4 + z 5 + z 6 + z 7 + z 8, z 0 + z 9 + z 16, z 0 + z 10 + z 9, z 0 + z 11 + z 10, z 0 + z 12 + z 11, z 0 + z 13 + z 12, z 0 + z 14 + z 13, z 0 + z 15 + z 14, z 0 + z 16 + z 15, z 1 + z 2, z 2 + z 3, z 3 + z 4, z 4 + z 5, z 5 + z 6, z 6 + z 7, z 7 + z 8, z 8 + z 1] : Fin 17 → ℝ) i = 16 * c * z i) ∧
    (∀ i : Fin 8,
      (![z 16 + z 9, z 9 + z 10, z 10 + z 11, z 11 + z 12, z 12 + z 13, z 13 + z 14, z 14 + z 15, z 15 + z 16] : Fin 8 → ℝ) i = 0) := by
  dsimp only
  constructor
  · intro i
    have h := congrArg (fun y : TileHilbert Vertex => y (centralVertex i)) he
    change interaction x (centralVertex i) = c * x (centralVertex i) at h
    rw [interaction_apply, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      neighbors_sum_of_sector_support x hx] at h
    have hd := congrFun naturalCell_degree_values i
    have hn := congrFun (central_neighbor_sum (fun k => x (centralVertex k))) i
    change ((neighbors (centralVertex i)).card : ℝ) = _ at hd
    change (∑ j : Fin 17, if Adjacent (centralVertex i) (centralVertex j)
      then x (centralVertex j) else 0) = _ at hn
    rw [hd, hn] at h
    linarith only [h]
  · intro i
    have h := congrArg (fun y : TileHilbert Vertex => y (naturalThirdRingVertex i)) he
    change interaction x (naturalThirdRingVertex i) = c * x (naturalThirdRingVertex i) at h
    rw [interaction_apply, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      neighbors_sum_of_sector_support x hx, hx _ (naturalThirdRingVertex_outside i)] at h
    have hn := congrFun (naturalThirdRing_neighbor_sum (fun k => x (centralVertex k))) i
    change (∑ j : Fin 17, if Adjacent (naturalThirdRingVertex i) (centralVertex j)
      then x (centralVertex j) else 0) = _ at hn
    rw [hn] at h
    linarith only [h]

set_option maxHeartbeats 3000000 in
/-- The interior and exterior equations imply precisely alternating
ring coordinates, with each nonzero coefficient fixing its own energy. -/
theorem naturalCell_coordinate_classification (z : Fin 17 → ℝ) (c : ℝ)
    (hi : ∀ i : Fin 17,
      (![8, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4] : Fin 17 → ℝ) i * z i -
        (![z 1 + z 2 + z 3 + z 4 + z 5 + z 6 + z 7 + z 8, z 0 + z 9 + z 16, z 0 + z 10 + z 9, z 0 + z 11 + z 10, z 0 + z 12 + z 11, z 0 + z 13 + z 12, z 0 + z 14 + z 13, z 0 + z 15 + z 14, z 0 + z 16 + z 15, z 1 + z 2, z 2 + z 3, z 3 + z 4, z 4 + z 5, z 5 + z 6, z 6 + z 7, z 7 + z 8, z 8 + z 1] : Fin 17 → ℝ) i = 16 * c * z i)
    (hb : ∀ i : Fin 8,
      (![z 16 + z 9, z 9 + z 10, z 10 + z 11, z 11 + z 12, z 12 + z 13, z 13 + z 14, z 14 + z 15, z 15 + z 16] : Fin 8 → ℝ) i = 0) :
    z = centralCompactCoordinates (z 1) (z 9) ∧
      (3 - 16 * c) * z 1 = 0 ∧ (4 - 16 * c) * z 9 = 0 := by
  have h1 := hi 1
  have h2 := hi 2
  have h3 := hi 3
  have h4 := hi 4
  have h5 := hi 5
  have h6 := hi 6
  have h7 := hi 7
  have h8 := hi 8
  have h9 := hi 9
  have h10 := hi 10
  have h11 := hi 11
  have h12 := hi 12
  have h13 := hi 13
  have h14 := hi 14
  have h15 := hi 15
  have h16 := hi 16
  have hb1 := hb 1
  have hb2 := hb 2
  have hb3 := hb 3
  have hb4 := hb 4
  have hb5 := hb 5
  have hb6 := hb 6
  have hb7 := hb 7
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have b10 : z 10 = -z 9 := by
    linarith only [hb1]
  have b11 : z 11 = z 9 := by
    linarith only [hb2, b10]
  have b12 : z 12 = -z 9 := by
    linarith only [hb3, b11]
  have b13 : z 13 = z 9 := by
    linarith only [hb4, b12]
  have b14 : z 14 = -z 9 := by
    linarith only [hb5, b13]
  have b15 : z 15 = z 9 := by
    linarith only [hb6, b14]
  have b16 : z 16 = -z 9 := by
    linarith only [hb7, b15]
  simp only [b10, b11, b12, b13, b14, b15, b16] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  have hs : z 1 + z 2 + z 3 + z 4 + z 5 + z 6 + z 7 + z 8 = 0 := by
    linear_combination -(1 / 2 : ℝ) * (h9 + h10 + h11 + h12 + h13 + h14 + h15 + h16)
  have hz : z 0 = 0 := by
    linear_combination -(1 / 8 : ℝ) * (h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8) + ((3 - 16 * c) / 8) * hs
  have hbp : (4 - 16 * c) * z 9 = 0 := by
    linear_combination (1 / 8 : ℝ) * (h9 - h10 + h11 - h12 + h13 - h14 + h15 - h16)
  have ha0 : z 1 + z 2 = 0 := by
    linear_combination hbp - h9
  have ha1 : z 2 + z 3 = 0 := by
    linear_combination -hbp - h10
  have ha2 : z 3 + z 4 = 0 := by
    linear_combination hbp - h11
  have ha3 : z 4 + z 5 = 0 := by
    linear_combination -hbp - h12
  have ha4 : z 5 + z 6 = 0 := by
    linear_combination hbp - h13
  have ha5 : z 6 + z 7 = 0 := by
    linear_combination -hbp - h14
  have ha6 : z 7 + z 8 = 0 := by
    linear_combination hbp - h15
  have a2 : z 2 = -z 1 := by
    linarith only [ha0]
  have a3 : z 3 = z 1 := by
    linarith only [ha1, a2]
  have a4 : z 4 = -z 1 := by
    linarith only [ha2, a3]
  have a5 : z 5 = z 1 := by
    linarith only [ha3, a4]
  have a6 : z 6 = -z 1 := by
    linarith only [ha4, a5]
  have a7 : z 7 = z 1 := by
    linarith only [ha5, a6]
  have a8 : z 8 = -z 1 := by
    linarith only [ha6, a7]
  have hap : (3 - 16 * c) * z 1 = 0 := by
    linear_combination h1 + hz
  refine ⟨?_, hap, hbp⟩
  funext i
  fin_cases i <;> norm_num [centralCompactCoordinates] <;>
    linarith only [hz, a2, a3, a4, a5, a6, a7, a8, b10, b11, b12, b13, b14, b15, b16]

/-- Every full-graph Laplacian eigenvector supported in the cell belongs
to the two known compact directions, with the two energy constraints. -/
theorem naturalCell_supported_eigenvector_representation
    (x : TileHilbert Vertex) (hx : ∀ v : Vertex, v ∉ sector → x v = 0)
    (c : ℝ) (he : interaction x = c • x) :
    x = x (centralVertex 1) • compactA + x (centralVertex 9) • compactB ∧
      (3 - 16 * c) * x (centralVertex 1) = 0 ∧
      (4 - 16 * c) * x (centralVertex 9) = 0 := by
  obtain ⟨hi, hb⟩ := naturalCell_coordinate_equations x hx c he
  obtain ⟨hr, ha, hb'⟩ := naturalCell_coordinate_classification
    (fun i => x (centralVertex i)) c hi hb
  refine ⟨?_, ha, hb'⟩
  apply lp.ext
  funext v
  change x v = x (centralVertex 1) * compactA v + x (centralVertex 9) * compactB v
  by_cases hv : v ∈ sector
  · rw [sector_eq_centralPatch] at hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    rw [show compactA (centralVertex i) = centralCompactCoordinates 1 0 i from
      congrFun compactA_centralCoordinates i]
    rw [show compactB (centralVertex i) = centralCompactCoordinates 0 1 i from
      congrFun compactB_centralCoordinates i]
    rw [show x (centralVertex i) =
      centralCompactCoordinates (x (centralVertex 1)) (x (centralVertex 9)) i from
      congrFun hr i]
    exact congrFun (centralCompactCoordinates_decomposition
      (x (centralVertex 1)) (x (centralVertex 9))) i
  · have hv' : v ∉ centralPatch := by simpa [sector_eq_centralPatch] using hv
    rw [hx v hv, compactA_supported_centralPatch v hv', compactB_supported_centralPatch v hv']
    ring

/-- No third nonzero eigenvector direction occurs at any energy with
support inside the seventeen-site sector of the unmodified Laplacian. -/
theorem naturalCell_supported_eigenvector_classification
    (x : TileHilbert Vertex) (hx : ∀ v : Vertex, v ∉ sector → x v = 0)
    (c : ℝ) (he : interaction x = c • x) (hn : x ≠ 0) :
    (c = 3 / 16 ∧ ∃ a : ℝ, a ≠ 0 ∧ x = a • compactA) ∨
      (c = 1 / 4 ∧ ∃ b : ℝ, b ≠ 0 ∧ x = b • compactB) := by
  obtain ⟨hr, ha, hb⟩ := naturalCell_supported_eigenvector_representation x hx c he
  by_cases hA : x (centralVertex 1) = 0
  · have hB : x (centralVertex 9) ≠ 0 := by
      intro hz
      apply hn
      simpa [hA, hz] using hr
    have hc := (mul_eq_zero.mp hb).resolve_right hB
    exact Or.inr ⟨by linarith, x (centralVertex 9), hB, by simpa [hA] using hr⟩
  · have hc := (mul_eq_zero.mp ha).resolve_right hA
    have hB : x (centralVertex 9) = 0 := by
      apply (mul_eq_zero.mp hb).resolve_left
      linarith
    exact Or.inl ⟨by linarith, x (centralVertex 1), hA, by simpa [hB] using hr⟩

end
end SpectralGeometry.AmmannBeenker
