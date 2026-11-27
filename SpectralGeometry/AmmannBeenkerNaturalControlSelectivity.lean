module

public import SpectralGeometry.AmmannBeenkerNaturalRemoteControls

public section

/-!
# Exact spatial selectivity of the natural remote controls

The local operators annihilate every state vanishing on the controlled
cell. For disjoint recurring cells this gives exact cross-cell
decoupling. A finite sum of independently weighted local controls
preserves each selected plane and the central crossing plane, as well
as their common orthogonal complement. No collective gap is assumed.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

theorem naturalRemoteFirstRing_mem_cell (t : Lattice) (i : Fin 8) :
    naturalRemoteFirstRing t i ∈ naturalRemoteCell t := by
  exact Finset.mem_image.mpr ⟨firstRingVertex i, natural_firstRing_mem_patch i, rfl⟩

theorem naturalRemoteSecondRing_mem_cell (t : Lattice) (i : Fin 8) :
    naturalRemoteSecondRing t i ∈ naturalRemoteCell t := by
  exact Finset.mem_image.mpr ⟨secondRingVertex i, natural_secondRing_mem_patch i, rfl⟩

theorem naturalRemoteEdge_apply (t : Lattice) (i : Fin 8) (x : TileHilbert Vertex) :
    naturalRemoteEdge t i x =
      (x (naturalRemoteFirstRing t i) - x (naturalRemoteSecondRing t i)) •
        infiniteEdgeVector (naturalRemoteFirstRing t i) (naturalRemoteSecondRing t i) := by
  simp [naturalRemoteEdge, InnerProductSpace.rankOne_apply, infiniteEdgeVector,
    inner_sub_left, lp.inner_single_left, RCLike.inner_apply]
  module

theorem naturalRemoteControls_zero_of_cell_zero (t : Lattice)
    (x : TileHilbert Vertex) (hx : ∀ w ∈ naturalRemoteCell t, x w = 0) :
    naturalRemoteOnsiteControl t x = 0 ∧ naturalRemoteMatchingControl t x = 0 := by
  constructor
  · apply lp.ext
    funext w
    change finiteSectorProjection (Finset.univ.image (naturalRemoteFirstRing t)) x w = 0
    rw [finiteSectorProjection_apply]
    split_ifs with hw
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
      exact hx _ (naturalRemoteFirstRing_mem_cell t i)
    · rfl
  · rw [naturalRemoteMatchingControl, ContinuousLinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [naturalRemoteEdge_apply, hx _ (naturalRemoteFirstRing_mem_cell t i),
      hx _ (naturalRemoteSecondRing_mem_cell t i), sub_self, zero_smul]

@[expose] def naturalRemotePerturbation (t : Lattice) (δ η : ℝ) :
    TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  δ • naturalRemoteOnsiteControl t + η • naturalRemoteMatchingControl t

theorem naturalRemotePerturbation_zero_of_cell_zero (t : Lattice) (δ η : ℝ)
    (x : TileHilbert Vertex) (hx : ∀ w ∈ naturalRemoteCell t, x w = 0) :
    naturalRemotePerturbation t δ η x = 0 := by
  obtain ⟨ha, hb⟩ := naturalRemoteControls_zero_of_cell_zero t x hx
  simp [naturalRemotePerturbation, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ha, hb]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem naturalRemotePerturbation_zero_of_disjoint (t s : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (hdis : ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
      n + t ≠ m + s)
    (δ η : ℝ) (x : TileHilbert Vertex) :
    naturalRemotePerturbation t δ η (translateFiniteState centralPatch s x) = 0 := by
  apply naturalRemotePerturbation_zero_of_cell_zero
  intro w hw
  obtain ⟨u, hu, he⟩ := (naturalRemoteCell_mem_iff t hrec w).mp hw
  apply translateFiniteState_apply_zero
  intro q hq
  rw [he]
  exact hdis u.val (centralPatch_val_mem_recurrence u hu)
    q.val (centralPatch_val_mem_recurrence q hq)

theorem naturalRemotePerturbation_zero_of_central_support (v : Vertex)
    (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (δ η : ℝ) (x : TileHilbert Vertex)
    (hx : ∀ w : Vertex, w ∉ sector → x w = 0) :
    naturalRemotePerturbation v.val δ η x = 0 := by
  apply naturalRemotePerturbation_zero_of_cell_zero
  intro w hw
  apply hx
  intro hs
  exact naturalRemoteCell_disjoint_sector v hr hrec w hs hw

theorem naturalRemoteEdge_symmetric (t : Lattice) (i : Fin 8)
    (x y : TileHilbert Vertex) :
    inner ℝ (naturalRemoteEdge t i x) y = inner ℝ x (naturalRemoteEdge t i y) := by
  rw [naturalRemoteEdge_apply, naturalRemoteEdge_apply,
    real_inner_smul_left, real_inner_smul_right]
  simp [infiniteEdgeVector, inner_sub_right, inner_sub_left,
    lp.inner_single_right, lp.inner_single_left, RCLike.inner_apply]
  ring

theorem naturalRemoteMatching_symmetric (t : Lattice) (x y : TileHilbert Vertex) :
    inner ℝ (naturalRemoteMatchingControl t x) y =
      inner ℝ x (naturalRemoteMatchingControl t y) := by
  simp only [naturalRemoteMatchingControl, ContinuousLinearMap.sum_apply,
    sum_inner, inner_sum, naturalRemoteEdge_symmetric]

theorem naturalRemotePerturbation_symmetric (t : Lattice) (δ η : ℝ)
    (x y : TileHilbert Vertex) :
    inner ℝ (naturalRemotePerturbation t δ η x) y =
      inner ℝ x (naturalRemotePerturbation t δ η y) := by
  simp only [naturalRemotePerturbation, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, naturalRemoteMatching_symmetric,
    naturalRemoteOnsiteControl, finiteSectorProjection_symmetric]

theorem naturalRemotePerturbation_pair_action (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (δ η a b : ℝ) :
    naturalRemotePerturbation t δ η (a • translatedCompactA t + b • translatedCompactB t) =
      ((δ + η) * a - η * b) • translatedCompactA t +
      (η * b - η * a) • translatedCompactB t := by
  simp only [naturalRemotePerturbation, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, map_add, map_smul,
    naturalRemoteOnsite_compactA t hrec, naturalRemoteOnsite_compactB t hrec,
    naturalRemoteMatching_compactA t hrec, naturalRemoteMatching_compactB t hrec]
  module

/-- Independent simultaneous signed controls on a finite set of cells. -/
@[expose] def naturalFamilyHamiltonian (S : Finset Vertex) (δ η : Vertex → ℝ) :
    TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  canonicalPlateauHamiltonian + ∑ v ∈ S, naturalRemotePerturbation v.val (δ v) (η v)

theorem naturalFamilyHamiltonian_symmetric (S : Finset Vertex)
    (δ η : Vertex → ℝ) (x y : TileHilbert Vertex) :
    inner ℝ (naturalFamilyHamiltonian S δ η x) y =
      inner ℝ x (naturalFamilyHamiltonian S δ η y) := by
  have h := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    canonicalPlateau_isolated_double_eigenvalue.1) x y
  change inner ℝ (canonicalPlateauHamiltonian x) y =
    inner ℝ x (canonicalPlateauHamiltonian y) at h
  simp only [naturalFamilyHamiltonian, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, inner_add_left, inner_add_right,
    sum_inner, inner_sum, h, naturalRemotePerturbation_symmetric]

theorem naturalFamilyHamiltonian_isSelfAdjoint (S : Finset Vertex)
    (δ η : Vertex → ℝ) : IsSelfAdjoint (naturalFamilyHamiltonian S δ η) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact naturalFamilyHamiltonian_symmetric S δ η

/-- On a selected cell, the entire family Hamiltonian acts exactly as
its own two controls and the rest drift. Other controls disappear. -/
theorem naturalFamilyHamiltonian_pair_action (S : Finset Vertex)
    (hp : ∀ v ∈ S, 4 < ‖position v‖ ∧
      ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (hd : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
        n + v.val ≠ m + w.val)
    (δ η : Vertex → ℝ) (v : Vertex) (hv : v ∈ S) (a b : ℝ) :
    naturalFamilyHamiltonian S δ η (a • translatedCompactA v.val + b • translatedCompactB v.val) =
      ((canonicalPlateauHeight + 3 / 16 + δ v + η v) * a - η v * b) • translatedCompactA v.val +
      ((canonicalPlateauHeight + 1 / 4 + η v) * b - η v * a) • translatedCompactB v.val := by
  have hrec := (hp v hv).2
  unfold naturalFamilyHamiltonian
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    Finset.sum_eq_single_of_mem v hv]
  · rw [naturalRemotePerturbation_pair_action v.val hrec]
    obtain ⟨ha, hb⟩ := naturalPlateauPair_eigenvectors v (hp v hv).1 hrec
    simp only [map_add, map_smul, ha, hb]
    module
  · intro w hw hwv
    have hdis := hd w hw v hv hwv
    have hA := naturalRemotePerturbation_zero_of_disjoint w.val v.val
      (hp w hw).2 hdis (δ w) (η w) compactA
    have hB := naturalRemotePerturbation_zero_of_disjoint w.val v.val
      (hp w hw).2 hdis (δ w) (η w) compactB
    change naturalRemotePerturbation w.val (δ w) (η w) (translatedCompactA v.val) = 0 at hA
    change naturalRemotePerturbation w.val (δ w) (η w) (translatedCompactB v.val) = 0 at hB
    simp only [map_add, map_smul, hA, hB, smul_zero, add_zero]

/-- All remote controls leave the original crossing plane unchanged. -/
theorem naturalFamilyHamiltonian_central_action (S : Finset Vertex)
    (hp : ∀ v ∈ S, 4 < ‖position v‖ ∧
      ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (δ η : Vertex → ℝ) (a b : ℝ) :
    naturalFamilyHamiltonian S δ η (a • compactA + b • compactB) =
      crossingEnergy • (a • compactA + b • compactB) := by
  have hx (w : Vertex) (hw : w ∉ sector) : (a • compactA + b • compactB) w = 0 := by
    have hw' : w ∉ centralPatch := by simpa [sector_eq_centralPatch] using hw
    change a * compactA w + b * compactB w = 0
    rw [compactA_supported_centralPatch w hw', compactB_supported_centralPatch w hw']
    ring
  have hz : (∑ v ∈ S, naturalRemotePerturbation v.val (δ v) (η v)
      (a • compactA + b • compactB)) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact naturalRemotePerturbation_zero_of_central_support v (hp v hv).1
      (hp v hv).2 (δ v) (η v) _ hx
  obtain ⟨_, _, ha, hb, _⟩ := canonicalPlateau_isolated_double_eigenvalue
  unfold naturalFamilyHamiltonian
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply, hz, add_zero]
  simp only [map_add, map_smul, ha, hb]
  module

/-- Orthogonality to the two directions of a selected remote cell is
preserved by the entire driven family operator. -/
theorem naturalFamilyHamiltonian_remote_complement (S : Finset Vertex)
    (hp : ∀ v ∈ S, 4 < ‖position v‖ ∧
      ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (hd : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
        n + v.val ≠ m + w.val)
    (δ η : Vertex → ℝ) (v : Vertex) (hv : v ∈ S)
    (x : TileHilbert Vertex)
    (ha : inner ℝ (translatedCompactA v.val) x = 0)
    (hb : inner ℝ (translatedCompactB v.val) x = 0) :
    inner ℝ (translatedCompactA v.val) (naturalFamilyHamiltonian S δ η x) = 0 ∧
      inner ℝ (translatedCompactB v.val) (naturalFamilyHamiltonian S δ η x) = 0 := by
  have hA := naturalFamilyHamiltonian_pair_action S hp hd δ η v hv 1 0
  have hB := naturalFamilyHamiltonian_pair_action S hp hd δ η v hv 0 1
  simp only [one_smul, zero_smul, add_zero, zero_add] at hA hB
  constructor
  · rw [← naturalFamilyHamiltonian_symmetric, hA, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, ha, hb]
    ring
  · rw [← naturalFamilyHamiltonian_symmetric, hB, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, ha, hb]
    ring

theorem naturalFamilyHamiltonian_central_complement (S : Finset Vertex)
    (hp : ∀ v ∈ S, 4 < ‖position v‖ ∧
      ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (δ η : Vertex → ℝ) (x : TileHilbert Vertex)
    (ha : inner ℝ compactA x = 0) (hb : inner ℝ compactB x = 0) :
    inner ℝ compactA (naturalFamilyHamiltonian S δ η x) = 0 ∧
      inner ℝ compactB (naturalFamilyHamiltonian S δ η x) = 0 := by
  have hA := naturalFamilyHamiltonian_central_action S hp δ η 1 0
  have hB := naturalFamilyHamiltonian_central_action S hp δ η 0 1
  simp only [one_smul, zero_smul, add_zero, zero_add] at hA hB
  constructor
  · rw [← naturalFamilyHamiltonian_symmetric, hA, real_inner_smul_left, ha, mul_zero]
  · rw [← naturalFamilyHamiltonian_symmetric, hB, real_inner_smul_left, hb, mul_zero]

end
end SpectralGeometry.AmmannBeenker
