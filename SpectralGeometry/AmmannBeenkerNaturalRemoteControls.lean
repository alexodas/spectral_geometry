module

public import SpectralGeometry.AmmannBeenkerNaturalDefectComparison
public import SpectralGeometry.AmmannBeenkerCoordinatedInvariantPlane

public section

/-!
# Translated local controls on natural recurring cells

The onsite control acts only on the translated first ring. The edge
control is the sum of eight actual matched graph-edge Laplacians.
Finite-state translation, not a global symmetry, intertwines their
actions on the two supported modes. The rest Hamiltonian is unchanged.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

theorem natural_firstRing_mem_patch (i : Fin 8) : firstRingVertex i ∈ centralPatch := by
  rw [← sector_eq_centralPatch]
  exact firstRing_mem_sector i

theorem natural_secondRing_mem_patch (i : Fin 8) : secondRingVertex i ∈ centralPatch := by
  rw [← sector_eq_centralPatch]
  exact secondRing_mem_sector i

theorem natural_patchTranslate_injective_on (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) :
    Set.InjOn (patchTranslateVertex t) (centralPatch : Set Vertex) := by
  intro u hu w hw he
  have h := congrArg (fun z : Vertex => z.val) he
  rw [patchTranslateVertex_val t u (central_recurrence_admitted t hrec u hu),
    patchTranslateVertex_val t w (central_recurrence_admitted t hrec w hw)] at h
  exact Subtype.ext (add_right_cancel h)

@[expose] def naturalRemoteFirstRing (t : Lattice) (i : Fin 8) : Vertex :=
  patchTranslateVertex t (firstRingVertex i)

@[expose] def naturalRemoteSecondRing (t : Lattice) (i : Fin 8) : Vertex :=
  patchTranslateVertex t (secondRingVertex i)

theorem naturalRemoteRing_adjacent (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (i : Fin 8) : Adjacent (naturalRemoteFirstRing t i) (naturalRemoteSecondRing t i) := by
  have ha := patchTranslateVertex_val t (firstRingVertex i)
    (central_recurrence_admitted t hrec _ (natural_firstRing_mem_patch i))
  have hb := patchTranslateVertex_val t (secondRingVertex i)
    (central_recurrence_admitted t hrec _ (natural_secondRing_mem_patch i))
  change (naturalRemoteFirstRing t i).val = _ at ha
  change (naturalRemoteSecondRing t i).val = _ at hb
  obtain ⟨j, hj | hj⟩ := coordinatedRingPair_adjacent i
  · refine ⟨j, Or.inl ?_⟩
    rw [ha, hb, show (secondRingVertex i).val = (firstRingVertex i).val + basis j from hj]
    abel
  · refine ⟨j, Or.inr ?_⟩
    rw [ha, hb, show (secondRingVertex i).val = (firstRingVertex i).val - basis j from hj]
    abel

theorem naturalRemoteRing_disjoint (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (i j : Fin 8) : naturalRemoteFirstRing t i ≠ naturalRemoteSecondRing t j := by
  intro h
  exact coordinatedRing_disjoint i j
    (natural_patchTranslate_injective_on t hrec
      (natural_firstRing_mem_patch i) (natural_secondRing_mem_patch j) h)

theorem naturalRemoteRing_matching (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (i j : Fin 8) (hne : i ≠ j) :
    naturalRemoteFirstRing t i ≠ naturalRemoteFirstRing t j ∧
    naturalRemoteSecondRing t i ≠ naturalRemoteSecondRing t j ∧
    naturalRemoteFirstRing t i ≠ naturalRemoteSecondRing t j ∧
    naturalRemoteSecondRing t i ≠ naturalRemoteFirstRing t j := by
  refine ⟨?_, ?_, naturalRemoteRing_disjoint t hrec i j,
    (naturalRemoteRing_disjoint t hrec j i).symm⟩
  · intro h
    exact hne (firstRing_injective (natural_patchTranslate_injective_on t hrec
      (natural_firstRing_mem_patch i) (natural_firstRing_mem_patch j) h))
  · intro h
    exact hne (secondRing_injective (natural_patchTranslate_injective_on t hrec
      (natural_secondRing_mem_patch i) (natural_secondRing_mem_patch j) h))

@[expose] def naturalRemoteOnsiteControl (t : Lattice) :
    TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  finiteSectorProjection (Finset.univ.image (naturalRemoteFirstRing t))

@[expose] def naturalRemoteEdge (t : Lattice) (i : Fin 8) :
    TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  InnerProductSpace.rankOne ℝ
    (infiniteEdgeVector (naturalRemoteFirstRing t i) (naturalRemoteSecondRing t i))
    (infiniteEdgeVector (naturalRemoteFirstRing t i) (naturalRemoteSecondRing t i))

@[expose] def naturalRemoteMatchingControl (t : Lattice) :
    TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  ∑ i : Fin 8, naturalRemoteEdge t i

theorem translateFiniteState_add (F : Finset Vertex) (t : Lattice)
    (x y : TileHilbert Vertex) :
    translateFiniteState F t (x + y) =
      translateFiniteState F t x + translateFiniteState F t y := by
  unfold translateFiniteState
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  change (x u + y u) • latticeSingle (u.val + t) =
    x u • latticeSingle (u.val + t) + y u • latticeSingle (u.val + t)
  rw [add_smul]

theorem translateFiniteState_sub (F : Finset Vertex) (t : Lattice)
    (x y : TileHilbert Vertex) :
    translateFiniteState F t (x - y) =
      translateFiniteState F t x - translateFiniteState F t y := by
  unfold translateFiniteState
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  change (x u - y u) • latticeSingle (u.val + t) =
    x u • latticeSingle (u.val + t) - y u • latticeSingle (u.val + t)
  rw [sub_smul]

theorem translateFiniteState_sum {ι : Type*} (F : Finset Vertex) (t : Lattice)
    (s : Finset ι) (f : ι → TileHilbert Vertex) :
    translateFiniteState F t (∑ i ∈ s, f i) =
      ∑ i ∈ s, translateFiniteState F t (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [translateFiniteState]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, translateFiniteState_add, ih]

theorem natural_translate_single (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (u : Vertex) (hu : u ∈ centralPatch) :
    translateFiniteState centralPatch t (lp.single (2 : ENNReal) u (1 : ℝ)) =
      lp.single (2 : ENNReal) (patchTranslateVertex t u) (1 : ℝ) := by
  unfold translateFiniteState
  rw [Finset.sum_eq_single_of_mem u hu]
  · simp only [lp.single_apply, Pi.single_apply, if_true, one_smul]
    apply lp.ext
    funext w
    rw [latticeSingle_apply, lp.single_apply, Pi.single_apply]
    have hv := patchTranslateVertex_val t u (central_recurrence_admitted t hrec u hu)
    have he : w.val = u.val + t ↔ w = patchTranslateVertex t u := by
      constructor
      · intro h
        exact Subtype.ext (h.trans hv.symm)
      · intro h
        rw [h, hv]
    simp [he, eq_comm]
  · intro w hw hwu
    simp [lp.single_apply, Pi.single_apply, hwu, Ne.symm hwu]

theorem natural_translate_edgeVector (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (i : Fin 8) :
    translateFiniteState centralPatch t
      (infiniteEdgeVector (firstRingVertex i) (secondRingVertex i)) =
      infiniteEdgeVector (naturalRemoteFirstRing t i) (naturalRemoteSecondRing t i) := by
  unfold infiniteEdgeVector
  rw [translateFiniteState_sub,
    natural_translate_single t hrec _ (natural_firstRing_mem_patch i),
    natural_translate_single t hrec _ (natural_secondRing_mem_patch i)] <;> rfl

theorem natural_edgeVector_supported (i : Fin 8) (w : Vertex) (hw : w ∉ centralPatch) :
    infiniteEdgeVector (firstRingVertex i) (secondRingVertex i) w = 0 := by
  have ha : w ≠ firstRingVertex i := fun h => hw (h.symm ▸ natural_firstRing_mem_patch i)
  have hb : w ≠ secondRingVertex i := fun h => hw (h.symm ▸ natural_secondRing_mem_patch i)
  simp [infiniteEdgeVector, lp.coeFn_sub, Pi.sub_apply, lp.single_apply,
    Pi.single_apply, ha, hb, Ne.symm ha, Ne.symm hb]

theorem naturalRemoteEdge_intertwines (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (i : Fin 8) (x : TileHilbert Vertex) (hx : ∀ w : Vertex, w ∉ centralPatch → x w = 0) :
    naturalRemoteEdge t i (translateFiniteState centralPatch t x) =
      translateFiniteState centralPatch t (coordinatedRingEdge i x) := by
  unfold naturalRemoteEdge coordinatedRingEdge
  rw [← natural_translate_edgeVector t hrec i]
  simp only [InnerProductSpace.rankOne_apply]
  rw [translateFiniteState_inner centralPatch t (central_recurrence_admitted t hrec)
      _ x (natural_edgeVector_supported i) hx, translateFiniteState_smul]

theorem naturalRemoteMatching_intertwines (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (x : TileHilbert Vertex) (hx : ∀ w : Vertex, w ∉ centralPatch → x w = 0) :
    naturalRemoteMatchingControl t (translateFiniteState centralPatch t x) =
      translateFiniteState centralPatch t (coordinatedRingControl x) := by
  rw [naturalRemoteMatchingControl, ContinuousLinearMap.sum_apply,
    coordinatedRingControl_apply, translateFiniteState_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact naturalRemoteEdge_intertwines t hrec i x hx

theorem naturalRemoteMatching_compactA (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) :
    naturalRemoteMatchingControl t (translatedCompactA t) =
      translatedCompactA t - translatedCompactB t := by
  change naturalRemoteMatchingControl t (translateFiniteState centralPatch t compactA) = _
  rw [naturalRemoteMatching_intertwines t hrec compactA compactA_supported_centralPatch,
    coordinatedRingControl_compactA, translateFiniteState_sub] <;> rfl

theorem naturalRemoteMatching_compactB (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) :
    naturalRemoteMatchingControl t (translatedCompactB t) =
      translatedCompactB t - translatedCompactA t := by
  change naturalRemoteMatchingControl t (translateFiniteState centralPatch t compactB) = _
  rw [naturalRemoteMatching_intertwines t hrec compactB compactB_supported_centralPatch,
    coordinatedRingControl_compactB, translateFiniteState_sub] <;> rfl

theorem naturalRemoteOnsite_compactA (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) :
    naturalRemoteOnsiteControl t (translatedCompactA t) = translatedCompactA t := by
  apply lp.ext
  funext w
  change finiteSectorProjection (Finset.univ.image (naturalRemoteFirstRing t))
    (translatedCompactA t) w = translatedCompactA t w
  rw [finiteSectorProjection_apply]
  split_ifs with hw
  · rfl
  · symm
    by_contra hn
    obtain ⟨u, hu, he⟩ := translateFiniteState_nonzero centralPatch t compactA w hn
    have hne : compactA u ≠ 0 := by
      intro hz
      apply hn
      rw [show translatedCompactA t w = compactA u from
        translateFiniteState_apply_supported centralPatch t compactA
          compactA_supported_centralPatch u w he, hz]
    obtain ⟨i, rfl⟩ := compactA_support hne
    apply hw
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ _, Subtype.ext ?_⟩
    exact (patchTranslateVertex_val t _ (central_recurrence_admitted t hrec _ hu)).trans he.symm

theorem naturalRemoteOnsite_compactB (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) :
    naturalRemoteOnsiteControl t (translatedCompactB t) = 0 := by
  apply lp.ext
  funext w
  change finiteSectorProjection (Finset.univ.image (naturalRemoteFirstRing t))
    (translatedCompactB t) w = 0
  rw [finiteSectorProjection_apply]
  split_ifs with hw
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    change translateFiniteState centralPatch t compactB (patchTranslateVertex t (firstRingVertex i)) = 0
    rw [translateFiniteState_apply_supported centralPatch t compactB compactB_supported_centralPatch
      (firstRingVertex i) _ (patchTranslateVertex_val t _
        (central_recurrence_admitted t hrec _ (natural_firstRing_mem_patch i)))]
    exact (coordinatedRing_amplitudes i).2.2
  · rfl

/-- Exact driven action on the full infinite space, at arbitrary real
control strengths. The rest drift is nondegenerate on the remote cell. -/
theorem naturalRemoteControls_pair_action (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (δ η a b : ℝ) :
    (canonicalPlateauHamiltonian + δ • naturalRemoteOnsiteControl v.val +
      η • naturalRemoteMatchingControl v.val)
      (a • translatedCompactA v.val + b • translatedCompactB v.val) =
    ((canonicalPlateauHeight + 3 / 16 + δ + η) * a - η * b) • translatedCompactA v.val +
      ((canonicalPlateauHeight + 1 / 4 + η) * b - η * a) • translatedCompactB v.val := by
  obtain ⟨ha, hb⟩ := naturalPlateauPair_eigenvectors v hr hrec
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    map_add, map_smul, ha, hb, naturalRemoteOnsite_compactA v.val hrec,
    naturalRemoteOnsite_compactB v.val hrec, naturalRemoteMatching_compactA v.val hrec,
    naturalRemoteMatching_compactB v.val hrec]
  module

end
end SpectralGeometry.AmmannBeenker
