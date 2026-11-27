module

public import SpectralGeometry.AmmannBeenkerPatchNeighborhood

public section

/-!
# Full-graph transfer of finitely supported states to recurring patches

Translation is a finite sum of actual site vectors. No global translation
automorphism is assumed. Recurrence of the two-step candidate pattern
identifies the complete neighborhoods of the support and its boundary,
so the full Laplacian equation can be transported, including exterior
cancellation and vertices outside the translated neighborhood.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

/-- A translated coordinate denotes a vertex when admitted. The fallback
is irrelevant on the recurring finite neighborhood and is never used
as a global graph symmetry. -/
@[expose] def patchTranslateVertex (t : Lattice) (v : Vertex) : Vertex :=
  if h : Admitted (v.val + t) then ⟨v.val + t, h⟩ else v

theorem patchTranslateVertex_val (t : Lattice) (v : Vertex)
    (h : Admitted (v.val + t)) : (patchTranslateVertex t v).val = v.val + t := by
  simp [patchTranslateVertex, h]

/-- Translate the amplitudes on a finite set, with zero amplitude elsewhere. -/
@[expose] def translateFiniteState (F : Finset Vertex) (t : Lattice)
    (x : TileHilbert Vertex) : TileHilbert Vertex :=
  ∑ v ∈ F, x v • latticeSingle (v.val + t)

theorem translateFiniteState_apply (F : Finset Vertex) (t : Lattice)
    (x : TileHilbert Vertex) (w : Vertex) :
    translateFiniteState F t x w =
      ∑ v ∈ F, x v * (if w.val = v.val + t then 1 else 0) := by
  simp only [translateFiniteState, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, latticeSingle_apply]

theorem translateFiniteState_apply_zero (F : Finset Vertex) (t : Lattice)
    (x : TileHilbert Vertex) (w : Vertex)
    (h : ∀ v ∈ F, w.val ≠ v.val + t) : translateFiniteState F t x w = 0 := by
  rw [translateFiniteState_apply]
  apply Finset.sum_eq_zero
  intro v hv
  simp [h v hv]

theorem translateFiniteState_apply_at (F : Finset Vertex) (t : Lattice)
    (x : TileHilbert Vertex) (v w : Vertex) (he : w.val = v.val + t) :
    translateFiniteState F t x w = if v ∈ F then x v else 0 := by
  classical
  have hne (u : Vertex) (hu : u ≠ v) : w.val ≠ u.val + t := by
    intro h
    apply hu
    apply Subtype.ext
    exact add_right_cancel (h.symm.trans he)
  by_cases hv : v ∈ F
  · rw [translateFiniteState_apply, if_pos hv]
    rw [Finset.sum_eq_single_of_mem v hv]
    · simp [he]
    · intro u hu huv
      simp [hne u huv]
  · rw [if_neg hv]
    apply translateFiniteState_apply_zero
    intro u hu
    exact hne u (fun h => hv (h ▸ hu))

theorem translateFiniteState_apply_supported (F : Finset Vertex) (t : Lattice)
    (x : TileHilbert Vertex) (hx : ∀ v : Vertex, v ∉ F → x v = 0)
    (v w : Vertex) (he : w.val = v.val + t) :
    translateFiniteState F t x w = x v := by
  rw [translateFiniteState_apply_at F t x v w he]
  by_cases hv : v ∈ F
  · simp [hv]
  · simp [hv, hx v hv]

theorem translateFiniteState_nonzero (F : Finset Vertex) (t : Lattice)
    (x : TileHilbert Vertex) (w : Vertex) (hw : translateFiniteState F t x w ≠ 0) :
    ∃ v ∈ F, w.val = v.val + t := by
  classical
  by_contra h
  apply hw
  apply translateFiniteState_apply_zero
  intro v hv he
  exact h ⟨v, hv, he⟩

/-- The complete neighbor set is the image of the original neighbor set
under the admitted local translation. -/
theorem translated_neighbors_image (F : Finset Lattice) (t : Lattice)
    (hrec : ∀ n ∈ patchNeighborhoodLifts F, Admitted (n + t) ↔ Admitted n)
    (v v' : Vertex) (hv : v.val ∈ F) (hv' : v'.val = v.val + t) :
    neighbors v' = (neighbors v).image (patchTranslateVertex t) := by
  classical
  have ha (w : Vertex) (hw : w ∈ neighbors v) : Admitted (w.val + t) :=
    (hrec _ (neighbor_lift_mem_patchNeighborhood hv hw)).mpr w.property
  ext w'
  rw [translated_neighbors_exact F t hrec v v' hv hv' w', Finset.mem_image]
  constructor
  · rintro ⟨w, hw, he⟩
    refine ⟨w, hw, Subtype.ext ?_⟩
    rw [patchTranslateVertex_val t w (ha w hw), he]
  · rintro ⟨w, hw, he⟩
    refine ⟨w, hw, ?_⟩
    rw [← he, patchTranslateVertex_val t w (ha w hw)]

set_option maxHeartbeats 2000000 in
/-- Local Laplacian equality at every translated vertex whose original
complete neighborhood is certified. -/
theorem translated_interaction_apply (F : Finset Lattice) (P : Finset Vertex)
    (t : Lattice)
    (hrec : ∀ n ∈ patchNeighborhoodLifts F, Admitted (n + t) ↔ Admitted n)
    (x : TileHilbert Vertex) (hx : ∀ v : Vertex, v ∉ P → x v = 0)
    (v v' : Vertex) (hv : v.val ∈ F) (hv' : v'.val = v.val + t) :
    interaction (translateFiniteState P t x) v' = interaction x v := by
  classical
  have ha (w : Vertex) (hw : w ∈ neighbors v) : Admitted (w.val + t) :=
    (hrec _ (neighbor_lift_mem_patchNeighborhood hv hw)).mpr w.property
  have hval (w : Vertex) (hw : w ∈ neighbors v) :
      (patchTranslateVertex t w).val = w.val + t :=
    patchTranslateVertex_val t w (ha w hw)
  have hvc := translateFiniteState_apply_supported P t x hx v v' hv'
  rw [interaction_apply, interaction_apply, hvc,
    translated_neighbors_image F t hrec v v' hv hv']
  rw [Finset.sum_image]
  · have hs :
        (∑ w ∈ neighbors v, (x v - translateFiniteState P t x (patchTranslateVertex t w))) =
          ∑ w ∈ neighbors v, (x v - x w) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [translateFiniteState_apply_supported P t x hx w
        (patchTranslateVertex t w) (hval w hw)]
    exact congrArg (fun a : ℝ => (1 / 16 : ℝ) * a) hs
  · intro a ha' b hb' he
    have h := congrArg (fun w : Vertex => w.val) he
    rw [hval a ha', hval b hb'] at h
    exact Subtype.ext (add_right_cancel h)

/-- On the concrete central pattern, the full Laplacian eigenvector equation
is invariant under any recurring translation, for every state supported on
the central sector. No hypothesis of global graph periodicity is used. -/
theorem central_translate_eigenvector (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (x : TileHilbert Vertex) (hx : ∀ v : Vertex, v ∉ centralPatch → x v = 0)
    (c : ℝ) (heig : interaction x = c • x) :
    interaction (translateFiniteState centralPatch t x) =
      c • translateFiniteState centralPatch t x := by
  classical
  apply lp.ext
  funext w
  change interaction (translateFiniteState centralPatch t x) w =
    c * translateFiniteState centralPatch t x w
  by_cases hw : ∃ v : Vertex, v.val ∈ patchNeighborhoodLifts centralLifts ∧
      w.val = v.val + t
  · obtain ⟨v, hv, hval⟩ := hw
    rw [translated_interaction_apply (patchNeighborhoodLifts centralLifts)
      centralPatch t hrec x hx v w hv hval,
      translateFiniteState_apply_supported centralPatch t x hx v w hval]
    have h := congrArg (fun z : TileHilbert Vertex => z v) heig
    exact h
  · have hzero : translateFiniteState centralPatch t x w = 0 := by
      apply translateFiniteState_apply_zero
      intro v hv he
      exact hw ⟨v, mem_patchNeighborhoodLifts_self ((mem_centralPatch v).mp hv), he⟩
    have hnzero (u : Vertex) (hu : u ∈ neighbors w) :
        translateFiniteState centralPatch t x u = 0 := by
      by_contra hn
      obtain ⟨v, hv, he⟩ := translateFiniteState_nonzero centralPatch t x u hn
      have hvL : v.val ∈ centralLifts := (mem_centralPatch v).mp hv
      have hv' : v.val ∈ patchNeighborhoodLifts centralLifts :=
        mem_patchNeighborhoodLifts_self hvL
      have hwu : w ∈ neighbors u :=
        (mem_neighbors_iff u w).mpr (adjacent_symm ((mem_neighbors_iff w u).mp hu))
      obtain ⟨z, hz, hzval⟩ :=
        (central_recurrence_neighbors_exact t hrec v u hv' he w).mp hwu
      exact hw ⟨z, neighbor_lift_mem_patchNeighborhood hvL hz, hzval⟩
    rw [interaction_apply, hzero, mul_zero]
    have hs : (∑ u ∈ neighbors w, (0 - translateFiniteState centralPatch t x u)) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [hnzero u hu, sub_zero]
    rw [hs, mul_zero]

/-- The actual central alternating modes, translated into the recurring patch. -/
@[expose] def translatedCompactA (t : Lattice) : TileHilbert Vertex :=
  translateFiniteState centralPatch t compactA

@[expose] def translatedCompactB (t : Lattice) : TileHilbert Vertex :=
  translateFiniteState centralPatch t compactB

theorem translatedCompactA_eigenvector (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) :
    interaction (translatedCompactA t) = (3 / 16 : ℝ) • translatedCompactA t := by
  apply central_translate_eigenvector t hrec compactA
  · intro v hv
    apply compactA_eq_zero_of_not_ring
    intro i he
    apply hv
    rw [he, ← sector_eq_centralPatch]
    exact firstRing_mem_sector i
  · exact interaction_compactA

theorem translatedCompactB_eigenvector (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) :
    interaction (translatedCompactB t) = (1 / 4 : ℝ) • translatedCompactB t := by
  apply central_translate_eigenvector t hrec compactB
  · intro v hv
    apply compactB_eq_zero_of_not_ring
    intro i he
    apply hv
    rw [he, ← sector_eq_centralPatch]
    exact secondRing_mem_sector i
  · simpa only [show (4 / 16 : ℝ) = 1 / 4 by norm_num] using interaction_compactB

end
end SpectralGeometry.AmmannBeenker
