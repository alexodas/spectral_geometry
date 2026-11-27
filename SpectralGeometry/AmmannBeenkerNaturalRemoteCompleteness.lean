module

public import SpectralGeometry.AmmannBeenkerNaturalCellCompleteness

public section

/-!
# Exact local completeness on remote natural plateau cells

Reverse translation is performed only on an admitted finite recurring
patch. The support and the boundary equations are transported back
to the original Laplacian cell, without global translation symmetry.
The central defect of the canonical plateau remains unchanged.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

@[expose] def naturalRemoteCell (t : Lattice) : Finset Vertex :=
  centralPatch.image (patchTranslateVertex t)

theorem naturalRemoteCell_mem_iff (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (w : Vertex) :
    w ∈ naturalRemoteCell t ↔ ∃ u ∈ centralPatch, w.val = u.val + t := by
  unfold naturalRemoteCell
  rw [Finset.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, patchTranslateVertex_val t u (central_recurrence_admitted t hrec u hu)⟩
  · rintro ⟨u, hu, he⟩
    refine ⟨u, hu, Subtype.ext ?_⟩
    rw [patchTranslateVertex_val t u (central_recurrence_admitted t hrec u hu), he]

theorem naturalRemoteCell_card (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) :
    (naturalRemoteCell t).card = 17 := by
  unfold naturalRemoteCell
  rw [← centralPatch_card]
  apply Finset.card_image_of_injOn
  intro u hu w hw he
  have h := congrArg (fun z : Vertex => z.val) he
  rw [patchTranslateVertex_val t u (central_recurrence_admitted t hrec u hu),
    patchTranslateVertex_val t w (central_recurrence_admitted t hrec w hw)] at h
  exact Subtype.ext (add_right_cancel h)

theorem naturalRemoteCell_disjoint_sector (v : Vertex)
    (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (w : Vertex) (hw : w ∈ sector) : w ∉ naturalRemoteCell v.val := by
  intro hm
  obtain ⟨u, hu, he⟩ := (naturalRemoteCell_mem_iff v.val hrec w).mp hm
  have hp : position w = position u + position v := by
    change physical w.val = physical u.val + physical v.val
    rw [he, physical_add]
  have hs : position v = position w - position u := by rw [hp]; ring
  have hb := norm_sub_le (position w) (position u)
  rw [← hs] at hb
  have hu' : u ∈ sector := by rwa [sector_eq_centralPatch]
  have hw' := (mem_sector w).mp hw
  have hu'' := (mem_sector u).mp hu'
  linarith

/-- Every supported remote state has a supported preimage under local translation. -/
theorem naturalRemoteCell_pullback (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (x : TileHilbert Vertex) (hx : ∀ w : Vertex, w ∉ naturalRemoteCell t → x w = 0) :
    ∃ y : TileHilbert Vertex,
      (∀ u : Vertex, u ∉ centralPatch → y u = 0) ∧
      translateFiniteState centralPatch t y = x := by
  let y := translateFiniteState (naturalRemoteCell t) (-t) x
  have hy (u : Vertex) (hu : u ∉ centralPatch) : y u = 0 := by
    by_contra hn
    obtain ⟨w, hw, he⟩ := translateFiniteState_nonzero (naturalRemoteCell t) (-t) x u hn
    obtain ⟨q, hq, hval⟩ := (naturalRemoteCell_mem_iff t hrec w).mp hw
    have h : u.val = q.val := by rw [he, hval]; abel
    exact hu (by rwa [show u = q from Subtype.ext h])
  refine ⟨y, hy, ?_⟩
  apply lp.ext
  funext w
  by_cases hw : w ∈ naturalRemoteCell t
  · obtain ⟨u, hu, he⟩ := (naturalRemoteCell_mem_iff t hrec w).mp hw
    rw [translateFiniteState_apply_supported centralPatch t y hy u w he]
    have hrev : u.val = w.val + -t := by rw [he]; abel
    exact translateFiniteState_apply_supported (naturalRemoteCell t) (-t) x hx w u hrev
  · rw [hx w hw]
    apply translateFiniteState_apply_zero
    intro u hu he
    exact hw ((naturalRemoteCell_mem_iff t hrec w).mpr ⟨u, hu, he⟩)

/-- A remote eigenvector pulls back to a full-graph eigenvector of L.
The proof explicitly includes the exterior neighbors of the original cell. -/
theorem naturalRemoteCell_pullback_eigenvector (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (y : TileHilbert Vertex) (hy : ∀ u : Vertex, u ∉ centralPatch → y u = 0)
    (c : ℝ)
    (he : interaction (translateFiniteState centralPatch t y) =
      c • translateFiniteState centralPatch t y) :
    interaction y = c • y := by
  apply lp.ext
  funext u
  change interaction y u = c * y u
  by_cases hu : u.val ∈ patchNeighborhoodLifts centralLifts
  · have hu' : u.val ∈ centralRecurrenceLifts := by
      exact mem_patchNeighborhoodLifts_self hu
    have ha : Admitted (u.val + t) := (hrec _ hu').mpr u.property
    let w := patchTranslateVertex t u
    have hv : w.val = u.val + t := patchTranslateVertex_val t u ha
    have h := congrArg (fun z : TileHilbert Vertex => z w) he
    change interaction (translateFiniteState centralPatch t y) w =
      c * translateFiniteState centralPatch t y w at h
    rw [translated_interaction_apply (patchNeighborhoodLifts centralLifts)
      centralPatch t hrec y hy u w hu hv,
      translateFiniteState_apply_supported centralPatch t y hy u w hv] at h
    exact h
  · have hzero : y u = 0 := hy u (fun h =>
      hu (mem_patchNeighborhoodLifts_self ((mem_centralPatch u).mp h)))
    have hn (w : Vertex) (hw : w ∈ neighbors u) : y w = 0 := by
      apply hy w
      intro hs
      have hwu : u ∈ neighbors w :=
        (mem_neighbors_iff w u).mpr (adjacent_symm ((mem_neighbors_iff u w).mp hw))
      exact hu (neighbor_lift_mem_patchNeighborhood ((mem_centralPatch w).mp hs) hwu)
    rw [interaction_apply, hzero, mul_zero]
    have hsum : (∑ w ∈ neighbors u, (0 - y w)) = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      rw [hn w hw, sub_zero]
    rw [hsum, mul_zero]

theorem translateFiniteState_smul (F : Finset Vertex) (t : Lattice)
    (a : ℝ) (x : TileHilbert Vertex) :
    translateFiniteState F t (a • x) = a • translateFiniteState F t x := by
  unfold translateFiniteState
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  change (a * x u) • latticeSingle (u.val + t) =
    a • (x u • latticeSingle (u.val + t))
  rw [mul_smul]

/-- All nonzero full-space Laplacian eigenvectors supported within an
admitted recurrent cell, at any energy. -/
theorem naturalRemoteCell_laplacian_classification (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (x : TileHilbert Vertex) (hx : ∀ w : Vertex, w ∉ naturalRemoteCell t → x w = 0)
    (c : ℝ) (he : interaction x = c • x) (hn : x ≠ 0) :
    (c = 3 / 16 ∧ ∃ a : ℝ, a ≠ 0 ∧ x = a • translatedCompactA t) ∨
      (c = 1 / 4 ∧ ∃ b : ℝ, b ≠ 0 ∧ x = b • translatedCompactB t) := by
  obtain ⟨y, hy, ht⟩ := naturalRemoteCell_pullback t hrec x hx
  have hyne : y ≠ 0 := by
    intro hz
    apply hn
    rw [← ht, hz]
    simp [translateFiniteState]
  have hys (u : Vertex) (hu : u ∉ sector) : y u = 0 := by
    apply hy u
    simpa [sector_eq_centralPatch] using hu
  have hye := naturalRemoteCell_pullback_eigenvector t hrec y hy c (by rw [ht]; exact he)
  rcases naturalCell_supported_eigenvector_classification y hys c hye hyne with
    ⟨hc, a, ha, hya⟩ | ⟨hc, b, hb, hyb⟩
  · exact Or.inl ⟨hc, a, ha, by
      rw [← ht, hya, translateFiniteState_smul]
      rfl⟩
  · exact Or.inr ⟨hc, b, hb, by
      rw [← ht, hyb, translateFiniteState_smul]
      rfl⟩

/-- The actual canonical plateau has exactly the two natural eigenvector
directions among states supported inside each remote recurrent cell. -/
theorem naturalRemoteCell_plateau_classification (v : Vertex)
    (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (x : TileHilbert Vertex)
    (hx : ∀ w : Vertex, w ∉ naturalRemoteCell v.val → x w = 0)
    (e : ℝ) (he : canonicalPlateauHamiltonian x = e • x) (hn : x ≠ 0) :
    (e = canonicalPlateauHeight + 3 / 16 ∧
      ∃ a : ℝ, a ≠ 0 ∧ x = a • translatedCompactA v.val) ∨
    (e = canonicalPlateauHeight + 1 / 4 ∧
      ∃ b : ℝ, b ≠ 0 ∧ x = b • translatedCompactB v.val) := by
  have hs (w : Vertex) (hw : w ∈ sector) : x w = 0 :=
    hx w (naturalRemoteCell_disjoint_sector v hr hrec w hw)
  rw [canonicalPlateau_eq_bulk_of_exterior_support x hs] at he
  have hl : interaction x = (e - canonicalPlateauHeight) • x := by
    change canonicalPlateauHeight • x + interaction x = e • x at he
    rw [sub_smul, eq_sub_iff_add_eq]
    simpa [add_comm] using he
  rcases naturalRemoteCell_laplacian_classification v.val hrec x hx
      (e - canonicalPlateauHeight) hl hn with ⟨h, a, ha, hxa⟩ | ⟨h, b, hb, hxb⟩
  · exact Or.inl ⟨by linarith, a, ha, hxa⟩
  · exact Or.inr ⟨by linarith, b, hb, hxb⟩

end
end SpectralGeometry.AmmannBeenker
