module

public import SpectralGeometry.AmmannBeenkerTranslatedModes

public section

/-!
# Exact inner products and finite families of replicated compact modes

On an admitted finite pattern, translation preserves the original
amplitudes and inner products of supported states. Different disjoint
translated patterns have mutually orthogonal states. These identities
combine with full-graph Laplacian transfer to give arbitrary finite
families of compact localized eigenstates on the same infinite graph.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

theorem translateFiniteState_zero (F : Finset Vertex) (x : TileHilbert Vertex)
    (hx : ∀ v : Vertex, v ∉ F → x v = 0) :
    translateFiniteState F 0 x = x := by
  apply lp.ext
  funext w
  exact translateFiniteState_apply_supported F 0 x hx w w (by simp)

/-- Inner product against an arbitrary state, evaluated at the translated
sites of an admitted finite pattern. -/
theorem inner_translateFiniteState (F : Finset Vertex) (t : Lattice)
    (ha : ∀ v ∈ F, Admitted (v.val + t)) (x y : TileHilbert Vertex) :
    inner ℝ (translateFiniteState F t x) y =
      ∑ v ∈ F, x v * y (patchTranslateVertex t v) := by
  classical
  simp only [translateFiniteState, sum_inner, real_inner_smul_left]
  apply Finset.sum_congr rfl
  intro v hv
  rw [inner_latticeSingle _ (ha v hv)]
  have he : latticeVertex (v.val + t) (ha v hv) = patchTranslateVertex t v :=
    Subtype.ext (patchTranslateVertex_val t v (ha v hv)).symm
  rw [he]

theorem inner_eq_sum_of_finite_support (F : Finset Vertex)
    (x y : TileHilbert Vertex) (hx : ∀ v : Vertex, v ∉ F → x v = 0) :
    inner ℝ x y = ∑ v ∈ F, x v * y v := by
  classical
  have ha (v : Vertex) (_ : v ∈ F) : Admitted (v.val + 0) := by
    simpa using v.property
  have h := inner_translateFiniteState F 0 ha x y
  rw [translateFiniteState_zero F x hx] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro v hv
  have he : patchTranslateVertex 0 v = v := by
    apply Subtype.ext
    rw [patchTranslateVertex_val 0 v (ha v hv), add_zero]
  rw [he]

/-- Finite supported states retain exactly their inner products. -/
theorem translateFiniteState_inner (F : Finset Vertex) (t : Lattice)
    (ha : ∀ v ∈ F, Admitted (v.val + t)) (x y : TileHilbert Vertex)
    (hx : ∀ v : Vertex, v ∉ F → x v = 0)
    (hy : ∀ v : Vertex, v ∉ F → y v = 0) :
    inner ℝ (translateFiniteState F t x) (translateFiniteState F t y) =
      inner ℝ x y := by
  rw [inner_translateFiniteState F t ha, inner_eq_sum_of_finite_support F x y hx]
  apply Finset.sum_congr rfl
  intro v hv
  rw [translateFiniteState_apply_supported F t y hy v
    (patchTranslateVertex t v) (patchTranslateVertex_val t v (ha v hv))]

/-- No amplitude overlap is possible for disjoint translated lift sets. -/
theorem translateFiniteState_inner_of_disjoint (F G : Finset Vertex)
    (t s : Lattice) (ha : ∀ v ∈ F, Admitted (v.val + t))
    (hdis : ∀ v ∈ F, ∀ w ∈ G, v.val + t ≠ w.val + s)
    (x y : TileHilbert Vertex) :
    inner ℝ (translateFiniteState F t x) (translateFiniteState G s y) = 0 := by
  rw [inner_translateFiniteState F t ha]
  apply Finset.sum_eq_zero
  intro v hv
  have hz : translateFiniteState G s y (patchTranslateVertex t v) = 0 := by
    apply translateFiniteState_apply_zero
    intro w hw
    rw [patchTranslateVertex_val t v (ha v hv)]
    exact hdis v hv w hw
  rw [hz, mul_zero]

set_option maxRecDepth 4096 in
theorem centralPatch_val_mem_recurrence (v : Vertex) (hv : v ∈ centralPatch) :
    v.val ∈ centralRecurrenceLifts := by
  have hcentral : v.val ∈ centralLifts := (mem_centralPatch v).mp hv
  exact centralLifts_mem_recurrence (n := v.val) hcentral

set_option maxRecDepth 4096 in
theorem central_recurrence_admitted (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (v : Vertex) (hv : v ∈ centralPatch) : Admitted (v.val + t) := by
  have hn : v.val ∈ centralRecurrenceLifts := centralPatch_val_mem_recurrence v hv
  exact (hrec v.val hn).mpr v.property

theorem compactA_supported_centralPatch (v : Vertex) (hv : v ∉ centralPatch) :
    compactA v = 0 := by
  apply compactA_eq_zero_of_not_ring
  intro i he
  apply hv
  rw [he, ← sector_eq_centralPatch]
  exact firstRing_mem_sector i

theorem compactB_supported_centralPatch (v : Vertex) (hv : v ∉ centralPatch) :
    compactB v = 0 := by
  apply compactB_eq_zero_of_not_ring
  intro i he
  apply hv
  rw [he, ← sector_eq_centralPatch]
  exact secondRing_mem_sector i

theorem translatedCompact_inner_products (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) :
    inner ℝ (translatedCompactA t) (translatedCompactA t) = 8 ∧
    inner ℝ (translatedCompactB t) (translatedCompactB t) = 8 ∧
    inner ℝ (translatedCompactA t) (translatedCompactB t) = 0 := by
  have ha := central_recurrence_admitted t hrec
  refine ⟨?_, ?_, ?_⟩
  · exact (translateFiniteState_inner centralPatch t ha compactA compactA
      compactA_supported_centralPatch compactA_supported_centralPatch).trans compactA_inner_self
  · exact (translateFiniteState_inner centralPatch t ha compactB compactB
      compactB_supported_centralPatch compactB_supported_centralPatch).trans compactB_inner_self
  · exact (translateFiniteState_inner centralPatch t ha compactA compactB
      compactA_supported_centralPatch compactB_supported_centralPatch).trans compactA_inner_compactB

/-- The support of any state translated from the central sector lies in
the translated central lift set. -/
theorem central_translate_support (t : Lattice) (x : TileHilbert Vertex)
    (w : Vertex) (hw : translateFiniteState centralPatch t x w ≠ 0) :
    ∃ n ∈ centralLifts, w.val = n + t := by
  obtain ⟨v, hv, he⟩ := translateFiniteState_nonzero centralPatch t x w hw
  exact ⟨v.val, (mem_centralPatch v).mp hv, he⟩

set_option maxRecDepth 4096 in
theorem central_translate_inner_of_disjoint (t s : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (hdis : ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
      n + t ≠ m + s) (x y : TileHilbert Vertex) :
    inner ℝ (translateFiniteState centralPatch t x)
      (translateFiniteState centralPatch s y) = 0 := by
  apply translateFiniteState_inner_of_disjoint centralPatch centralPatch t s
    (central_recurrence_admitted t hrec) _ x y
  intro v hv w hw
  have hv' : v.val ∈ centralRecurrenceLifts := centralPatch_val_mem_recurrence v hv
  have hw' : w.val ∈ centralRecurrenceLifts := centralPatch_val_mem_recurrence w hw
  exact hdis v.val hv' w.val hw'

/-- Arbitrarily many exact compact-mode pairs with complete disjoint
candidate neighborhoods, full-graph eigenvector equations and all
within-pair and cross-pair inner products. The two energies are those
of the graph Laplacian, not a degenerate or individually isolated
Hamiltonian level. -/
theorem exact_recurrent_compact_mode_pairs (R D : ℝ) (hD : 0 ≤ D) (N : ℕ) :
    ∃ S : Finset Vertex, S.card = N ∧
      (∀ v ∈ S, R < ‖position v‖ ∧
        (∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n) ∧
        interaction (translatedCompactA v.val) = (3 / 16 : ℝ) • translatedCompactA v.val ∧
        interaction (translatedCompactB v.val) = (1 / 4 : ℝ) • translatedCompactB v.val ∧
        inner ℝ (translatedCompactA v.val) (translatedCompactA v.val) = 8 ∧
        inner ℝ (translatedCompactB v.val) (translatedCompactB v.val) = 8 ∧
        inner ℝ (translatedCompactA v.val) (translatedCompactB v.val) = 0) ∧
      (∀ v ∈ S, ∀ w ∈ S, v ≠ w →
        D < dist (position v) (position w) ∧
        (∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
          n + v.val ≠ m + w.val) ∧
        inner ℝ (translatedCompactA v.val) (translatedCompactA w.val) = 0 ∧
        inner ℝ (translatedCompactA v.val) (translatedCompactB w.val) = 0 ∧
        inner ℝ (translatedCompactB v.val) (translatedCompactA w.val) = 0 ∧
        inner ℝ (translatedCompactB v.val) (translatedCompactB w.val) = 0) := by
  obtain ⟨S, hc, hp, hs⟩ := central_recurrence_disjoint_copies R D hD N
  refine ⟨S, hc, ?_, ?_⟩
  · intro v hv
    obtain ⟨hr, hrec⟩ := hp v hv
    obtain ⟨ha, hb, hab⟩ := translatedCompact_inner_products v.val hrec
    exact ⟨hr, hrec, translatedCompactA_eigenvector v.val hrec,
      translatedCompactB_eigenvector v.val hrec, ha, hb, hab⟩
  · intro v hv w hw hne
    obtain ⟨hd, hdis⟩ := hs v hv w hw hne
    have hrec := (hp v hv).2
    exact ⟨hd, hdis,
      central_translate_inner_of_disjoint v.val w.val hrec hdis compactA compactA,
      central_translate_inner_of_disjoint v.val w.val hrec hdis compactA compactB,
      central_translate_inner_of_disjoint v.val w.val hrec hdis compactB compactA,
      central_translate_inner_of_disjoint v.val w.val hrec hdis compactB compactB⟩

end
end SpectralGeometry.AmmannBeenker
