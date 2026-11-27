module

public import SpectralGeometry.AmmannBeenkerPatchRecurrence
public import SpectralGeometry.AmmannBeenkerCentralPatch

public section

/-!
# Complete candidate neighborhoods for recurring compact patches

A finite lift set is enlarged by every signed coordinate step, whether
admitted or excluded. Repeating the enlargement captures the neighbors
of the neighbors. Exact recurrence of this larger pattern provides a
bijection of complete graph neighborhoods, independently of edge colors.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- Include the original lifts and all eight candidate neighbors of each. -/
@[expose] def patchNeighborhoodLifts (F : Finset Lattice) : Finset Lattice := by
  classical
  exact F ∪ F.biUnion (fun n =>
    (Finset.univ.image (fun i : Fin 4 => n + basis i)) ∪
    (Finset.univ.image (fun i : Fin 4 => n - basis i)))

theorem mem_patchNeighborhoodLifts_self {F : Finset Lattice} {n : Lattice}
    (hn : n ∈ F) : n ∈ patchNeighborhoodLifts F := by
  classical
  exact Finset.mem_union_left _ hn

theorem mem_patchNeighborhoodLifts_add {F : Finset Lattice} {n : Lattice}
    (hn : n ∈ F) (i : Fin 4) : n + basis i ∈ patchNeighborhoodLifts F := by
  classical
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨n, hn, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩

theorem mem_patchNeighborhoodLifts_sub {F : Finset Lattice} {n : Lattice}
    (hn : n ∈ F) (i : Fin 4) : n - basis i ∈ patchNeighborhoodLifts F := by
  classical
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨n, hn, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩

theorem neighbor_lift_mem_patchNeighborhood {F : Finset Lattice} {v w : Vertex}
    (hv : v.val ∈ F) (hw : w ∈ neighbors v) :
    w.val ∈ patchNeighborhoodLifts F := by
  rcases (mem_neighbors_iff v w).mp hw with ⟨i, hi | hi⟩
  · rw [hi]
    exact mem_patchNeighborhoodLifts_add hv i
  · rw [hi]
    exact mem_patchNeighborhoodLifts_sub hv i

/-- Complete neighbor correspondence, not just preservation of edges between
already selected sites. All candidate lifts must have their membership preserved. -/
theorem translated_neighbors_exact (F : Finset Lattice) (t : Lattice)
    (hrec : ∀ n ∈ patchNeighborhoodLifts F, Admitted (n + t) ↔ Admitted n)
    (v v' : Vertex) (hv : v.val ∈ F) (hv' : v'.val = v.val + t)
    (w' : Vertex) :
    w' ∈ neighbors v' ↔ ∃ w ∈ neighbors v, w'.val = w.val + t := by
  constructor
  · intro hw
    rcases (mem_neighbors_iff v' w').mp hw with ⟨i, hi | hi⟩
    · have he : w'.val = (v.val + basis i) + t := by
        rw [hi, hv']
        abel
      have ha : Admitted (v.val + basis i) :=
        (hrec _ (mem_patchNeighborhoodLifts_add hv i)).mp (he ▸ w'.property)
      let w : Vertex := ⟨v.val + basis i, ha⟩
      exact ⟨w, (mem_neighbors_iff v w).mpr ⟨i, Or.inl rfl⟩, he⟩
    · have he : w'.val = (v.val - basis i) + t := by
        rw [hi, hv']
        abel
      have ha : Admitted (v.val - basis i) :=
        (hrec _ (mem_patchNeighborhoodLifts_sub hv i)).mp (he ▸ w'.property)
      let w : Vertex := ⟨v.val - basis i, ha⟩
      exact ⟨w, (mem_neighbors_iff v w).mpr ⟨i, Or.inr rfl⟩, he⟩
  · rintro ⟨w, hw, he⟩
    apply (mem_neighbors_iff v' w').mpr
    rcases (mem_neighbors_iff v w).mp hw with ⟨i, hi | hi⟩
    · refine ⟨i, Or.inl ?_⟩
      rw [he, hv', hi]
      abel
    · refine ⟨i, Or.inr ?_⟩
      rw [he, hv', hi]
      abel

/-- A concrete finite pattern containing the central sector and every
candidate lift within two signed coordinate steps of it. -/
@[expose] def centralRecurrenceLifts : Finset Lattice :=
  patchNeighborhoodLifts (patchNeighborhoodLifts centralLifts)

set_option maxRecDepth 4096 in
theorem centralLifts_mem_recurrence {n : Lattice} (hn : n ∈ centralLifts) :
    n ∈ centralRecurrenceLifts := by
  have hinner : n ∈ patchNeighborhoodLifts centralLifts :=
    mem_patchNeighborhoodLifts_self (F := centralLifts) (n := n) hn
  change n ∈ patchNeighborhoodLifts (patchNeighborhoodLifts centralLifts)
  exact mem_patchNeighborhoodLifts_self
    (F := patchNeighborhoodLifts centralLifts) (n := n) hinner

/-- On each of the central vertices and its actual neighbors the complete
neighbor correspondence follows from recurrence of the concrete pattern. -/
theorem central_recurrence_neighbors_exact (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (v v' : Vertex) (hv : v.val ∈ patchNeighborhoodLifts centralLifts)
    (hv' : v'.val = v.val + t) (w' : Vertex) :
    w' ∈ neighbors v' ↔ ∃ w ∈ neighbors v, w'.val = w.val + t :=
  translated_neighbors_exact (patchNeighborhoodLifts centralLifts) t hrec v v' hv hv' w'

/-- Arbitrarily many disjoint copies of the complete concrete candidate
neighborhood pattern, with centers arbitrarily far away. -/
theorem central_recurrence_disjoint_copies (R D : ℝ) (hD : 0 ≤ D) (N : ℕ) :
    ∃ S : Finset Vertex, S.card = N ∧
      (∀ v ∈ S, R < ‖position v‖ ∧
        ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n) ∧
      (∀ v ∈ S, ∀ w ∈ S, v ≠ w →
        D < dist (position v) (position w) ∧
          ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
            n + v.val ≠ m + w.val) :=
  finite_pattern_disjoint_copies centralRecurrenceLifts R D hD N

end
end SpectralGeometry.AmmannBeenker
