module

public import SpectralGeometry.AmmannBeenkerPlateauBulk
public import SpectralGeometry.AmmannBeenkerReplicatedPairs

public section

/-!
# Natural compact pairs on the canonical plateau

The existing central defect is unchanged. A compact state supported
outside it sees the uniform bulk, so the two replicated Laplacian
energies are shifted by exactly the canonical plateau height.
The result concerns existence and orthogonality, not completeness of
the supported eigenvectors or spectral isolation.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

/-- The diagonal defect annihilates any state vanishing on the central sector. -/
theorem canonicalPlateauDefect_eq_zero_of_exterior_support
    (x : TileHilbert Vertex) (hx : ∀ v ∈ sector, x v = 0) :
    canonicalPlateauDefect x = 0 := by
  apply lp.ext
  funext v
  change canonicalPlateauDefect x v = 0
  by_cases hv : v ∈ sector
  · have hz := hx v hv
    change (plateauOnsite canonicalPlateauHeight
      (le_trans (by norm_num : (1 : ℝ) ≤ 5) canonicalPlateauHeight_ge_five) x v +
      (interaction x v + crossingParameter * finiteSectorProjection (neighbors origin) x v)) -
      (canonicalPlateauHeight * x v + interaction x v) = 0
    rw [plateauOnsite_apply, finiteSectorProjection_apply, hz]
    split_ifs <;> ring
  · exact canonicalPlateauDefect_zero_outside x v hv

/-- Exact full-space agreement with the uniform bulk on exterior-supported states. -/
theorem canonicalPlateau_eq_bulk_of_exterior_support
    (x : TileHilbert Vertex) (hx : ∀ v ∈ sector, x v = 0) :
    canonicalPlateauHamiltonian x = plateauBulk canonicalPlateauHeight x := by
  have h := canonicalPlateauDefect_eq_zero_of_exterior_support x hx
  change canonicalPlateauHamiltonian x - plateauBulk canonicalPlateauHeight x = 0 at h
  exact sub_eq_zero.mp h

theorem plateauBulk_eigenvector_of_interaction (C c : ℝ)
    (x : TileHilbert Vertex) (he : interaction x = c • x) :
    plateauBulk C x = (C + c) • x := by
  change C • x + interaction x = (C + c) • x
  rw [he, add_smul]

/-- Any exterior-supported Laplacian eigenvector keeps its shape and
acquires just the constant energy shift. -/
theorem canonicalPlateau_eigenvector_of_exterior_support
    (x : TileHilbert Vertex) (hx : ∀ v ∈ sector, x v = 0)
    (c : ℝ) (he : interaction x = c • x) :
    canonicalPlateauHamiltonian x = (canonicalPlateauHeight + c) • x := by
  rw [canonicalPlateau_eq_bulk_of_exterior_support x hx]
  exact plateauBulk_eigenvector_of_interaction _ _ x he

/-- A translated radius-two support with center farther than four from
the origin cannot intersect the central radius-two sector. -/
theorem central_translate_zero_on_sector (v : Vertex)
    (hr : 4 < ‖position v‖) (x : TileHilbert Vertex)
    (w : Vertex) (hw : w ∈ sector) :
    translateFiniteState centralPatch v.val x w = 0 := by
  by_contra hn
  obtain ⟨n, hn, he⟩ := central_translate_support v.val x w hn
  have hpos : position w = physical n + position v := by
    change physical w.val = physical n + physical v.val
    rw [he, physical_add]
  have hsub : position v = position w - physical n := by
    rw [hpos]
    ring
  have hb := norm_sub_le (position w) (physical n)
  rw [← hsub] at hb
  have hw' := (mem_sector w).mp hw
  have hn' := centralLifts_radius hn
  linarith

/-- The two natural plateau levels, common to every remote recurrent cell. -/
theorem naturalPlateauPair_eigenvectors (v : Vertex)
    (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n) :
    canonicalPlateauHamiltonian (translatedCompactA v.val) =
      (canonicalPlateauHeight + 3 / 16) • translatedCompactA v.val ∧
    canonicalPlateauHamiltonian (translatedCompactB v.val) =
      (canonicalPlateauHeight + 1 / 4) • translatedCompactB v.val := by
  constructor
  · exact canonicalPlateau_eigenvector_of_exterior_support
      (translatedCompactA v.val) (central_translate_zero_on_sector v hr compactA)
      (3 / 16) (translatedCompactA_eigenvector v.val hrec)
  · exact canonicalPlateau_eigenvector_of_exterior_support
      (translatedCompactB v.val) (central_translate_zero_on_sector v hr compactB)
      (1 / 4) (translatedCompactB_eigenvector v.val hrec)

theorem naturalPlateauPair_energy_difference :
    (canonicalPlateauHeight + 1 / 4) - (canonicalPlateauHeight + 3 / 16) =
      (1 / 16 : ℝ) := by ring

/-- Arbitrarily many orthogonal pairs for the actual canonical plateau,
with unchanged central defect and complete disjoint candidate neighborhoods. -/
theorem exact_recurrent_natural_plateau_pairs (R D : ℝ) (hD : 0 ≤ D) (N : ℕ) :
    ∃ S : Finset Vertex, S.card = N ∧
      (∀ v ∈ S, R < ‖position v‖ ∧ 4 < ‖position v‖ ∧
        (∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n) ∧
        canonicalPlateauHamiltonian (translatedCompactA v.val) =
          (canonicalPlateauHeight + 3 / 16) • translatedCompactA v.val ∧
        canonicalPlateauHamiltonian (translatedCompactB v.val) =
          (canonicalPlateauHeight + 1 / 4) • translatedCompactB v.val ∧
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
  obtain ⟨S, hc, hp, hs⟩ := exact_recurrent_compact_mode_pairs (max R 4) D hD N
  refine ⟨S, hc, ?_, hs⟩
  intro v hv
  obtain ⟨hr, hrec, _, _, ha, hb, hab⟩ := hp v hv
  have hrR : R < ‖position v‖ := lt_of_le_of_lt (le_max_left _ _) hr
  have hr4 : 4 < ‖position v‖ := lt_of_le_of_lt (le_max_right _ _) hr
  obtain ⟨heA, heB⟩ := naturalPlateauPair_eigenvectors v hr4 hrec
  exact ⟨hrR, hr4, hrec, heA, heB, ha, hb, hab⟩

end
end SpectralGeometry.AmmannBeenker
