module

public import SpectralGeometry.AmmannBeenkerNaturalMultiplicity

public section

/-!
# Obstruction to individual spectral isolation on the natural plateau

For any prescribed recurring remote cell there are other exact cells
arbitrarily far away, with disjoint complete candidate neighborhoods.
The equal-energy eigenvectors of the other cells give exact nonzero
residual-kernel witnesses orthogonal to the original two-state plane.
This rules out an individual positive residual gap, not a collective
gap around either entire eigenspace.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

/-- Extend any prescribed center by a remote recurrence whose complete
candidate pattern is disjoint, at any requested separation. -/
theorem naturalRemoteCell_disjoint_partner (v : Vertex) (R D : ℝ) (hD : 0 ≤ D) :
    ∃ w : Vertex, R < ‖position w‖ ∧ 4 < ‖position w‖ ∧
      D < dist (position v) (position w) ∧
      (∀ n ∈ centralRecurrenceLifts, Admitted (n + w.val) ↔ Admitted n) ∧
      (∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
        n + v.val ≠ m + w.val) := by
  let r : ℝ := ∑ n ∈ centralRecurrenceLifts, ‖physical n‖
  have hnonneg : 0 ≤ r := Finset.sum_nonneg (fun n _ => norm_nonneg _)
  obtain ⟨w, hw, hrec⟩ := finite_pattern_recurrence centralRecurrenceLifts
    (max R 4 + ‖position v‖ + D + 2 * r)
  have htriangle : ‖position w‖ ≤ dist (position v) (position w) + ‖position v‖ := by
    simpa [dist_comm] using dist_triangle (position w) (position v) (0 : ℂ)
  have hR : R < ‖position w‖ := by
    linarith [le_max_left R 4, norm_nonneg (position v)]
  have h4 : 4 < ‖position w‖ := by
    linarith [le_max_right R 4, norm_nonneg (position v)]
  have hdist : D + 2 * r < dist (position v) (position w) := by
    linarith [le_max_right R 4]
  refine ⟨w, hR, h4, by linarith, hrec, ?_⟩
  intro n hn m hm
  have hn' : ‖physical n‖ ≤ r :=
    Finset.single_le_sum (fun a _ => norm_nonneg (physical a)) hn
  have hm' : ‖physical m‖ ≤ r :=
    Finset.single_le_sum (fun a _ => norm_nonneg (physical a)) hm
  exact separated_translated_lifts v w n m r hn' hm' (by linarith)

/-- The two equal-energy partners can be placed beyond any radius and
at any required nonnegative distance from the prescribed recurring cell. -/
theorem naturalPlateauPair_orthogonal_partners (v : Vertex)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (R D : ℝ) (hD : 0 ≤ D) :
    ∃ w : Vertex, R < ‖position w‖ ∧ 4 < ‖position w‖ ∧
      D < dist (position v) (position w) ∧
      (∀ n ∈ centralRecurrenceLifts, Admitted (n + w.val) ↔ Admitted n) ∧
      (∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
        n + v.val ≠ m + w.val) ∧
      canonicalPlateauHamiltonian (translatedCompactA w.val) =
        (canonicalPlateauHeight + 3 / 16) • translatedCompactA w.val ∧
      canonicalPlateauHamiltonian (translatedCompactB w.val) =
        (canonicalPlateauHeight + 1 / 4) • translatedCompactB w.val ∧
      inner ℝ (translatedCompactA w.val) (translatedCompactA w.val) = 8 ∧
      inner ℝ (translatedCompactB w.val) (translatedCompactB w.val) = 8 ∧
      inner ℝ (translatedCompactA v.val) (translatedCompactA w.val) = 0 ∧
      inner ℝ (translatedCompactA v.val) (translatedCompactB w.val) = 0 ∧
      inner ℝ (translatedCompactB v.val) (translatedCompactA w.val) = 0 ∧
      inner ℝ (translatedCompactB v.val) (translatedCompactB w.val) = 0 := by
  obtain ⟨w, hR, h4, hdist, hwrec, hdis⟩ :=
    naturalRemoteCell_disjoint_partner v R D hD
  obtain ⟨ha, hb⟩ := naturalPlateauPair_eigenvectors w h4 hwrec
  obtain ⟨hna, hnb, _⟩ := translatedCompact_inner_products w.val hwrec
  exact ⟨w, hR, h4, hdist, hwrec, hdis, ha, hb, hna, hnb,
    central_translate_inner_of_disjoint v.val w.val hrec hdis compactA compactA,
    central_translate_inner_of_disjoint v.val w.val hrec hdis compactA compactB,
    central_translate_inner_of_disjoint v.val w.val hrec hdis compactB compactA,
    central_translate_inner_of_disjoint v.val w.val hrec hdis compactB compactB⟩

/-- At both natural energies there is a nonzero exact eigenvector
orthogonal to both compact directions of any prescribed recurring cell. -/
theorem naturalPlateauPair_exterior_eigenvector (v : Vertex)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (e : ℝ) (he : e = canonicalPlateauHeight + 3 / 16 ∨
      e = canonicalPlateauHeight + 1 / 4) :
    ∃ x : TileHilbert Vertex, x ≠ 0 ∧
      canonicalPlateauHamiltonian x = e • x ∧
      inner ℝ (translatedCompactA v.val) x = 0 ∧
      inner ℝ (translatedCompactB v.val) x = 0 := by
  obtain ⟨w, _, _, _, _, _, ha, hb, hna, hnb, haa, hab, hba, hbb⟩ :=
    naturalPlateauPair_orthogonal_partners v hrec 0 0 le_rfl
  rcases he with rfl | rfl
  · refine ⟨translatedCompactA w.val, ?_, ha, haa, hba⟩
    intro hz
    rw [hz, inner_zero_left] at hna
    norm_num at hna
  · refine ⟨translatedCompactB w.val, ?_, hb, hab, hbb⟩
    intro hz
    rw [hz, inner_zero_left] at hnb
    norm_num at hnb

/-- No positive residual lower bound holds on the entire orthogonal
complement of a single natural two-state cell, at either of its energies. -/
theorem naturalPlateauPair_no_individual_residual_gap (v : Vertex)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (e g : ℝ) (he : e = canonicalPlateauHeight + 3 / 16 ∨
      e = canonicalPlateauHeight + 1 / 4) (hg : 0 < g) :
    ¬ (∀ x : TileHilbert Vertex,
      inner ℝ (translatedCompactA v.val) x = 0 →
      inner ℝ (translatedCompactB v.val) x = 0 →
      g * ‖x‖ ≤ ‖canonicalPlateauHamiltonian x - e • x‖) := by
  intro h
  obtain ⟨x, hx, hxe, ha, hb⟩ := naturalPlateauPair_exterior_eigenvector v hrec e he
  have hbad := h x ha hb
  rw [hxe, sub_self, norm_zero] at hbad
  exact (not_le_of_gt (mul_pos hg (norm_pos_iff.mpr hx))) hbad

end
end SpectralGeometry.AmmannBeenker
