module

public import SpectralGeometry.AmmannBeenkerNaturalControlSelectivity

public section

/-!
# Sharp norms of local controls on recurring cells

Disjoint matched edges yield the full-space identity M² = 2M.
The bounds are attained on compact states and are independent of the
cell position. A separate algebraic compensation of the natural
splitting prepares the next dynamical step without any gap assumption.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

theorem naturalRemoteMatching_apply (t : Lattice) (x : TileHilbert Vertex) :
    naturalRemoteMatchingControl t x = ∑ i : Fin 8, naturalRemoteEdge t i x := by
  simp only [naturalRemoteMatchingControl, ContinuousLinearMap.sum_apply]

private theorem naturalRemote_sum_eval (t : Lattice) (s : Finset (Fin 8))
    (x : TileHilbert Vertex) (v : Vertex) :
    (∑ i ∈ s, naturalRemoteEdge t i x) v =
      ∑ i ∈ s, (naturalRemoteEdge t i x) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, lp.coeFn_add, Pi.add_apply, ih]

private theorem naturalRemote_edge_eval (t : Lattice) (i : Fin 8)
    (x : TileHilbert Vertex) (v : Vertex) :
    (naturalRemoteEdge t i x) v =
      (x (naturalRemoteFirstRing t i) - x (naturalRemoteSecondRing t i)) *
        ((if v = naturalRemoteFirstRing t i then 1 else 0) -
          (if v = naturalRemoteSecondRing t i then 1 else 0)) := by
  rw [naturalRemoteEdge_apply t]
  change (x (naturalRemoteFirstRing t i) - x (naturalRemoteSecondRing t i)) *
    infiniteEdgeVector (naturalRemoteFirstRing t i) (naturalRemoteSecondRing t i) v = _
  simp [infiniteEdgeVector, lp.coeFn_sub, Pi.sub_apply, lp.single_apply,
    Pi.single_apply, eq_comm]

private theorem naturalRemote_first_eval (t : Lattice) (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) (x : TileHilbert Vertex) (i : Fin 8) :
    (naturalRemoteMatchingControl t x) (naturalRemoteFirstRing t i) =
      x (naturalRemoteFirstRing t i) - x (naturalRemoteSecondRing t i) := by
  rw [naturalRemoteMatching_apply t, naturalRemote_sum_eval t]
  rw [Finset.sum_eq_single i]
  · rw [naturalRemote_edge_eval t]
    simp [naturalRemoteRing_disjoint t hrec]
  · intro j _ hj
    have h := naturalRemoteRing_matching t hrec i j (Ne.symm hj)
    rw [naturalRemote_edge_eval t]
    simp [h.1, h.2.2.1]
  · simp

private theorem naturalRemote_second_eval (t : Lattice) (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) (x : TileHilbert Vertex) (i : Fin 8) :
    (naturalRemoteMatchingControl t x) (naturalRemoteSecondRing t i) =
      x (naturalRemoteSecondRing t i) - x (naturalRemoteFirstRing t i) := by
  rw [naturalRemoteMatching_apply t, naturalRemote_sum_eval t]
  rw [Finset.sum_eq_single i]
  · rw [naturalRemote_edge_eval t]
    have h := (naturalRemoteRing_disjoint t hrec i i).symm
    simp [h] <;> ring
  · intro j _ hj
    have h := naturalRemoteRing_matching t hrec i j (Ne.symm hj)
    rw [naturalRemote_edge_eval t]
    simp [h.2.1, h.2.2.2]
  · simp

private theorem naturalRemote_outside_eval (t : Lattice) (x : TileHilbert Vertex) (v : Vertex)
    (ha : ∀ i : Fin 8, v ≠ naturalRemoteFirstRing t i)
    (hb : ∀ i : Fin 8, v ≠ naturalRemoteSecondRing t i) :
    (naturalRemoteMatchingControl t x) v = 0 := by
  rw [naturalRemoteMatching_apply t, naturalRemote_sum_eval t]
  apply Finset.sum_eq_zero
  intro i _
  rw [naturalRemote_edge_eval t]
  simp [ha i, hb i]


theorem naturalRemoteMatching_sq_apply (t : Lattice) (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) (x : TileHilbert Vertex) :
    naturalRemoteMatchingControl t (naturalRemoteMatchingControl t x) =
      (2 : ℝ) • naturalRemoteMatchingControl t x := by
  apply lp.ext
  funext v
  change (naturalRemoteMatchingControl t (naturalRemoteMatchingControl t x)) v =
    (2 : ℝ) * (naturalRemoteMatchingControl t x) v
  by_cases ha : ∃ i : Fin 8, v = naturalRemoteFirstRing t i
  · obtain ⟨i, rfl⟩ := ha
    rw [naturalRemote_first_eval t hrec (naturalRemoteMatchingControl t x) i,
      naturalRemote_first_eval t hrec x i, naturalRemote_second_eval t hrec x i]
    ring
  · by_cases hb : ∃ i : Fin 8, v = naturalRemoteSecondRing t i
    · obtain ⟨i, rfl⟩ := hb
      rw [naturalRemote_second_eval t hrec (naturalRemoteMatchingControl t x) i,
        naturalRemote_second_eval t hrec x i, naturalRemote_first_eval t hrec x i]
      ring
    · have hA : ∀ i : Fin 8, v ≠ naturalRemoteFirstRing t i :=
        fun i hi => ha ⟨i, hi⟩
      have hB : ∀ i : Fin 8, v ≠ naturalRemoteSecondRing t i :=
        fun i hi => hb ⟨i, hi⟩
      rw [naturalRemote_outside_eval t (naturalRemoteMatchingControl t x) v hA hB,
        naturalRemote_outside_eval t x v hA hB, mul_zero]

/-- A sharp uniform matching bound, obtained from symmetry and M²=2M. -/
theorem naturalRemoteMatching_norm_le_two (t : Lattice) (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) : ‖naturalRemoteMatchingControl t‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have hs : ‖naturalRemoteMatchingControl t x‖ ^ 2 =
      2 * inner ℝ x (naturalRemoteMatchingControl t x) := by
    rw [← real_inner_self_eq_norm_sq,
      naturalRemoteMatching_symmetric t x (naturalRemoteMatchingControl t x),
      naturalRemoteMatching_sq_apply t hrec, real_inner_smul_right]
  have hc := real_inner_le_norm x (naturalRemoteMatchingControl t x)
  by_contra! hn
  have hp : 0 < ‖naturalRemoteMatchingControl t x‖ :=
    lt_of_le_of_lt (mul_nonneg (by norm_num) (norm_nonneg x)) hn
  have ht := mul_lt_mul_of_pos_right hn hp
  nlinarith only [hs, hc, ht]


theorem naturalRemoteMatching_difference (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) :
    naturalRemoteMatchingControl t (translatedCompactA t - translatedCompactB t) =
      (2 : ℝ) • (translatedCompactA t - translatedCompactB t) := by
  simp only [map_sub, naturalRemoteMatching_compactA t hrec,
    naturalRemoteMatching_compactB t hrec]
  module

theorem naturalRemoteMatching_opNorm (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) :
    ‖naturalRemoteMatchingControl t‖ = 2 := by
  apply le_antisymm (naturalRemoteMatching_norm_le_two t hrec)
  have h := ContinuousLinearMap.le_opNorm (naturalRemoteMatchingControl t)
    (translatedCompactA t - translatedCompactB t)
  rw [naturalRemoteMatching_difference t hrec, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))] at h
  obtain ⟨ha, _, hab⟩ := translatedCompact_inner_products t hrec
  have hn : translatedCompactA t - translatedCompactB t ≠ 0 := by
    intro hz
    have he := sub_eq_zero.mp hz
    rw [he] at ha
    rw [he] at hab
    linarith
  exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hn)

theorem naturalRemoteOnsite_opNorm (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) :
    ‖naturalRemoteOnsiteControl t‖ = 1 := by
  apply le_antisymm (finiteSectorProjection_norm_le _)
  have h := ContinuousLinearMap.le_opNorm (naturalRemoteOnsiteControl t) (translatedCompactA t)
  rw [naturalRemoteOnsite_compactA t hrec] at h
  obtain ⟨ha, _, _⟩ := translatedCompact_inner_products t hrec
  have hn : translatedCompactA t ≠ 0 := by
    intro hz
    rw [hz, inner_zero_left] at ha
    norm_num at ha
  apply le_of_mul_le_mul_right _ (norm_pos_iff.mpr hn)
  simpa only [one_mul] using h

theorem naturalRemotePerturbation_norm_le (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) (δ η : ℝ) :
    ‖naturalRemotePerturbation t δ η‖ ≤ |δ| + 2 * |η| := by
  unfold naturalRemotePerturbation
  calc
    _ ≤ ‖δ • naturalRemoteOnsiteControl t‖ + ‖η • naturalRemoteMatchingControl t‖ :=
      norm_add_le _ _
    _ = |δ| + 2 * |η| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        naturalRemoteOnsite_opNorm t hrec, naturalRemoteMatching_opNorm t hrec]
      ring

/-- Detuning by the natural splitting compensates the two diagonal
energies. The additional detuning d and edge amplitude η then recover
the original degenerate control matrix, at the new common energy. -/
theorem naturalRemote_compensated_pair_action (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (d η a b : ℝ) :
    (canonicalPlateauHamiltonian + (1 / 16 + d) • naturalRemoteOnsiteControl v.val +
      η • naturalRemoteMatchingControl v.val)
      (a • translatedCompactA v.val + b • translatedCompactB v.val) =
      ((canonicalPlateauHeight + 1 / 4 + d + η) * a - η * b) • translatedCompactA v.val +
      ((canonicalPlateauHeight + 1 / 4 + η) * b - η * a) • translatedCompactB v.val := by
  rw [naturalRemoteControls_pair_action v hr hrec]
  module

end
end SpectralGeometry.AmmannBeenker
