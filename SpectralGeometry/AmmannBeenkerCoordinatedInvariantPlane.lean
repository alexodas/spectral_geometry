module

public import SpectralGeometry.AmmannBeenkerCoordinatedRingControl
public import SpectralGeometry.AmmannBeenkerQubitLeakage

public section

/-!
# Exact coordinated control on the original crossing plane (L7a/L7b)

The full-space edge action is evaluated before restricting to the two-mode
coordinates. All Hamiltonian statements use the original natural domain.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped BigOperators Classical

/-- Evaluate the finite sum before doing any vertex-case simplification. -/
private theorem coordinatedRing_sum_eval (s : Finset (Fin 8))
    (x : TileHilbert Vertex) (v : Vertex) :
    (∑ i ∈ s, coordinatedRingEdge i x) v =
      ∑ i ∈ s, (coordinatedRingEdge i x) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, lp.coeFn_add, Pi.add_apply, ih]

private theorem coordinatedRing_edge_eval (i : Fin 8)
    (x : TileHilbert Vertex) (v : Vertex) :
    (coordinatedRingEdge i x) v =
      (x (firstRingVertex i) - x (secondRingVertex i)) *
        ((if v = firstRingVertex i then 1 else 0) -
          (if v = secondRingVertex i then 1 else 0)) := by
  rw [coordinatedRingEdge_apply]
  change (x (firstRingVertex i) - x (secondRingVertex i)) *
    infiniteEdgeVector (firstRingVertex i) (secondRingVertex i) v = _
  simp [infiniteEdgeVector, lp.coeFn_sub, Pi.sub_apply, lp.single_apply,
    Pi.single_apply, eq_comm]

private theorem coordinatedRing_first_eval (x : TileHilbert Vertex) (i : Fin 8) :
    (coordinatedRingControl x) (firstRingVertex i) =
      x (firstRingVertex i) - x (secondRingVertex i) := by
  rw [coordinatedRingControl_apply, coordinatedRing_sum_eval]
  rw [Finset.sum_eq_single i]
  · rw [coordinatedRing_edge_eval]
    simp [coordinatedRing_disjoint]
  · intro j _ hj
    have h := coordinatedRing_matching i j (Ne.symm hj)
    rw [coordinatedRing_edge_eval]
    simp [h.1, h.2.2.1]
  · simp

private theorem coordinatedRing_second_eval (x : TileHilbert Vertex) (i : Fin 8) :
    (coordinatedRingControl x) (secondRingVertex i) =
      x (secondRingVertex i) - x (firstRingVertex i) := by
  rw [coordinatedRingControl_apply, coordinatedRing_sum_eval]
  rw [Finset.sum_eq_single i]
  · rw [coordinatedRing_edge_eval]
    have h := (coordinatedRing_disjoint i i).symm
    simp [h] <;> ring
  · intro j _ hj
    have h := coordinatedRing_matching i j (Ne.symm hj)
    rw [coordinatedRing_edge_eval]
    simp [h.2.1, h.2.2.2]
  · simp

private theorem coordinatedRing_outside_eval (x : TileHilbert Vertex) (v : Vertex)
    (ha : ∀ i : Fin 8, v ≠ firstRingVertex i)
    (hb : ∀ i : Fin 8, v ≠ secondRingVertex i) :
    (coordinatedRingControl x) v = 0 := by
  rw [coordinatedRingControl_apply, coordinatedRing_sum_eval]
  apply Finset.sum_eq_zero
  intro i _
  rw [coordinatedRing_edge_eval]
  simp [ha i, hb i]

/-- Exact full-space action, not an identity for a compressed matrix.
The proof covers both rings and every vertex outside them. -/
theorem coordinatedRingControl_compactA :
    coordinatedRingControl compactA = compactA - compactB := by
  apply lp.ext
  funext v
  change (coordinatedRingControl compactA) v = compactA v - compactB v
  by_cases ha : ∃ i : Fin 8, v = firstRingVertex i
  · obtain ⟨i, rfl⟩ := ha
    rw [coordinatedRing_first_eval]
    obtain ⟨_, hA, hB⟩ := coordinatedRing_amplitudes i
    rw [hA, hB]
  · by_cases hb : ∃ i : Fin 8, v = secondRingVertex i
    · obtain ⟨i, rfl⟩ := hb
      rw [coordinatedRing_second_eval]
      obtain ⟨h, _, _⟩ := coordinatedRing_amplitudes i
      rw [h]
    · have hA : ∀ i : Fin 8, v ≠ firstRingVertex i :=
        fun i hi => ha ⟨i, hi⟩
      have hB : ∀ i : Fin 8, v ≠ secondRingVertex i :=
        fun i hi => hb ⟨i, hi⟩
      rw [coordinatedRing_outside_eval _ _ hA hB,
        compactA_eq_zero_of_not_ring _ hA, compactB_eq_zero_of_not_ring _ hB,
        sub_zero]

theorem coordinatedRingControl_compactB :
    coordinatedRingControl compactB = compactB - compactA := by
  apply lp.ext
  funext v
  change (coordinatedRingControl compactB) v = compactB v - compactA v
  by_cases ha : ∃ i : Fin 8, v = firstRingVertex i
  · obtain ⟨i, rfl⟩ := ha
    rw [coordinatedRing_first_eval]
    obtain ⟨h, _, _⟩ := coordinatedRing_amplitudes i
    rw [h]
  · by_cases hb : ∃ i : Fin 8, v = secondRingVertex i
    · obtain ⟨i, rfl⟩ := hb
      rw [coordinatedRing_second_eval]
      obtain ⟨_, hA, hB⟩ := coordinatedRing_amplitudes i
      rw [hA, hB]
    · have hA : ∀ i : Fin 8, v ≠ firstRingVertex i :=
        fun i hi => ha ⟨i, hi⟩
      have hB : ∀ i : Fin 8, v ≠ secondRingVertex i :=
        fun i hi => hb ⟨i, hi⟩
      rw [coordinatedRing_outside_eval _ _ hA hB,
        compactA_eq_zero_of_not_ring _ hA, compactB_eq_zero_of_not_ring _ hB,
        sub_zero]

theorem coordinatedRingControl_bright :
    coordinatedRingControl crossingBright = (2 : ℝ) • crossingBright := by
  simp only [crossingBright, map_smul, map_sub,
    coordinatedRingControl_compactA, coordinatedRingControl_compactB]
  module

theorem coordinatedRingControl_pair (r s : ℝ) :
    coordinatedRingControl (r • compactA + s • compactB) =
      (r - s) • compactA + (s - r) • compactB := by
  simp only [map_add, map_smul, coordinatedRingControl_compactA,
    coordinatedRingControl_compactB]
  module

/-- Q M P = 0 for the existing full-space orthogonal decomposition. -/
theorem coordinatedRingControl_offplane_zero (x : TileHilbert Vertex) :
    crossingLeakage (coordinatedRingControl (crossingQubitPart x)) = 0 := by
  rw [crossingQubitPart, coordinatedRingControl_pair]
  exact crossingLeakage_pair_zero _ _

/-- The two-control Hamiltonian preserves the original compact plane at
arbitrary real control strengths; the input lies in the natural domain. -/
theorem coordinatedControls_compact_action (δ η r s : ℝ) :
    onsitePlusBounded potential
      (ringInteraction (crossingParameter + δ) + η • coordinatedRingControl)
      (r • domainCompactA + s • domainCompactB) =
      ((crossingEnergy + δ + η) * r - η * s) • compactA +
      ((crossingEnergy + η) * s - η * r) • compactB := by
  have hdet := detuning_two_mode_action δ r s
  rw [onsitePlusBounded_apply] at hdet ⊢
  change infiniteOnsiteOperator potential
      (r • domainCompactA + s • domainCompactB) +
        ringInteraction (crossingParameter + δ)
          (r • compactA + s • compactB) = _ at hdet
  change infiniteOnsiteOperator potential
      (r • domainCompactA + s • domainCompactB) +
        (ringInteraction (crossingParameter + δ)
          (r • compactA + s • compactB) +
         η • coordinatedRingControl (r • compactA + s • compactB)) = _
  rw [← add_assoc, hdet, coordinatedRingControl_pair]
  module

theorem coordinatedControls_offplane_zero (δ η r s : ℝ) :
    crossingLeakage
      (onsitePlusBounded potential
        (ringInteraction (crossingParameter + δ) + η • coordinatedRingControl)
        (r • domainCompactA + s • domainCompactB)) = 0 := by
  rw [coordinatedControls_compact_action]
  exact crossingLeakage_pair_zero _ _

/-- Explicit natural-domain lift of the output. -/
theorem coordinatedControls_domain_invariant (δ η r s : ℝ) :
    onsitePlusBounded potential
      (ringInteraction (crossingParameter + δ) + η • coordinatedRingControl)
      (r • domainCompactA + s • domainCompactB) ∈
        infiniteOnsiteDomain potential := by
  rw [coordinatedControls_compact_action]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ compactA_mem_domain)
    (Submodule.smul_mem _ _ compactB_mem_domain)

/-- Exact restriction in the normalized dark/bright basis. The matrix
is [[E+δ/2, δ/2], [δ/2, E+δ/2+2η]], with no exterior term. -/
theorem coordinatedControls_dark_bright_action (δ η u v : ℝ) :
    onsitePlusBounded potential
      (ringInteraction (crossingParameter + δ) + η • coordinatedRingControl)
      (u • domainCrossingDark + v • domainCrossingBright) =
      ((crossingEnergy + δ / 2) * u + δ / 2 * v) • crossingDark +
      (δ / 2 * u + (crossingEnergy + δ / 2 + 2 * η) * v) • crossingBright := by
  have hinput :
      u • domainCrossingDark + v • domainCrossingBright =
        ((u + v) / 4) • domainCompactA +
        ((u - v) / 4) • domainCompactB := by
    simp only [domainCrossingDark, domainCrossingBright]
    module
  rw [hinput, coordinatedControls_compact_action]
  simp only [crossingDark, crossingBright]
  module

/-!
## L8a.1 — Sharp bounded control estimates

The local matching identities give a scaled orthogonal projection on
the whole real Hilbert space. The norm estimate does not sum eight
individual edge norms.
-/

/-- Disjoint matched endpoints imply the exact full-space quadratic
identity M² = 2M. -/
theorem coordinatedRingControl_sq_apply (x : TileHilbert Vertex) :
    coordinatedRingControl (coordinatedRingControl x) =
      (2 : ℝ) • coordinatedRingControl x := by
  apply lp.ext
  funext v
  change (coordinatedRingControl (coordinatedRingControl x)) v =
    (2 : ℝ) * (coordinatedRingControl x) v
  by_cases ha : ∃ i : Fin 8, v = firstRingVertex i
  · obtain ⟨i, rfl⟩ := ha
    rw [coordinatedRing_first_eval (coordinatedRingControl x) i,
      coordinatedRing_first_eval x i, coordinatedRing_second_eval x i]
    ring
  · by_cases hb : ∃ i : Fin 8, v = secondRingVertex i
    · obtain ⟨i, rfl⟩ := hb
      rw [coordinatedRing_second_eval (coordinatedRingControl x) i,
        coordinatedRing_second_eval x i, coordinatedRing_first_eval x i]
      ring
    · have hA : ∀ i : Fin 8, v ≠ firstRingVertex i :=
        fun i hi => ha ⟨i, hi⟩
      have hB : ∀ i : Fin 8, v ≠ secondRingVertex i :=
        fun i hi => hb ⟨i, hi⟩
      rw [coordinatedRing_outside_eval (coordinatedRingControl x) v hA hB,
        coordinatedRing_outside_eval x v hA hB, mul_zero]

/-- A sharp uniform matching bound, obtained from symmetry and M²=2M. -/
theorem coordinatedRingControl_norm_le_two : ‖coordinatedRingControl‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have hs : ‖coordinatedRingControl x‖ ^ 2 =
      2 * inner ℝ x (coordinatedRingControl x) := by
    rw [← real_inner_self_eq_norm_sq,
      ← coordinatedRingControl_symmetric x (coordinatedRingControl x),
      coordinatedRingControl_sq_apply, real_inner_smul_right]
  have hc := real_inner_le_norm x (coordinatedRingControl x)
  by_contra! hn
  have hp : 0 < ‖coordinatedRingControl x‖ :=
    lt_of_le_of_lt (mul_nonneg (by norm_num) (norm_nonneg x)) hn
  have ht := mul_lt_mul_of_pos_right hn hp
  nlinarith only [hs, hc, ht]

/-- The existing bright eigenvector attains the sharp bound. -/
theorem coordinatedRingControl_opNorm : ‖coordinatedRingControl‖ = 2 := by
  apply le_antisymm coordinatedRingControl_norm_le_two
  have h := ContinuousLinearMap.le_opNorm coordinatedRingControl crossingBright
  rw [coordinatedRingControl_bright, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))] at h
  have hp : 0 < ‖crossingBright‖ := by
    have hs := crossingBright_norm_sq
    have hn := norm_nonneg crossingBright
    by_contra! hz
    have he : ‖crossingBright‖ = 0 := le_antisymm hz hn
    rw [he] at hs
    norm_num at hs
  exact le_of_mul_le_mul_right h hp

/-- The first-ring onsite projection is a contraction, and compact A
attains its norm. -/
theorem coordinatedOnsiteProjection_opNorm :
    ‖finiteSectorProjection (neighbors origin)‖ = 1 := by
  apply le_antisymm (finiteSectorProjection_norm_le _)
  have h := ContinuousLinearMap.le_opNorm
    (finiteSectorProjection (neighbors origin)) compactA
  rw [projection_compactA] at h
  have hp : 0 < ‖compactA‖ := norm_pos_iff.mpr compactA_ne_zero
  apply le_of_mul_le_mul_right _ hp
  simpa only [one_mul] using h

/-- The change relative to zero controls, as a bounded full-space map. -/
@[expose] def coordinatedControlPerturbation (δ η : ℝ) :
    TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  δ • finiteSectorProjection (neighbors origin) + η • coordinatedRingControl

/-- Exact decomposition of the bounded interaction part. -/
theorem coordinatedControlCorrection_decomposition (δ η : ℝ) :
    ringInteraction (crossingParameter + δ) + η • coordinatedRingControl =
      ringInteraction crossingParameter + coordinatedControlPerturbation δ η := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ringInteraction, coordinatedControlPerturbation,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  module

/-- Exact decomposition of the full Hamiltonian on its unchanged
natural onsite domain. -/
theorem coordinatedControlHamiltonian_decomposition (δ η : ℝ)
    (x : infiniteOnsiteDomain potential) :
    onsitePlusBounded potential
      (ringInteraction (crossingParameter + δ) + η • coordinatedRingControl) x =
      onsitePlusBounded potential (ringInteraction crossingParameter) x +
        coordinatedControlPerturbation δ η (x : TileHilbert Vertex) := by
  rw [coordinatedControlCorrection_decomposition]
  simp only [onsitePlusBounded_apply, ContinuousLinearMap.add_apply]
  abel

/-- Conservative operator-norm bound for both independently signed controls. -/
theorem coordinatedControlPerturbation_norm_le (δ η : ℝ) :
    ‖coordinatedControlPerturbation δ η‖ ≤ |δ| + 2 * |η| := by
  unfold coordinatedControlPerturbation
  calc
    _ ≤ ‖δ • finiteSectorProjection (neighbors origin)‖ +
        ‖η • coordinatedRingControl‖ := norm_add_le _ _
    _ = |δ| + 2 * |η| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        coordinatedOnsiteProjection_opNorm, coordinatedRingControl_opNorm]
      ring

end
end SpectralGeometry.AmmannBeenker
