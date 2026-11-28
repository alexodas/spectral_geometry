module

public import SpectralGeometry.AmmannBeenkerNaturalTwoCellPreparation

public section

/-!
# Simultaneous preparation of a finite family of natural cells

Orthogonality gives additive weights for a finite direct sum.
The same three unit-duration intervals suffice for any finite number
of selected disjoint recurrent cells, with independent parameters.
The full infinite operator is used on each open interval. The
endpoint phases are local phases, not necessarily a common scalar.
No tensor-product or arbitrary weak-control assertion is made.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

private theorem naturalFinite_norm_sq (S : Finset Vertex) (x : Vertex → TileHilbert Vertex)
    (ho : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → inner ℝ (x v) (x w) = 0) :
    ‖∑ v ∈ S, x v‖ ^ 2 = ∑ v ∈ S, ‖x v‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_eq_single_of_mem v hv]
  intro w hw hwv
  exact ho w hw v hv hwv

@[expose] def naturalFiniteReal (S : Finset Vertex) (c : Vertex → ℝ)
    (f : Vertex → ℝ → ℂ × ℂ) (τ : ℝ) : TileHilbert Vertex :=
  ∑ v ∈ S, c v • naturalStateReal v.val (f v τ)

@[expose] def naturalFiniteImag (S : Finset Vertex) (c : Vertex → ℝ)
    (f : Vertex → ℝ → ℂ × ℂ) (τ : ℝ) : TileHilbert Vertex :=
  ∑ v ∈ S, c v • naturalStateImag v.val (f v τ)

theorem naturalFinite_weight (S : Finset Vertex)
    (hp : ∀ v ∈ S, 4 < ‖position v‖ ∧
      ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (hd : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
        n + v.val ≠ m + w.val)
    (c : Vertex → ℝ) (f : Vertex → ℝ → ℂ × ℂ) (τ : ℝ) :
    ‖naturalFiniteReal S c f τ‖ ^ 2 + ‖naturalFiniteImag S c f τ‖ ^ 2 =
      ∑ v ∈ S, (c v) ^ 2 * naturalStateWeight v.val (f v τ) := by
  have hR : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      inner ℝ (c v • naturalStateReal v.val (f v τ))
        (c w • naturalStateReal w.val (f w τ)) = 0 := by
    intro v hv w hw hne
    have h : inner ℝ (naturalStateReal v.val (f v τ))
        (naturalStateReal w.val (f w τ)) = 0 :=
      naturalTwoState_cross_inner v w (hp v hv).2 (hd v hv w hw hne) _ _ _ _
    rw [real_inner_smul_left, real_inner_smul_right, h, mul_zero, mul_zero]
  have hI : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      inner ℝ (c v • naturalStateImag v.val (f v τ))
        (c w • naturalStateImag w.val (f w τ)) = 0 := by
    intro v hv w hw hne
    have h : inner ℝ (naturalStateImag v.val (f v τ))
        (naturalStateImag w.val (f w τ)) = 0 :=
      naturalTwoState_cross_inner v w (hp v hv).2 (hd v hv w hw hne) _ _ _ _
    rw [real_inner_smul_left, real_inner_smul_right, h, mul_zero, mul_zero]
  unfold naturalFiniteReal naturalFiniteImag
  rw [naturalFinite_norm_sq _ _ hR, naturalFinite_norm_sq _ _ hI, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [naturalStateWeight, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

private theorem naturalFinite_continuous_sum (S : Finset Vertex)
    (r : Vertex → ℝ → TileHilbert Vertex) (h : ∀ v ∈ S, Continuous (r v)) :
    Continuous (fun τ => ∑ v ∈ S, r v τ) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact continuous_const
  | @insert v S hv ih =>
    simp only [Finset.sum_insert hv]
    exact (h v (Finset.mem_insert_self _ _)).add
      (ih (fun w hw => h w (Finset.mem_insert_of_mem hw)))

theorem naturalFinite_continuous (S : Finset Vertex) (c : Vertex → ℝ)
    (f : Vertex → ℝ → ℂ × ℂ) (hf : ∀ v ∈ S, Continuous (f v)) :
    Continuous (naturalFiniteReal S c f) ∧ Continuous (naturalFiniteImag S c f) := by
  unfold naturalFiniteReal naturalFiniteImag
  constructor
  · apply naturalFinite_continuous_sum
    intro v hv
    have hc : Continuous (fun _ : ℝ => c v) := continuous_const
    apply hc.smul
    unfold naturalStateReal
    exact ((Complex.continuous_re.comp (hf v hv).fst).smul continuous_const).add
      ((Complex.continuous_re.comp (hf v hv).snd).smul continuous_const)
  · apply naturalFinite_continuous_sum
    intro v hv
    have hc : Continuous (fun _ : ℝ => c v) := continuous_const
    apply hc.smul
    unfold naturalStateImag
    exact ((Complex.continuous_im.comp (hf v hv).fst).smul continuous_const).add
      ((Complex.continuous_im.comp (hf v hv).snd).smul continuous_const)

private theorem naturalFinite_eval (S : Finset Vertex)
    (x : Vertex → TileHilbert Vertex) (u : Vertex) :
    (∑ v ∈ S, x v) u = ∑ v ∈ S, x v u := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert v S hv ih =>
    simp only [Finset.sum_insert hv, lp.coeFn_add, Pi.add_apply, ih]

theorem naturalFinite_support (S : Finset Vertex)
    (hp : ∀ v ∈ S, ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (c : Vertex → ℝ) (f : Vertex → ℝ → ℂ × ℂ) (τ : ℝ) (u : Vertex)
    (hu : ∀ v ∈ S, u ∉ naturalRemoteCell v.val) :
    naturalFiniteReal S c f τ u = 0 ∧ naturalFiniteImag S c f τ u = 0 := by
  unfold naturalFiniteReal naturalFiniteImag
  constructor
  · rw [naturalFinite_eval]
    apply Finset.sum_eq_zero
    intro v hv
    change c v * naturalStateReal v.val (f v τ) u = 0
    rw [(naturalState_support v.val (hp v hv) (f v τ) u (hu v hv)).1, mul_zero]
  · rw [naturalFinite_eval]
    apply Finset.sum_eq_zero
    intro v hv
    change c v * naturalStateImag v.val (f v τ) u = 0
    rw [(naturalState_support v.val (hp v hv) (f v τ) u (hu v hv)).2, mul_zero]

private theorem naturalFullSolvesAt_sum (H : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (S : Finset Vertex) (r i : Vertex → ℝ → TileHilbert Vertex) (τ : ℝ)
    (h : ∀ v ∈ S, naturalFullSolvesAt H (r v) (i v) τ) :
    naturalFullSolvesAt H (fun s => ∑ v ∈ S, r v s) (fun s => ∑ v ∈ S, i v s) τ := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, naturalFullSolvesAt, map_zero, neg_zero]
    exact ⟨hasDerivAt_const τ _, hasDerivAt_const τ _⟩
  | @insert v S hv ih =>
    simp only [Finset.sum_insert hv]
    exact naturalFullSolvesAt_add H _ _ _ _ τ
      (h v (Finset.mem_insert_self _ _))
      (ih (fun w hw => h w (Finset.mem_insert_of_mem hw)))

theorem naturalFinite_solvesAt (S : Finset Vertex)
    (hp : ∀ v ∈ S, 4 < ‖position v‖ ∧
      ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (hd : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
        n + v.val ≠ m + w.val)
    (δ η c : Vertex → ℝ) (f : Vertex → ℝ → ℂ × ℂ) (τ : ℝ)
    (hf : ∀ v ∈ S, naturalSolvesAt v.val (δ v) (η v) (f v) τ) :
    naturalFullSolvesAt (naturalFamilyHamiltonian S δ η)
      (naturalFiniteReal S c f) (naturalFiniteImag S c f) τ := by
  unfold naturalFiniteReal naturalFiniteImag
  apply naturalFullSolvesAt_sum
  intro v hv
  exact naturalFullSolvesAt_smul _ _ _ τ (c v)
    (naturalFamilySolvesAt_of_local S hp hd δ η v hv (f v) τ (hf v hv))

/-- Any finite disjoint family can prepare independently specified
normalized local targets in three shared intervals. The total weight
is one and every endpoint phase is retained separately. -/
theorem naturalFinite_exact_preparation (S : Finset Vertex)
    (hp : ∀ v ∈ S, 4 < ‖position v‖ ∧
      ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (hd : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
        n + v.val ≠ m + w.val)
    (c : Vertex → ℝ) (hc : (∑ v ∈ S, (c v) ^ 2) = 1)
    (a b : Vertex → ℂ) (hn : ∀ v ∈ S, ‖a v‖ ^ 2 + ‖b v‖ ^ 2 = 1) :
    ∃ p t q : Vertex → ℝ,
      let f := fun v => naturalProtocolPair (p v) (t v) (q v) (1,0)
      let z := fun v => coordinatedPhase (naturalProtocolAngle (p v) (t v) (q v))
      (∀ v ∈ S, 0 ≤ t v ∧ t v ≤ Real.pi / 2 ∧ ‖z v‖ = 1 ∧
        f v 0 = (1,0) ∧ f v 3 = (z v * a v,z v * b v)) ∧
      naturalFiniteReal S c f 0 = ∑ v ∈ S, c v • naturalRemoteDark v.val ∧
      naturalFiniteImag S c f 0 = 0 ∧
      Continuous (naturalFiniteReal S c f) ∧ Continuous (naturalFiniteImag S c f) ∧
      (∀ τ : ℝ, ‖naturalFiniteReal S c f τ‖ ^ 2 + ‖naturalFiniteImag S c f τ‖ ^ 2 = 1) ∧
      (∀ τ : ℝ, ∀ u : Vertex, (∀ v ∈ S, u ∉ naturalRemoteCell v.val) →
        naturalFiniteReal S c f τ u = 0 ∧ naturalFiniteImag S c f τ u = 0) ∧
      (∀ τ : ℝ, 0 < τ → τ < 1 →
        naturalFullSolvesAt (naturalFamilyHamiltonian S (fun _ => 1 / 16) p)
          (naturalFiniteReal S c f) (naturalFiniteImag S c f) τ) ∧
      (∀ τ : ℝ, 1 < τ → τ < 2 →
        naturalFullSolvesAt (naturalFamilyHamiltonian S (fun v => 1 / 16 + -2 * t v) (fun _ => 0))
          (naturalFiniteReal S c f) (naturalFiniteImag S c f) τ) ∧
      (∀ τ : ℝ, 2 < τ → τ < 3 →
        naturalFullSolvesAt (naturalFamilyHamiltonian S (fun _ => 1 / 16) q)
          (naturalFiniteReal S c f) (naturalFiniteImag S c f) τ) := by
  have hex : ∀ v : Vertex, ∃ p t q : ℝ, v ∈ S →
      0 ≤ t ∧ t ≤ Real.pi / 2 ∧ naturalProtocolPair p t q (1,0) 3 =
        (coordinatedPhase (naturalProtocolAngle p t q) * a v,
          coordinatedPhase (naturalProtocolAngle p t q) * b v) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨p,t,q,h0,h1,he⟩ := naturalProtocol_reaches_from_dark (a v) (b v) (hn v hv)
      exact ⟨p,t,q,fun _ => ⟨h0,h1,he⟩⟩
    · exact ⟨0,0,0,fun h => (hv h).elim⟩
  choose p t q h using hex
  refine ⟨p,t,q,?_⟩
  dsimp only
  have hcont := naturalFinite_continuous S c
    (fun v => naturalProtocolPair (p v) (t v) (q v) (1,0))
    (fun v _ => naturalProtocol_continuous (p v) (t v) (q v) (1,0))
  refine ⟨?_, ?_, ?_, hcont.1, hcont.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨h0,h1,he⟩ := h v hv
    exact ⟨h0,h1,naturalProtocolPhase_norm _ _ _,
      naturalProtocol_initial _ _ _ _,he⟩
  · unfold naturalFiniteReal
    apply Finset.sum_congr rfl
    intro v hv
    change c v • naturalStateReal v.val (naturalProtocolPair (p v) (t v) (q v) (1,0) 0) =
      c v • naturalRemoteDark v.val
    rw [naturalProtocol_initial, (naturalState_dark_initial v.val).1]
  · unfold naturalFiniteImag
    apply Finset.sum_eq_zero
    intro v hv
    change c v • naturalStateImag v.val (naturalProtocolPair (p v) (t v) (q v) (1,0) 0) = 0
    rw [naturalProtocol_initial, (naturalState_dark_initial v.val).2, smul_zero]
  · intro τ
    rw [naturalFinite_weight S hp hd]
    calc
      _ = ∑ v ∈ S, (c v) ^ 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [naturalProtocol_dark_weight v.val (hp v hv).2, mul_one]
      _ = 1 := hc
  · intro τ u hu
    exact naturalFinite_support S (fun v hv => (hp v hv).2) c _ τ u hu
  · intro τ h0 h1
    apply naturalFinite_solvesAt S hp hd
    intro v hv
    exact naturalProtocol_solves_first v (hp v hv).1 (hp v hv).2
      (p v) (t v) (q v) (1,0) h0 h1
  · intro τ h1 h2
    apply naturalFinite_solvesAt S hp hd
    intro v hv
    exact naturalProtocol_solves_second v (hp v hv).1 (hp v hv).2
      (p v) (t v) (q v) (1,0) h1 h2
  · intro τ h2 h3
    apply naturalFinite_solvesAt S hp hd
    intro v hv
    exact naturalProtocol_solves_third v (hp v hv).1 (hp v hv).2
      (p v) (t v) (q v) (1,0) h2 h3

end
end SpectralGeometry.AmmannBeenker
