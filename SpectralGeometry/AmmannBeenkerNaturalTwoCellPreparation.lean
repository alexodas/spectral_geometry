module

public import SpectralGeometry.AmmannBeenkerNaturalFamilyDynamics

public section

/-!
# Simultaneous exact preparation in two orthogonal natural planes

Two independently specified normalized local targets are attained in
the same three unit-duration intervals. The full graph trajectory
is a weighted direct sum, normalized by c²+d²=1. The two scalar
phases are retained separately; they need not agree. This is not a
tensor-product two-qubit register and does not assert entangling gates.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

theorem naturalTwoState_cross_inner (v w : Vertex)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (hdis : ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
      n + v.val ≠ m + w.val)
    (a b c d : ℝ) :
    inner ℝ (a • naturalRemoteDark v.val + b • naturalRemoteBright v.val)
      (c • naturalRemoteDark w.val + d • naturalRemoteBright w.val) = 0 := by
  have hAA : inner ℝ (translatedCompactA v.val) (translatedCompactA w.val) = 0 :=
    central_translate_inner_of_disjoint v.val w.val hrec hdis compactA compactA
  have hAB : inner ℝ (translatedCompactA v.val) (translatedCompactB w.val) = 0 :=
    central_translate_inner_of_disjoint v.val w.val hrec hdis compactA compactB
  have hBA : inner ℝ (translatedCompactB v.val) (translatedCompactA w.val) = 0 :=
    central_translate_inner_of_disjoint v.val w.val hrec hdis compactB compactA
  have hBB : inner ℝ (translatedCompactB v.val) (translatedCompactB w.val) = 0 :=
    central_translate_inner_of_disjoint v.val w.val hrec hdis compactB compactB
  simp only [naturalRemoteDark, naturalRemoteBright, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    hAA, hAB, hBA, hBB]
  ring

private theorem naturalWeighted_norm_sq (x y : TileHilbert Vertex)
    (hxy : inner ℝ x y = 0) (c d : ℝ) :
    ‖c • x + d • y‖ ^ 2 = c ^ 2 * ‖x‖ ^ 2 + d ^ 2 * ‖y‖ ^ 2 := by
  have hyx : inner ℝ y x = 0 := by rw [real_inner_comm, hxy]
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hxy, hyx]
  ring

@[expose] def naturalTwoReal (v w : Vertex) (c d : ℝ)
    (f g : ℝ → ℂ × ℂ) (τ : ℝ) : TileHilbert Vertex :=
  c • naturalStateReal v.val (f τ) + d • naturalStateReal w.val (g τ)

@[expose] def naturalTwoImag (v w : Vertex) (c d : ℝ)
    (f g : ℝ → ℂ × ℂ) (τ : ℝ) : TileHilbert Vertex :=
  c • naturalStateImag v.val (f τ) + d • naturalStateImag w.val (g τ)

theorem naturalTwo_weight (v w : Vertex)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (hdis : ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
      n + v.val ≠ m + w.val)
    (c d : ℝ) (f g : ℝ → ℂ × ℂ) (τ : ℝ) :
    ‖naturalTwoReal v w c d f g τ‖ ^ 2 + ‖naturalTwoImag v w c d f g τ‖ ^ 2 =
      c ^ 2 * naturalStateWeight v.val (f τ) + d ^ 2 * naturalStateWeight w.val (g τ) := by
  have hR : inner ℝ (naturalStateReal v.val (f τ)) (naturalStateReal w.val (g τ)) = 0 :=
    naturalTwoState_cross_inner v w hrec hdis _ _ _ _
  have hI : inner ℝ (naturalStateImag v.val (f τ)) (naturalStateImag w.val (g τ)) = 0 :=
    naturalTwoState_cross_inner v w hrec hdis _ _ _ _
  unfold naturalTwoReal naturalTwoImag naturalStateWeight
  rw [naturalWeighted_norm_sq _ _ hR, naturalWeighted_norm_sq _ _ hI]
  ring

theorem naturalTwo_continuous (v w : Vertex) (c d : ℝ)
    (f g : ℝ → ℂ × ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (naturalTwoReal v w c d f g) ∧
    Continuous (naturalTwoImag v w c d f g) := by
  have hR (u : Vertex) (k : ℝ → ℂ × ℂ) (hk : Continuous k) :
      Continuous (fun s => naturalStateReal u.val (k s)) := by
    unfold naturalStateReal
    exact ((Complex.continuous_re.comp hk.fst).smul continuous_const).add
      ((Complex.continuous_re.comp hk.snd).smul continuous_const)
  have hI (u : Vertex) (k : ℝ → ℂ × ℂ) (hk : Continuous k) :
      Continuous (fun s => naturalStateImag u.val (k s)) := by
    unfold naturalStateImag
    exact ((Complex.continuous_im.comp hk.fst).smul continuous_const).add
      ((Complex.continuous_im.comp hk.snd).smul continuous_const)
  unfold naturalTwoReal naturalTwoImag
  have hc : Continuous (fun _ : ℝ => c) := continuous_const
  have hd : Continuous (fun _ : ℝ => d) := continuous_const
  constructor
  · exact (hc.smul (hR v f hf)).add (hd.smul (hR w g hg))
  · exact (hc.smul (hI v f hf)).add (hd.smul (hI w g hg))

theorem naturalTwo_support (v w : Vertex)
    (hvrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (hwrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + w.val) ↔ Admitted n)
    (c d : ℝ) (f g : ℝ → ℂ × ℂ) (τ : ℝ) (u : Vertex)
    (hv : u ∉ naturalRemoteCell v.val) (hw : u ∉ naturalRemoteCell w.val) :
    naturalTwoReal v w c d f g τ u = 0 ∧ naturalTwoImag v w c d f g τ u = 0 := by
  obtain ⟨hvR, hvI⟩ := naturalState_support v.val hvrec (f τ) u hv
  obtain ⟨hwR, hwI⟩ := naturalState_support w.val hwrec (g τ) u hw
  constructor
  · change c * naturalStateReal v.val (f τ) u + d * naturalStateReal w.val (g τ) u = 0
    rw [hvR, hwR]
    ring
  · change c * naturalStateImag v.val (f τ) u + d * naturalStateImag w.val (g τ) u = 0
    rw [hvI, hwI]
    ring

set_option backward.isDefEq.respectTransparency false in
theorem naturalFullSolvesAt_smul (H : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (r i : ℝ → TileHilbert Vertex) (τ c : ℝ)
    (h : naturalFullSolvesAt H r i τ) :
    naturalFullSolvesAt H (fun s => c • r s) (fun s => c • i s) τ := by
  unfold naturalFullSolvesAt at h ⊢
  constructor
  · rw [map_smul]
    first
    | exact h.1.fun_const_smul c
    | exact h.1.const_smul c
  · rw [map_smul, ← smul_neg]
    first
    | exact h.2.fun_const_smul c
    | exact h.2.const_smul c

theorem naturalTwo_solvesAt (S : Finset Vertex)
    (hp : ∀ v ∈ S, 4 < ‖position v‖ ∧
      ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (hd : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
        n + v.val ≠ m + w.val)
    (δ η : Vertex → ℝ) (v w : Vertex) (hv : v ∈ S) (hw : w ∈ S)
    (c d : ℝ) (f g : ℝ → ℂ × ℂ) (τ : ℝ)
    (hf : naturalSolvesAt v.val (δ v) (η v) f τ)
    (hg : naturalSolvesAt w.val (δ w) (η w) g τ) :
    naturalFullSolvesAt (naturalFamilyHamiltonian S δ η)
      (naturalTwoReal v w c d f g) (naturalTwoImag v w c d f g) τ := by
  have hV := naturalFamilySolvesAt_of_local S hp hd δ η v hv f τ hf
  have hW := naturalFamilySolvesAt_of_local S hp hd δ η w hw g τ hg
  exact naturalFullSolvesAt_add _ _ _ _ _ _
    (naturalFullSolvesAt_smul _ _ _ τ c hV)
    (naturalFullSolvesAt_smul _ _ _ τ d hW)

/-- Three common time intervals suffice for two independent target
pairs. Each local endpoint phase is explicitly retained. -/
theorem naturalTwo_exact_preparation (S : Finset Vertex)
    (hp : ∀ v ∈ S, 4 < ‖position v‖ ∧
      ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (hd : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
        n + v.val ≠ m + w.val)
    (v w : Vertex) (hv : v ∈ S) (hw : w ∈ S) (hne : v ≠ w)
    (c d : ℝ) (hcd : c ^ 2 + d ^ 2 = 1)
    (a b e k : ℂ) (hab : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (hek : ‖e‖ ^ 2 + ‖k‖ ^ 2 = 1) :
    ∃ p t q : Vertex → ℝ,
      (0 ≤ t v ∧ t v ≤ Real.pi / 2) ∧ (0 ≤ t w ∧ t w ≤ Real.pi / 2) ∧
      let f := naturalProtocolPair (p v) (t v) (q v) (1,0)
      let g := naturalProtocolPair (p w) (t w) (q w) (1,0)
      let z := coordinatedPhase (naturalProtocolAngle (p v) (t v) (q v))
      let u := coordinatedPhase (naturalProtocolAngle (p w) (t w) (q w))
      ‖z‖ = 1 ∧ ‖u‖ = 1 ∧
      f 0 = (1,0) ∧ g 0 = (1,0) ∧
      f 3 = (z*a,z*b) ∧ g 3 = (u*e,u*k) ∧
      naturalTwoReal v w c d f g 0 = c • naturalRemoteDark v.val + d • naturalRemoteDark w.val ∧
      naturalTwoImag v w c d f g 0 = 0 ∧
      Continuous (naturalTwoReal v w c d f g) ∧
      Continuous (naturalTwoImag v w c d f g) ∧
      (∀ τ : ℝ, ‖naturalTwoReal v w c d f g τ‖ ^ 2 +
        ‖naturalTwoImag v w c d f g τ‖ ^ 2 = 1) ∧
      (∀ τ : ℝ, ∀ x : Vertex, x ∉ naturalRemoteCell v.val → x ∉ naturalRemoteCell w.val →
        naturalTwoReal v w c d f g τ x = 0 ∧ naturalTwoImag v w c d f g τ x = 0) ∧
      (∀ τ : ℝ, 0 < τ → τ < 1 →
        naturalFullSolvesAt (naturalFamilyHamiltonian S (fun _ => 1 / 16) p)
          (naturalTwoReal v w c d f g) (naturalTwoImag v w c d f g) τ) ∧
      (∀ τ : ℝ, 1 < τ → τ < 2 →
        naturalFullSolvesAt (naturalFamilyHamiltonian S (fun x => 1 / 16 + -2 * t x) (fun _ => 0))
          (naturalTwoReal v w c d f g) (naturalTwoImag v w c d f g) τ) ∧
      (∀ τ : ℝ, 2 < τ → τ < 3 →
        naturalFullSolvesAt (naturalFamilyHamiltonian S (fun _ => 1 / 16) q)
          (naturalTwoReal v w c d f g) (naturalTwoImag v w c d f g) τ) := by
  obtain ⟨pv,tv,qv,hv0,hv1,hvend⟩ := naturalProtocol_reaches_from_dark a b hab
  obtain ⟨pw,tw,qw,hw0,hw1,hwend⟩ := naturalProtocol_reaches_from_dark e k hek
  let p : Vertex → ℝ := fun x => if x = v then pv else pw
  let t : Vertex → ℝ := fun x => if x = v then tv else tw
  let q : Vertex → ℝ := fun x => if x = v then qv else qw
  have hpv : p v = pv := by simp [p]
  have htv : t v = tv := by simp [t]
  have hqv : q v = qv := by simp [q]
  have hpw : p w = pw := by simp [p, hne.symm]
  have htw : t w = tw := by simp [t, hne.symm]
  have hqw : q w = qw := by simp [q, hne.symm]
  refine ⟨p,t,q,?_,?_,?_⟩
  · rw [htv]
    exact ⟨hv0,hv1⟩
  · rw [htw]
    exact ⟨hw0,hw1⟩
  · dsimp only
    have hf0 := naturalProtocol_initial (p v) (t v) (q v) (1,0)
    have hg0 := naturalProtocol_initial (p w) (t w) (q w) (1,0)
    have hc := naturalTwo_continuous v w c d _ _
      (naturalProtocol_continuous (p v) (t v) (q v) (1,0))
      (naturalProtocol_continuous (p w) (t w) (q w) (1,0))
    refine ⟨naturalProtocolPhase_norm _ _ _, naturalProtocolPhase_norm _ _ _,
      hf0, hg0, ?_, ?_, ?_, ?_, hc.1, hc.2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpv, htv, hqv]
      exact hvend
    · rw [hpw, htw, hqw]
      exact hwend
    · unfold naturalTwoReal
      rw [hf0, hg0, (naturalState_dark_initial v.val).1, (naturalState_dark_initial w.val).1]
    · unfold naturalTwoImag
      rw [hf0, hg0, (naturalState_dark_initial v.val).2, (naturalState_dark_initial w.val).2,
        smul_zero, smul_zero, add_zero]
    · intro τ
      rw [naturalTwo_weight v w (hp v hv).2 (hd v hv w hw hne),
        naturalProtocol_dark_weight v.val (hp v hv).2,
        naturalProtocol_dark_weight w.val (hp w hw).2, mul_one, mul_one]
      exact hcd
    · intro τ x hxv hxw
      exact naturalTwo_support v w (hp v hv).2 (hp w hw).2 c d _ _ τ x hxv hxw
    · intro τ h0 h1
      exact naturalTwo_solvesAt S hp hd (fun _ => 1 / 16) p v w hv hw c d _ _ τ
        (naturalProtocol_solves_first v (hp v hv).1 (hp v hv).2 (p v) (t v) (q v) (1,0) h0 h1)
        (naturalProtocol_solves_first w (hp w hw).1 (hp w hw).2 (p w) (t w) (q w) (1,0) h0 h1)
    · intro τ h1 h2
      exact naturalTwo_solvesAt S hp hd (fun x => 1 / 16 + -2 * t x) (fun _ => 0)
        v w hv hw c d _ _ τ
        (naturalProtocol_solves_second v (hp v hv).1 (hp v hv).2 (p v) (t v) (q v) (1,0) h1 h2)
        (naturalProtocol_solves_second w (hp w hw).1 (hp w hw).2 (p w) (t w) (q w) (1,0) h1 h2)
    · intro τ h2 h3
      exact naturalTwo_solvesAt S hp hd (fun _ => 1 / 16) q v w hv hw c d _ _ τ
        (naturalProtocol_solves_third v (hp v hv).1 (hp v hv).2 (p v) (t v) (q v) (1,0) h2 h3)
        (naturalProtocol_solves_third w (hp w hw).1 (hp w hw).2 (p w) (t w) (q w) (1,0) h2 h3)

end
end SpectralGeometry.AmmannBeenker
