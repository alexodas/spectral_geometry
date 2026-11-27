module

public import SpectralGeometry.AmmannBeenkerNaturalPairDynamics

public section

/-!
# Continuous compensated remote pulse protocol

The coefficient pair is expressed in the normalized remote dark/bright
basis. The common physical energy is C+1/4, and onsite detuning
includes the natural splitting 1/16 during each pulse. The local
clocks compose three unit-duration segments continuously. Both real
Hilbert components satisfy the actual bounded graph equations on
the open pulse intervals and remain supported on the remote cell.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open Filter Set
open scoped Topology Classical

@[expose] def naturalPulseEnergy : ℝ := canonicalPlateauHeight + 1 / 4

@[expose] def naturalPulseX (d τ : ℝ) (w : ℂ × ℂ) : ℂ × ℂ :=
  let u := coordinatedEigenCoeff (naturalPulseEnergy + d) ((w.1 + w.2) / 4) τ
  let v := coordinatedEigenCoeff naturalPulseEnergy ((w.1 - w.2) / 4) τ
  (2 * (u + v), 2 * (u - v))

@[expose] def naturalPulseZ (η τ : ℝ) (w : ℂ × ℂ) : ℂ × ℂ :=
  (coordinatedEigenCoeff naturalPulseEnergy w.1 τ,
    coordinatedEigenCoeff (naturalPulseEnergy + 2 * η) w.2 τ)

theorem naturalPulseX_initial (d : ℝ) (w : ℂ × ℂ) :
    naturalPulseX d 0 w = w := by
  apply Prod.ext <;> simp [naturalPulseX, coordinatedEigenCoeff_initial] <;> ring

theorem naturalPulseZ_initial (η : ℝ) (w : ℂ × ℂ) :
    naturalPulseZ η 0 w = w := by
  simp [naturalPulseZ, coordinatedEigenCoeff_initial]

@[expose] def naturalStateReal (t : Lattice) (w : ℂ × ℂ) : TileHilbert Vertex :=
  w.1.re • naturalRemoteDark t + w.2.re • naturalRemoteBright t

@[expose] def naturalStateImag (t : Lattice) (w : ℂ × ℂ) : TileHilbert Vertex :=
  w.1.im • naturalRemoteDark t + w.2.im • naturalRemoteBright t

private theorem naturalStateReal_compact (t : Lattice) (a b : ℂ) :
    naturalStateReal t (2 * (a + b), 2 * (a - b)) =
      a.re • (translatedCompactA t) + b.re • (translatedCompactB t) := by
  have h2r : (2 : ℂ).re = 2 := by norm_num
  have h2i : (2 : ℂ).im = 0 := by norm_num
  unfold naturalStateReal naturalRemoteDark naturalRemoteBright
  dsimp only
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, h2r, h2i, zero_mul, sub_zero]
  module

private theorem naturalStateImag_compact (t : Lattice) (a b : ℂ) :
    naturalStateImag t (2 * (a + b), 2 * (a - b)) =
      a.im • (translatedCompactA t) + b.im • (translatedCompactB t) := by
  have h2r : (2 : ℂ).re = 2 := by norm_num
  have h2i : (2 : ℂ).im = 0 := by norm_num
  unfold naturalStateImag naturalRemoteDark naturalRemoteBright
  dsimp only
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, h2r, h2i, zero_mul, add_zero]
  module


theorem naturalPulseX_trajectory (t : Lattice) (d τ : ℝ) (w : ℂ × ℂ) :
    naturalStateReal t (naturalPulseX d τ w) =
      naturalPairReal (translatedCompactA t) (translatedCompactB t)
        (naturalPulseEnergy + d) naturalPulseEnergy ((w.1+w.2)/4) ((w.1-w.2)/4) τ ∧
    naturalStateImag t (naturalPulseX d τ w) =
      naturalPairImag (translatedCompactA t) (translatedCompactB t)
        (naturalPulseEnergy + d) naturalPulseEnergy ((w.1+w.2)/4) ((w.1-w.2)/4) τ := by
  unfold naturalPulseX
  dsimp only
  constructor
  · rw [naturalStateReal_compact] <;> rfl
  · rw [naturalStateImag_compact] <;> rfl

theorem naturalPulseZ_trajectory (t : Lattice) (η τ : ℝ) (w : ℂ × ℂ) :
    naturalStateReal t (naturalPulseZ η τ w) =
      naturalPairReal (naturalRemoteDark t) (naturalRemoteBright t)
        naturalPulseEnergy (naturalPulseEnergy + 2*η) w.1 w.2 τ ∧
    naturalStateImag t (naturalPulseZ η τ w) =
      naturalPairImag (naturalRemoteDark t) (naturalRemoteBright t)
        naturalPulseEnergy (naturalPulseEnergy + 2*η) w.1 w.2 τ :=
  ⟨rfl, rfl⟩

@[expose] def naturalStateWeight (t : Lattice) (w : ℂ × ℂ) : ℝ :=
  ‖naturalStateReal t w‖ ^ 2 + ‖naturalStateImag t w‖ ^ 2

theorem naturalStateWeight_eq (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (w : ℂ × ℂ) :
    naturalStateWeight t w = ‖w.1‖ ^ 2 + ‖w.2‖ ^ 2 := by
  have h := naturalRemoteDarkBright_norm_sq t hrec 0 0 w.1 w.2 0
  obtain ⟨hr, hi⟩ := naturalPair_initial (naturalRemoteDark t) (naturalRemoteBright t) 0 0 w.1 w.2
  rw [hr, hi] at h
  exact h

theorem naturalPulseX_weight (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (d τ : ℝ) (w : ℂ × ℂ) :
    naturalStateWeight t (naturalPulseX d τ w) = naturalStateWeight t w := by
  unfold naturalStateWeight
  obtain ⟨hr, hi⟩ := naturalPulseX_trajectory t d τ w
  obtain ⟨hr0, hi0⟩ := naturalPulseX_trajectory t d 0 w
  rw [naturalPulseX_initial] at hr0 hi0
  rw [hr, hi, hr0, hi0]
  rw [naturalRemoteAB_norm_sq t hrec, naturalRemoteAB_norm_sq t hrec]

theorem naturalPulseZ_weight (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (η τ : ℝ) (w : ℂ × ℂ) :
    naturalStateWeight t (naturalPulseZ η τ w) = naturalStateWeight t w := by
  rw [naturalStateWeight_eq t hrec w]
  unfold naturalStateWeight
  obtain ⟨hr, hi⟩ := naturalPulseZ_trajectory t η τ w
  rw [hr, hi, naturalRemoteDarkBright_norm_sq t hrec]

theorem naturalPulseX_continuous (d : ℝ)
    (f : ℝ → ℝ) (w : ℝ → ℂ × ℂ)
    (hf : Continuous f) (hw : Continuous w) :
    Continuous (fun s => naturalPulseX d (f s) (w s)) := by
  have ha : Continuous (fun s => (w s).1) := hw.fst
  have hb : Continuous (fun s => (w s).2) := hw.snd
  have hp : Continuous (fun s => coordinatedPhase (-(naturalPulseEnergy+d) * f s)) :=
    coordinatedPhase_continuous.comp (continuous_const.mul hf)
  have hq : Continuous (fun s => coordinatedPhase (-naturalPulseEnergy * f s)) :=
    coordinatedPhase_continuous.comp (continuous_const.mul hf)
  simp only [naturalPulseX, coordinatedEigenCoeff]
  fun_prop

theorem naturalPulseZ_continuous (η : ℝ)
    (f : ℝ → ℝ) (w : ℝ → ℂ × ℂ)
    (hf : Continuous f) (hw : Continuous w) :
    Continuous (fun s => naturalPulseZ η (f s) (w s)) := by
  have ha : Continuous (fun s => (w s).1) := hw.fst
  have hb : Continuous (fun s => (w s).2) := hw.snd
  have hp : Continuous (fun s => coordinatedPhase (-naturalPulseEnergy * f s)) :=
    coordinatedPhase_continuous.comp (continuous_const.mul hf)
  have hq : Continuous (fun s => coordinatedPhase (-(naturalPulseEnergy+2*η) * f s)) :=
    coordinatedPhase_continuous.comp (continuous_const.mul hf)
  simp only [naturalPulseZ, coordinatedEigenCoeff]
  fun_prop

/-- Z(p), X(-2t), Z(q), with unit durations and physical scalar phases. -/
@[expose] def naturalProtocolPair (p t q : ℝ) (w : ℂ × ℂ)
    (τ : ℝ) : ℂ × ℂ :=
  naturalPulseZ q (coordinatedClock (τ-2))
    (naturalPulseX (-2*t) (coordinatedClock (τ-1))
      (naturalPulseZ p (coordinatedClock τ) w))

theorem naturalProtocol_first (p t q : ℝ) (w : ℂ × ℂ)
    {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    naturalProtocolPair p t q w τ = naturalPulseZ p τ w := by
  rw [naturalProtocolPair,
    coordinatedClock_zero (by linarith : τ-2 ≤ 0),
    coordinatedClock_zero (by linarith : τ-1 ≤ 0),
    coordinatedClock_inside h0 h1, naturalPulseX_initial, naturalPulseZ_initial]

theorem naturalProtocol_second (p t q : ℝ) (w : ℂ × ℂ)
    {τ : ℝ} (h1 : 1 ≤ τ) (h2 : τ ≤ 2) :
    naturalProtocolPair p t q w τ =
      naturalPulseX (-2*t) (τ-1) (naturalPulseZ p 1 w) := by
  rw [naturalProtocolPair,
    coordinatedClock_zero (by linarith : τ-2 ≤ 0),
    coordinatedClock_inside (by linarith : 0 ≤ τ-1) (by linarith : τ-1 ≤ 1),
    coordinatedClock_one h1, naturalPulseZ_initial]

theorem naturalProtocol_third (p t q : ℝ) (w : ℂ × ℂ)
    {τ : ℝ} (h2 : 2 ≤ τ) (h3 : τ ≤ 3) :
    naturalProtocolPair p t q w τ =
      naturalPulseZ q (τ-2)
        (naturalPulseX (-2*t) 1 (naturalPulseZ p 1 w)) := by
  rw [naturalProtocolPair,
    coordinatedClock_inside (by linarith : 0 ≤ τ-2) (by linarith : τ-2 ≤ 1),
    coordinatedClock_one (by linarith : 1 ≤ τ-1),
    coordinatedClock_one (by linarith : 1 ≤ τ)]

theorem naturalProtocol_initial (p t q : ℝ) (w : ℂ × ℂ) :
    naturalProtocolPair p t q w 0 = w := by
  rw [naturalProtocol_first p t q w (by norm_num) (by norm_num),
    naturalPulseZ_initial]

/-- The first two segments agree exactly at the first switch. -/
theorem naturalProtocol_join_one (p t : ℝ) (w : ℂ × ℂ) :
    naturalPulseZ p 1 w =
      naturalPulseX (-2*t) 0 (naturalPulseZ p 1 w) :=
  (naturalPulseX_initial _ _).symm

/-- The second and third segments agree exactly at the second switch. -/
theorem naturalProtocol_join_two (p t q : ℝ) (w : ℂ × ℂ) :
    naturalPulseX (-2*t) 1 (naturalPulseZ p 1 w) =
      naturalPulseZ q 0 (naturalPulseX (-2*t) 1 (naturalPulseZ p 1 w)) :=
  (naturalPulseZ_initial _ _).symm

theorem naturalProtocol_final (p t q : ℝ) (w : ℂ × ℂ) :
    naturalProtocolPair p t q w 3 =
      naturalPulseZ q 1 (naturalPulseX (-2*t) 1 (naturalPulseZ p 1 w)) := by
  have h := naturalProtocol_third p t q w (τ := 3) (by norm_num) (by norm_num)
  simpa only [show (3 : ℝ) - 2 = 1 by norm_num] using h

theorem naturalProtocol_continuous (p t q : ℝ) (w : ℂ × ℂ) :
    Continuous (naturalProtocolPair p t q w) := by
  unfold naturalProtocolPair
  have h0 : Continuous (fun s : ℝ => coordinatedClock s) := coordinatedClock_continuous
  have h1 : Continuous (fun s : ℝ => coordinatedClock (s-1)) :=
    coordinatedClock_continuous.comp (continuous_id.sub continuous_const)
  have h2 : Continuous (fun s : ℝ => coordinatedClock (s-2)) :=
    coordinatedClock_continuous.comp (continuous_id.sub continuous_const)
  exact naturalPulseZ_continuous q _ _ h2
    (naturalPulseX_continuous (-2*t) _ _ h1
      (naturalPulseZ_continuous p _ _ h0 continuous_const))


theorem naturalProtocol_state_continuous (u : Lattice) (p t q : ℝ) (w : ℂ × ℂ) :
    Continuous (fun τ => naturalStateReal u (naturalProtocolPair p t q w τ)) ∧
    Continuous (fun τ => naturalStateImag u (naturalProtocolPair p t q w τ)) := by
  have hc := naturalProtocol_continuous p t q w
  have ha : Continuous (fun τ : ℝ => (naturalProtocolPair p t q w τ).1) := hc.fst
  have hb : Continuous (fun τ : ℝ => (naturalProtocolPair p t q w τ).2) := hc.snd
  unfold naturalStateReal naturalStateImag
  constructor
  · exact ((Complex.continuous_re.comp ha).smul continuous_const).add
      ((Complex.continuous_re.comp hb).smul continuous_const)
  · exact ((Complex.continuous_im.comp ha).smul continuous_const).add
      ((Complex.continuous_im.comp hb).smul continuous_const)

theorem naturalProtocol_weight (u : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + u) ↔ Admitted n)
    (p t q : ℝ) (w : ℂ × ℂ) (τ : ℝ) :
    naturalStateWeight u (naturalProtocolPair p t q w τ) = naturalStateWeight u w := by
  simp only [naturalProtocolPair, naturalPulseZ_weight u hrec, naturalPulseX_weight u hrec]

theorem naturalState_support (u : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + u) ↔ Admitted n)
    (w : ℂ × ℂ) (v : Vertex) (hv : v ∉ naturalRemoteCell u) :
    naturalStateReal u w v = 0 ∧ naturalStateImag u w v = 0 := by
  have h := naturalRemotePair_support u hrec 0 0 w.1 w.2 0 v hv
  obtain ⟨hr, hi⟩ := naturalPair_initial (naturalRemoteDark u) (naturalRemoteBright u) 0 0 w.1 w.2
  rw [hr, hi] at h
  exact ⟨h.2.2.1, h.2.2.2⟩

theorem naturalProtocol_support (u : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + u) ↔ Admitted n)
    (p t q : ℝ) (w : ℂ × ℂ) (τ : ℝ) (v : Vertex) (hv : v ∉ naturalRemoteCell u) :
    naturalStateReal u (naturalProtocolPair p t q w τ) v = 0 ∧
    naturalStateImag u (naturalProtocolPair p t q w τ) v = 0 :=
  naturalState_support u hrec _ v hv

@[expose] def naturalSolvesAt (u : Lattice) (δ η : ℝ) (f : ℝ → ℂ × ℂ) (s : ℝ) : Prop :=
  HasDerivAt (fun τ => naturalStateReal u (f τ))
    (naturalRemoteDriven u δ η (naturalStateImag u (f s))) s ∧
  HasDerivAt (fun τ => naturalStateImag u (f τ))
    (-(naturalRemoteDriven u δ η (naturalStateReal u (f s)))) s

theorem naturalPulseX_solvesAt (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (d : ℝ) (w : ℂ × ℂ) (s : ℝ) :
    naturalSolvesAt v.val (1 / 16 + d) 0 (fun τ => naturalPulseX d τ w) s := by
  have hR : (fun τ => naturalStateReal v.val (naturalPulseX d τ w)) =
      naturalPairReal (translatedCompactA v.val) (translatedCompactB v.val)
        (naturalPulseEnergy+d) naturalPulseEnergy ((w.1+w.2)/4) ((w.1-w.2)/4) := by
    funext τ
    exact (naturalPulseX_trajectory v.val d τ w).1
  have hI : (fun τ => naturalStateImag v.val (naturalPulseX d τ w)) =
      naturalPairImag (translatedCompactA v.val) (translatedCompactB v.val)
        (naturalPulseEnergy+d) naturalPulseEnergy ((w.1+w.2)/4) ((w.1-w.2)/4) := by
    funext τ
    exact (naturalPulseX_trajectory v.val d τ w).2
  have he : canonicalPlateauHeight + 3 / 16 + (1 / 16 + d) =
      naturalPulseEnergy + d := by unfold naturalPulseEnergy; ring
  have h := naturalRemoteDetuning_Schrodinger v hr hrec (1 / 16 + d)
    ((w.1+w.2)/4) ((w.1-w.2)/4) s
  rw [he] at h
  unfold naturalSolvesAt
  rw [hR, hI, (naturalPulseX_trajectory v.val d s w).1,
    (naturalPulseX_trajectory v.val d s w).2]
  exact h

theorem naturalPulseZ_solvesAt (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (η : ℝ) (w : ℂ × ℂ) (s : ℝ) :
    naturalSolvesAt v.val (1 / 16) η (fun τ => naturalPulseZ η τ w) s := by
  exact naturalRemoteCompensated_Schrodinger v hr hrec η w.1 w.2 s

/-- Translation of the local time coordinate leaves the derivative unchanged. -/
theorem naturalSolvesAt_shift (u : Lattice) (δ η : ℝ) (f : ℝ → ℂ × ℂ) (c s : ℝ)
    (h : naturalSolvesAt u δ η f (s-c)) :
    naturalSolvesAt u δ η (fun τ => f (τ-c)) s := by
  have hs : HasDerivAt (fun τ : ℝ => τ-c) 1 s := (hasDerivAt_id s).sub_const c
  unfold naturalSolvesAt at h ⊢
  constructor
  · simpa only [Function.comp_def, one_smul] using h.1.scomp s hs
  · simpa only [Function.comp_def, one_smul] using h.2.scomp s hs

/-- The full-domain equation is local in time. -/
theorem naturalSolvesAt_congr (u : Lattice) (δ η : ℝ) (f g : ℝ → ℂ × ℂ) (s : ℝ)
    (h : naturalSolvesAt u δ η f s)
    (he : f =ᶠ[nhds s] g) : naturalSolvesAt u δ η g s := by
  have hs : f s = g s := he.eq_of_nhds
  have hr : (fun τ => naturalStateReal u (f τ)) =ᶠ[nhds s]
      (fun τ => naturalStateReal u (g τ)) :=
    he.mono fun τ hτ => congrArg (naturalStateReal u) hτ
  have hi : (fun τ => naturalStateImag u (f τ)) =ᶠ[nhds s]
      (fun τ => naturalStateImag u (g τ)) :=
    he.mono fun τ hτ => congrArg (naturalStateImag u) hτ
  unfold naturalSolvesAt at h ⊢
  rw [← hs]
  exact ⟨h.1.congr_of_eventuallyEq hr.symm, h.2.congr_of_eventuallyEq hi.symm⟩


theorem naturalProtocol_solves_first (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (p t q : ℝ) (w : ℂ × ℂ) {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    naturalSolvesAt v.val (1 / 16) p (naturalProtocolPair p t q w) s := by
  apply naturalSolvesAt_congr v.val (1 / 16) p (fun τ => naturalPulseZ p τ w)
    (naturalProtocolPair p t q w) s (naturalPulseZ_solvesAt v hr hrec p w s)
  filter_upwards [Ioo_mem_nhds h0 h1] with τ hτ
  exact (naturalProtocol_first p t q w hτ.1.le hτ.2.le).symm

theorem naturalProtocol_solves_second (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (p t q : ℝ) (w : ℂ × ℂ) {s : ℝ} (h1 : 1 < s) (h2 : s < 2) :
    naturalSolvesAt v.val (1 / 16 + -2*t) 0 (naturalProtocolPair p t q w) s := by
  apply naturalSolvesAt_congr v.val (1 / 16 + -2*t) 0
    (fun τ => naturalPulseX (-2*t) (τ-1) (naturalPulseZ p 1 w))
    (naturalProtocolPair p t q w) s
  · exact naturalSolvesAt_shift _ _ _ _ 1 s
      (naturalPulseX_solvesAt v hr hrec (-2*t) (naturalPulseZ p 1 w) (s-1))
  · filter_upwards [Ioo_mem_nhds h1 h2] with τ hτ
    exact (naturalProtocol_second p t q w hτ.1.le hτ.2.le).symm

theorem naturalProtocol_solves_third (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (p t q : ℝ) (w : ℂ × ℂ) {s : ℝ} (h2 : 2 < s) (h3 : s < 3) :
    naturalSolvesAt v.val (1 / 16) q (naturalProtocolPair p t q w) s := by
  apply naturalSolvesAt_congr v.val (1 / 16) q
    (fun τ => naturalPulseZ q (τ-2)
      (naturalPulseX (-2*t) 1 (naturalPulseZ p 1 w)))
    (naturalProtocolPair p t q w) s
  · exact naturalSolvesAt_shift _ _ _ _ 2 s
      (naturalPulseZ_solvesAt v hr hrec q (naturalPulseX (-2*t) 1 (naturalPulseZ p 1 w)) (s-2))
  · filter_upwards [Ioo_mem_nhds h2 h3] with τ hτ
    exact (naturalProtocol_third p t q w hτ.1.le hτ.2.le).symm

end
end SpectralGeometry.AmmannBeenker
