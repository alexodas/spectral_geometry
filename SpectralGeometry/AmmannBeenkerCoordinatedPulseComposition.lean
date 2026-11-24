module

public import SpectralGeometry.AmmannBeenkerCoordinatedRotationDynamics

public section

/-!
# Continuous three-pulse natural-domain protocol (L7c.3)

The full state is represented by its real and imaginary graph Hilbert
vectors. The physical (phase-retaining) coefficient matrices are
composed with local times clamped to [0,1]. The state is continuous
at switches, stays in the natural domain, and has zero leakage and
constant squared complex norm. Each closed segment is identified
with an exact full-domain Schroedinger trajectory in its local time.
No derivative across a discontinuous control switch is required.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open Filter Set
open scoped Topology

@[expose] def coordinatedPulseX (δ τ : ℝ) (w : ℂ × ℂ) : ℂ × ℂ :=
  coordinatedApplyPair (coordinatedXAxisMatrix δ τ) w.1 w.2

@[expose] def coordinatedPulseZ (η τ : ℝ) (w : ℂ × ℂ) : ℂ × ℂ :=
  coordinatedApplyPair (coordinatedZAxisMatrix η τ) w.1 w.2

theorem coordinatedApplyPair_one (a b : ℂ) :
    coordinatedApplyPair 1 a b = (a,b) := by
  simp [coordinatedApplyPair, Matrix.one_apply]

theorem coordinatedPulseX_initial (δ : ℝ) (w : ℂ × ℂ) :
    coordinatedPulseX δ 0 w = w := by
  rw [coordinatedPulseX, coordinatedXAxisMatrix_initial, coordinatedApplyPair_one]

theorem coordinatedPulseZ_initial (η : ℝ) (w : ℂ × ℂ) :
    coordinatedPulseZ η 0 w = w := by
  rw [coordinatedPulseZ, coordinatedZAxisMatrix_initial, coordinatedApplyPair_one]

/-- Real and imaginary embeddings, and their explicit natural-domain lifts. -/
@[expose] def coordinatedStateReal (w : ℂ × ℂ) : TileHilbert Vertex :=
  coordinatedEmbedReal w.1 w.2

@[expose] def coordinatedStateImag (w : ℂ × ℂ) : TileHilbert Vertex :=
  coordinatedEmbedImag w.1 w.2

@[expose] def domainCoordinatedStateReal (w : ℂ × ℂ) : infiniteOnsiteDomain potential :=
  w.1.re • domainCrossingDark + w.2.re • domainCrossingBright

@[expose] def domainCoordinatedStateImag (w : ℂ × ℂ) : infiniteOnsiteDomain potential :=
  w.1.im • domainCrossingDark + w.2.im • domainCrossingBright

theorem coordinatedState_domain (w : ℂ × ℂ) :
    (domainCoordinatedStateReal w : TileHilbert Vertex) = coordinatedStateReal w ∧
    (domainCoordinatedStateImag w : TileHilbert Vertex) = coordinatedStateImag w :=
  ⟨rfl,rfl⟩

theorem coordinatedState_leakage_zero (w : ℂ × ℂ) :
    crossingLeakage (coordinatedStateReal w) = 0 ∧
    crossingLeakage (coordinatedStateImag w) = 0 := by
  simp [coordinatedStateReal, coordinatedStateImag, coordinatedEmbedReal,
    coordinatedEmbedImag, crossingLeakage_add, crossingLeakage_smul,
    crossingDark_leakage_zero, coordinatedBright_leakage_zero]

@[expose] def coordinatedStateWeight (w : ℂ × ℂ) : ℝ :=
  ‖coordinatedStateReal w‖ ^ 2 + ‖coordinatedStateImag w‖ ^ 2

theorem coordinatedStateWeight_eq (w : ℂ × ℂ) :
    coordinatedStateWeight w = ‖w.1‖ ^ 2 + ‖w.2‖ ^ 2 := by
  have h := coordinatedZAxis_norm_sq 0 w.1 w.2 0
  have he := coordinatedZAxis_trajectory_matrix 0 0 w.1 w.2
  dsimp only at he
  rw [coordinatedZAxisMatrix_initial, coordinatedApplyPair_one] at he
  rw [he.1, he.2] at h
  exact h

theorem coordinatedPulseX_weight (δ τ : ℝ) (w : ℂ × ℂ) :
    coordinatedStateWeight (coordinatedPulseX δ τ w) = coordinatedStateWeight w := by
  have ht := coordinatedXAxis_norm_sq δ ((w.1+w.2)/4) ((w.1-w.2)/4) τ
  have h0 := coordinatedXAxis_norm_sq δ ((w.1+w.2)/4) ((w.1-w.2)/4) 0
  have et := coordinatedXAxis_trajectory_matrix δ τ w.1 w.2
  have e0 := coordinatedXAxis_trajectory_matrix δ 0 w.1 w.2
  dsimp only at et e0
  rw [coordinatedXAxisMatrix_initial, coordinatedApplyPair_one] at e0
  rw [et.1, et.2] at ht
  rw [e0.1, e0.2] at h0
  exact ht.trans h0.symm

theorem coordinatedPulseZ_weight (η τ : ℝ) (w : ℂ × ℂ) :
    coordinatedStateWeight (coordinatedPulseZ η τ w) = coordinatedStateWeight w := by
  have h := coordinatedZAxis_norm_sq η w.1 w.2 τ
  have he := coordinatedZAxis_trajectory_matrix η τ w.1 w.2
  dsimp only at he
  rw [he.1, he.2] at h
  rw [coordinatedStateWeight_eq w]
  exact h

theorem coordinatedPhase_continuous : Continuous coordinatedPhase := by
  unfold coordinatedPhase
  fun_prop

/-- Continuous dependence of each pulse on its time and input pair. -/
theorem coordinatedPulseX_continuous (δ : ℝ)
    (f : ℝ → ℝ) (w : ℝ → ℂ × ℂ)
    (hf : Continuous f) (hw : Continuous w) :
    Continuous (fun s => coordinatedPulseX δ (f s) (w s)) := by
  have ha : Continuous (fun s => (w s).1) := hw.fst
  have hb : Continuous (fun s => (w s).2) := hw.snd
  have hp : Continuous (fun s => coordinatedPhase (-(crossingEnergy+δ) * f s)) :=
    coordinatedPhase_continuous.comp (continuous_const.mul hf)
  have hq : Continuous (fun s => coordinatedPhase (-crossingEnergy * f s)) :=
    coordinatedPhase_continuous.comp (continuous_const.mul hf)
  simp only [coordinatedPulseX, coordinatedXAxisMatrix_coefficients, coordinatedEigenCoeff]
  fun_prop

theorem coordinatedPulseZ_continuous (η : ℝ)
    (f : ℝ → ℝ) (w : ℝ → ℂ × ℂ)
    (hf : Continuous f) (hw : Continuous w) :
    Continuous (fun s => coordinatedPulseZ η (f s) (w s)) := by
  have ha : Continuous (fun s => (w s).1) := hw.fst
  have hb : Continuous (fun s => (w s).2) := hw.snd
  have hp : Continuous (fun s => coordinatedPhase (-crossingEnergy * f s)) :=
    coordinatedPhase_continuous.comp (continuous_const.mul hf)
  have hq : Continuous (fun s => coordinatedPhase (-(crossingEnergy+2*η) * f s)) :=
    coordinatedPhase_continuous.comp (continuous_const.mul hf)
  simp only [coordinatedPulseZ, coordinatedZAxisMatrix_coefficients, coordinatedEigenCoeff]
  fun_prop

/-- A unit-duration pulse clock, frozen before and after its interval. -/
@[expose] def coordinatedClock (s : ℝ) : ℝ := min (max s 0) 1

theorem coordinatedClock_zero {s : ℝ} (h : s ≤ 0) :
    coordinatedClock s = 0 := by
  simp [coordinatedClock, max_eq_right h]

theorem coordinatedClock_one {s : ℝ} (h : 1 ≤ s) :
    coordinatedClock s = 1 := by
  rw [coordinatedClock, max_eq_left (by linarith : 0 ≤ s), min_eq_right h]

theorem coordinatedClock_inside {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    coordinatedClock s = s := by
  rw [coordinatedClock, max_eq_left h0, min_eq_left h1]

theorem coordinatedClock_continuous : Continuous coordinatedClock := by
  unfold coordinatedClock
  exact (continuous_id.max continuous_const).min continuous_const

/-- Z(p), X(-2t), Z(q), with unit durations and physical scalar phases. -/
@[expose] def coordinatedProtocolPair (p t q : ℝ) (w : ℂ × ℂ)
    (τ : ℝ) : ℂ × ℂ :=
  coordinatedPulseZ q (coordinatedClock (τ-2))
    (coordinatedPulseX (-2*t) (coordinatedClock (τ-1))
      (coordinatedPulseZ p (coordinatedClock τ) w))

theorem coordinatedProtocol_first (p t q : ℝ) (w : ℂ × ℂ)
    {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    coordinatedProtocolPair p t q w τ = coordinatedPulseZ p τ w := by
  rw [coordinatedProtocolPair,
    coordinatedClock_zero (by linarith : τ-2 ≤ 0),
    coordinatedClock_zero (by linarith : τ-1 ≤ 0),
    coordinatedClock_inside h0 h1, coordinatedPulseX_initial, coordinatedPulseZ_initial]

theorem coordinatedProtocol_second (p t q : ℝ) (w : ℂ × ℂ)
    {τ : ℝ} (h1 : 1 ≤ τ) (h2 : τ ≤ 2) :
    coordinatedProtocolPair p t q w τ =
      coordinatedPulseX (-2*t) (τ-1) (coordinatedPulseZ p 1 w) := by
  rw [coordinatedProtocolPair,
    coordinatedClock_zero (by linarith : τ-2 ≤ 0),
    coordinatedClock_inside (by linarith : 0 ≤ τ-1) (by linarith : τ-1 ≤ 1),
    coordinatedClock_one h1, coordinatedPulseZ_initial]

theorem coordinatedProtocol_third (p t q : ℝ) (w : ℂ × ℂ)
    {τ : ℝ} (h2 : 2 ≤ τ) (h3 : τ ≤ 3) :
    coordinatedProtocolPair p t q w τ =
      coordinatedPulseZ q (τ-2)
        (coordinatedPulseX (-2*t) 1 (coordinatedPulseZ p 1 w)) := by
  rw [coordinatedProtocolPair,
    coordinatedClock_inside (by linarith : 0 ≤ τ-2) (by linarith : τ-2 ≤ 1),
    coordinatedClock_one (by linarith : 1 ≤ τ-1),
    coordinatedClock_one (by linarith : 1 ≤ τ)]

theorem coordinatedProtocol_initial (p t q : ℝ) (w : ℂ × ℂ) :
    coordinatedProtocolPair p t q w 0 = w := by
  rw [coordinatedProtocol_first p t q w (by norm_num) (by norm_num),
    coordinatedPulseZ_initial]

/-- The first two segments agree exactly at the first switch. -/
theorem coordinatedProtocol_join_one (p t : ℝ) (w : ℂ × ℂ) :
    coordinatedPulseZ p 1 w =
      coordinatedPulseX (-2*t) 0 (coordinatedPulseZ p 1 w) :=
  (coordinatedPulseX_initial _ _).symm

/-- The second and third segments agree exactly at the second switch. -/
theorem coordinatedProtocol_join_two (p t q : ℝ) (w : ℂ × ℂ) :
    coordinatedPulseX (-2*t) 1 (coordinatedPulseZ p 1 w) =
      coordinatedPulseZ q 0 (coordinatedPulseX (-2*t) 1 (coordinatedPulseZ p 1 w)) :=
  (coordinatedPulseZ_initial _ _).symm

theorem coordinatedProtocol_final (p t q : ℝ) (w : ℂ × ℂ) :
    coordinatedProtocolPair p t q w 3 =
      coordinatedPulseZ q 1 (coordinatedPulseX (-2*t) 1 (coordinatedPulseZ p 1 w)) := by
  have h := coordinatedProtocol_third p t q w (τ := 3) (by norm_num) (by norm_num)
  simpa only [show (3 : ℝ) - 2 = 1 by norm_num] using h

theorem coordinatedProtocol_continuous (p t q : ℝ) (w : ℂ × ℂ) :
    Continuous (coordinatedProtocolPair p t q w) := by
  unfold coordinatedProtocolPair
  have h0 : Continuous (fun s : ℝ => coordinatedClock s) := coordinatedClock_continuous
  have h1 : Continuous (fun s : ℝ => coordinatedClock (s-1)) :=
    coordinatedClock_continuous.comp (continuous_id.sub continuous_const)
  have h2 : Continuous (fun s : ℝ => coordinatedClock (s-2)) :=
    coordinatedClock_continuous.comp (continuous_id.sub continuous_const)
  exact coordinatedPulseZ_continuous q _ _ h2
    (coordinatedPulseX_continuous (-2*t) _ _ h1
      (coordinatedPulseZ_continuous p _ _ h0 continuous_const))

theorem coordinatedProtocol_state_continuous (p t q : ℝ) (w : ℂ × ℂ) :
    Continuous (fun τ => coordinatedStateReal (coordinatedProtocolPair p t q w τ)) ∧
    Continuous (fun τ => coordinatedStateImag (coordinatedProtocolPair p t q w τ)) := by
  have hc := coordinatedProtocol_continuous p t q w
  have ha : Continuous (fun τ : ℝ => (coordinatedProtocolPair p t q w τ).1) := hc.fst
  have hb : Continuous (fun τ : ℝ => (coordinatedProtocolPair p t q w τ).2) := hc.snd
  unfold coordinatedStateReal coordinatedStateImag coordinatedEmbedReal coordinatedEmbedImag
  constructor
  · exact ((Complex.continuous_re.comp ha).smul continuous_const).add
      ((Complex.continuous_re.comp hb).smul continuous_const)
  · exact ((Complex.continuous_im.comp ha).smul continuous_const).add
      ((Complex.continuous_im.comp hb).smul continuous_const)

theorem coordinatedProtocol_weight (p t q : ℝ) (w : ℂ × ℂ) (τ : ℝ) :
    coordinatedStateWeight (coordinatedProtocolPair p t q w τ) =
      coordinatedStateWeight w := by
  simp only [coordinatedProtocolPair, coordinatedPulseZ_weight, coordinatedPulseX_weight]

theorem coordinatedProtocol_leakage_zero (p t q : ℝ) (w : ℂ × ℂ) (τ : ℝ) :
    crossingLeakage (coordinatedStateReal (coordinatedProtocolPair p t q w τ)) = 0 ∧
    crossingLeakage (coordinatedStateImag (coordinatedProtocolPair p t q w τ)) = 0 :=
  coordinatedState_leakage_zero _

theorem coordinatedProtocol_domain (p t q : ℝ) (w : ℂ × ℂ) (τ : ℝ) :
    coordinatedStateReal (coordinatedProtocolPair p t q w τ) ∈ infiniteOnsiteDomain potential ∧
    coordinatedStateImag (coordinatedProtocolPair p t q w τ) ∈ infiniteOnsiteDomain potential := by
  let v := coordinatedProtocolPair p t q w τ
  exact ⟨(coordinatedState_domain v).1 ▸ (domainCoordinatedStateReal v).property,
    (coordinatedState_domain v).2 ▸ (domainCoordinatedStateImag v).property⟩

/-- A coefficient trajectory solves the two full natural-domain equations. -/
@[expose] def coordinatedSolvesAt (δ η : ℝ) (f : ℝ → ℂ × ℂ) (s : ℝ) : Prop :=
  HasDerivAt (fun τ => coordinatedStateReal (f τ))
    (onsitePlusBounded potential (coordinatedCorrection δ η)
      (domainCoordinatedStateImag (f s))) s ∧
  HasDerivAt (fun τ => coordinatedStateImag (f τ))
    (-(onsitePlusBounded potential (coordinatedCorrection δ η)
      (domainCoordinatedStateReal (f s)))) s

theorem coordinatedPulseX_solvesAt (δ : ℝ) (w : ℂ × ℂ) (s : ℝ) :
    coordinatedSolvesAt δ 0 (fun τ => coordinatedPulseX δ τ w) s := by
  have hr : (fun τ => coordinatedStateReal (coordinatedPulseX δ τ w)) =
      coordinatedPairReal domainCompactA domainCompactB
        (crossingEnergy+δ) crossingEnergy ((w.1+w.2)/4) ((w.1-w.2)/4) := by
    funext τ
    exact (coordinatedXAxis_trajectory_matrix δ τ w.1 w.2).1.symm
  have hi : (fun τ => coordinatedStateImag (coordinatedPulseX δ τ w)) =
      coordinatedPairImag domainCompactA domainCompactB
        (crossingEnergy+δ) crossingEnergy ((w.1+w.2)/4) ((w.1-w.2)/4) := by
    funext τ
    exact (coordinatedXAxis_trajectory_matrix δ τ w.1 w.2).2.symm
  have hdr : domainCoordinatedStateReal (coordinatedPulseX δ s w) =
      domainCoordinatedPairReal domainCompactA domainCompactB
        (crossingEnergy+δ) crossingEnergy ((w.1+w.2)/4) ((w.1-w.2)/4) s := by
    apply Subtype.ext
    exact (coordinatedXAxis_trajectory_matrix δ s w.1 w.2).1.symm
  have hdi : domainCoordinatedStateImag (coordinatedPulseX δ s w) =
      domainCoordinatedPairImag domainCompactA domainCompactB
        (crossingEnergy+δ) crossingEnergy ((w.1+w.2)/4) ((w.1-w.2)/4) s := by
    apply Subtype.ext
    exact (coordinatedXAxis_trajectory_matrix δ s w.1 w.2).2.symm
  unfold coordinatedSolvesAt
  rw [hr, hi, hdr, hdi]
  exact coordinatedXAxis_Schrodinger δ _ _ s

theorem coordinatedPulseZ_solvesAt (η : ℝ) (w : ℂ × ℂ) (s : ℝ) :
    coordinatedSolvesAt 0 η (fun τ => coordinatedPulseZ η τ w) s := by
  have hr : (fun τ => coordinatedStateReal (coordinatedPulseZ η τ w)) =
      coordinatedPairReal domainCrossingDark domainCrossingBright
        crossingEnergy (crossingEnergy+2*η) w.1 w.2 := by
    funext τ
    exact (coordinatedZAxis_trajectory_matrix η τ w.1 w.2).1.symm
  have hi : (fun τ => coordinatedStateImag (coordinatedPulseZ η τ w)) =
      coordinatedPairImag domainCrossingDark domainCrossingBright
        crossingEnergy (crossingEnergy+2*η) w.1 w.2 := by
    funext τ
    exact (coordinatedZAxis_trajectory_matrix η τ w.1 w.2).2.symm
  have hdr : domainCoordinatedStateReal (coordinatedPulseZ η s w) =
      domainCoordinatedPairReal domainCrossingDark domainCrossingBright
        crossingEnergy (crossingEnergy+2*η) w.1 w.2 s := by
    apply Subtype.ext
    exact (coordinatedZAxis_trajectory_matrix η s w.1 w.2).1.symm
  have hdi : domainCoordinatedStateImag (coordinatedPulseZ η s w) =
      domainCoordinatedPairImag domainCrossingDark domainCrossingBright
        crossingEnergy (crossingEnergy+2*η) w.1 w.2 s := by
    apply Subtype.ext
    exact (coordinatedZAxis_trajectory_matrix η s w.1 w.2).2.symm
  unfold coordinatedSolvesAt
  rw [hr, hi, hdr, hdi]
  exact coordinatedZAxis_Schrodinger η _ _ s

/-- Translation of the local time coordinate leaves the derivative unchanged. -/
theorem coordinatedSolvesAt_shift (δ η : ℝ) (f : ℝ → ℂ × ℂ) (c s : ℝ)
    (h : coordinatedSolvesAt δ η f (s-c)) :
    coordinatedSolvesAt δ η (fun τ => f (τ-c)) s := by
  have hs : HasDerivAt (fun τ : ℝ => τ-c) 1 s := (hasDerivAt_id s).sub_const c
  unfold coordinatedSolvesAt at h ⊢
  constructor
  · simpa only [Function.comp_def, one_smul] using h.1.scomp s hs
  · simpa only [Function.comp_def, one_smul] using h.2.scomp s hs

/-- The full-domain equation is local in time. -/
theorem coordinatedSolvesAt_congr (δ η : ℝ) (f g : ℝ → ℂ × ℂ) (s : ℝ)
    (h : coordinatedSolvesAt δ η f s)
    (he : f =ᶠ[nhds s] g) : coordinatedSolvesAt δ η g s := by
  have hs : f s = g s := he.eq_of_nhds
  have hr : (fun τ => coordinatedStateReal (f τ)) =ᶠ[nhds s]
      (fun τ => coordinatedStateReal (g τ)) :=
    he.mono fun τ hτ => congrArg coordinatedStateReal hτ
  have hi : (fun τ => coordinatedStateImag (f τ)) =ᶠ[nhds s]
      (fun τ => coordinatedStateImag (g τ)) :=
    he.mono fun τ hτ => congrArg coordinatedStateImag hτ
  unfold coordinatedSolvesAt at h ⊢
  rw [← hs]
  exact ⟨h.1.congr_of_eventuallyEq hr.symm, h.2.congr_of_eventuallyEq hi.symm⟩

/-- On each open interval, the single global trajectory solves the actual
Hamiltonian equation for that segment. The state is continuous at switches. -/
theorem coordinatedProtocol_solves_first (p t q : ℝ) (w : ℂ × ℂ)
    {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    coordinatedSolvesAt 0 p (coordinatedProtocolPair p t q w) s := by
  apply coordinatedSolvesAt_congr 0 p (fun τ => coordinatedPulseZ p τ w)
    (coordinatedProtocolPair p t q w) s (coordinatedPulseZ_solvesAt p w s)
  filter_upwards [Ioo_mem_nhds h0 h1] with τ hτ
  exact (coordinatedProtocol_first p t q w hτ.1.le hτ.2.le).symm

theorem coordinatedProtocol_solves_second (p t q : ℝ) (w : ℂ × ℂ)
    {s : ℝ} (h1 : 1 < s) (h2 : s < 2) :
    coordinatedSolvesAt (-2*t) 0 (coordinatedProtocolPair p t q w) s := by
  apply coordinatedSolvesAt_congr (-2*t) 0
    (fun τ => coordinatedPulseX (-2*t) (τ-1) (coordinatedPulseZ p 1 w))
    (coordinatedProtocolPair p t q w) s
  · exact coordinatedSolvesAt_shift _ _ _ 1 s
      (coordinatedPulseX_solvesAt (-2*t) (coordinatedPulseZ p 1 w) (s-1))
  · filter_upwards [Ioo_mem_nhds h1 h2] with τ hτ
    exact (coordinatedProtocol_second p t q w hτ.1.le hτ.2.le).symm

theorem coordinatedProtocol_solves_third (p t q : ℝ) (w : ℂ × ℂ)
    {s : ℝ} (h2 : 2 < s) (h3 : s < 3) :
    coordinatedSolvesAt 0 q (coordinatedProtocolPair p t q w) s := by
  apply coordinatedSolvesAt_congr 0 q
    (fun τ => coordinatedPulseZ q (τ-2)
      (coordinatedPulseX (-2*t) 1 (coordinatedPulseZ p 1 w)))
    (coordinatedProtocolPair p t q w) s
  · exact coordinatedSolvesAt_shift _ _ _ 2 s
      (coordinatedPulseZ_solvesAt q (coordinatedPulseX (-2*t) 1 (coordinatedPulseZ p 1 w)) (s-2))
  · filter_upwards [Ioo_mem_nhds h2 h3] with τ hτ
    exact (coordinatedProtocol_third p t q w hτ.1.le hτ.2.le).symm

end
end SpectralGeometry.AmmannBeenker
