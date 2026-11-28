module

public import SpectralGeometry.AmmannBeenkerNaturalFinitePreparation

public section

/-!
# Exact storage after local preparation

After the three-pulse protocol, all controls are switched off.
The free trajectory is written in the same normalized dark/bright
coordinates as the preparation, with the actual two distinct natural
energies. It is continuous at the final switch and solves the
unperturbed infinite Hamiltonian equation afterwards. Norm and compact
support persist, and the ray returns after the common relative period
32*pi. This is ideal coherent storage, not a disorder protection result.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open Filter Set
open scoped Topology Classical

/-- Free evolution in dark/bright coordinates: the effective detuning
is minus the natural splitting, so the physical onsite control is zero. -/
@[expose] def naturalStoragePair (τ : ℝ) (w : ℂ × ℂ) : ℂ × ℂ :=
  naturalPulseX (-(1 / 16)) τ w

theorem naturalStorage_initial (w : ℂ × ℂ) :
    naturalStoragePair 0 w = w :=
  naturalPulseX_initial _ w

theorem naturalStorage_weight (u : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + u) ↔ Admitted n)
    (τ : ℝ) (w : ℂ × ℂ) :
    naturalStateWeight u (naturalStoragePair τ w) = naturalStateWeight u w :=
  naturalPulseX_weight u hrec _ τ w

theorem naturalStorage_continuous (f : ℝ → ℝ) (w : ℝ → ℂ × ℂ)
    (hf : Continuous f) (hw : Continuous w) :
    Continuous (fun s => naturalStoragePair (f s) (w s)) :=
  naturalPulseX_continuous _ f w hf hw

theorem naturalStorage_solvesAt (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (w : ℂ × ℂ) (τ : ℝ) :
    naturalSolvesAt v.val 0 0 (fun s => naturalStoragePair s w) τ := by
  have h := naturalPulseX_solvesAt v hr hrec (-(1 / 16)) w τ
  rw [show (1 / 16 : ℝ) + -(1 / 16) = 0 by ring] at h
  exact h

theorem naturalStorage_full_solvesAt (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (w : ℂ × ℂ) (τ : ℝ) :
    naturalFullSolvesAt canonicalPlateauHamiltonian
      (fun s => naturalStateReal v.val (naturalStoragePair s w))
      (fun s => naturalStateImag v.val (naturalStoragePair s w)) τ := by
  have h := naturalStorage_solvesAt v hr hrec w τ
  unfold naturalSolvesAt at h
  simpa only [naturalRemoteDriven, zero_smul, add_zero] using h

/-- The two A/B coefficients of the freely evolving state retain their
physical scalar phases. The two coefficients here multiply the
unnormalized compact modes. -/
theorem naturalStorage_AB_coefficients (τ : ℝ) (w : ℂ × ℂ) :
    naturalStoragePair τ w =
      let a := coordinatedEigenCoeff (canonicalPlateauHeight + 3 / 16) ((w.1 + w.2) / 4) τ
      let b := coordinatedEigenCoeff (canonicalPlateauHeight + 1 / 4) ((w.1 - w.2) / 4) τ
      (2 * (a + b), 2 * (a - b)) := by
  unfold naturalStoragePair naturalPulseX
  dsimp only
  rw [show naturalPulseEnergy + -(1 / 16) =
    canonicalPlateauHeight + 3 / 16 by unfold naturalPulseEnergy; ring] <;> rfl

theorem naturalStorage_period_phase :
    coordinatedPhase (-(32 * Real.pi : ℝ) / 16) = 1 := by
  rw [show -(32 * Real.pi : ℝ) / 16 = -(2 * Real.pi) by ring,
    coordinatedPhase_trig, Real.cos_neg, Real.sin_neg,
    Real.cos_two_pi, Real.sin_two_pi]
  simp

/-- Every initial local state returns to the same ray after 32*pi.
The common dynamical phase is explicit. -/
theorem naturalStorage_period_return (w : ℂ × ℂ) :
    naturalStoragePair (32 * Real.pi) w =
      let z := coordinatedPhase (-(canonicalPlateauHeight + 3 / 16) * (32 * Real.pi))
      (z * w.1, z * w.2) := by
  have h := naturalRemote_free_relative_phase canonicalPlateauHeight (32 * Real.pi)
  rw [naturalStorage_period_phase, one_mul] at h
  simp only [coordinatedEigenCoeff, mul_one] at h
  rw [naturalStorage_AB_coefficients]
  dsimp only [coordinatedEigenCoeff]
  rw [h]
  apply Prod.ext <;> dsimp only <;> ring

/-- The clamped preparation is constant after its final endpoint. -/
theorem naturalProtocol_after (p t q : ℝ) (w : ℂ × ℂ) (τ : ℝ) (hτ : 3 ≤ τ) :
    naturalProtocolPair p t q w τ = naturalProtocolPair p t q w 3 := by
  rw [naturalProtocol_final]
  unfold naturalProtocolPair
  rw [coordinatedClock_one (by linarith : 1 ≤ τ-2),
    coordinatedClock_one (by linarith : 1 ≤ τ-1),
    coordinatedClock_one (by linarith : 1 ≤ τ)]

/-- The preparation trajectory followed by actual free storage, not
the artificially frozen trajectory used to compose the pulses. -/
@[expose] def naturalProtocolStored (p t q : ℝ) (w : ℂ × ℂ) (τ : ℝ) : ℂ × ℂ :=
  naturalStoragePair (max (τ - 3) 0) (naturalProtocolPair p t q w τ)

theorem naturalProtocolStored_before (p t q : ℝ) (w : ℂ × ℂ) (τ : ℝ) (hτ : τ ≤ 3) :
    naturalProtocolStored p t q w τ = naturalProtocolPair p t q w τ := by
  rw [naturalProtocolStored, max_eq_right (by linarith : τ-3 ≤ 0), naturalStorage_initial]

theorem naturalProtocolStored_after (p t q : ℝ) (w : ℂ × ℂ) (τ : ℝ) (hτ : 3 ≤ τ) :
    naturalProtocolStored p t q w τ =
      naturalStoragePair (τ-3) (naturalProtocolPair p t q w 3) := by
  rw [naturalProtocolStored, max_eq_left (by linarith : 0 ≤ τ-3),
    naturalProtocol_after p t q w τ hτ]

theorem naturalProtocolStored_continuous (p t q : ℝ) (w : ℂ × ℂ) :
    Continuous (naturalProtocolStored p t q w) := by
  unfold naturalProtocolStored
  exact naturalStorage_continuous _ _ ((continuous_id.sub continuous_const).max continuous_const)
    (naturalProtocol_continuous p t q w)

theorem naturalProtocolStored_state_continuous (u : Lattice) (p t q : ℝ) (w : ℂ × ℂ) :
    Continuous (fun τ => naturalStateReal u (naturalProtocolStored p t q w τ)) ∧
    Continuous (fun τ => naturalStateImag u (naturalProtocolStored p t q w τ)) := by
  have hc := naturalProtocolStored_continuous p t q w
  unfold naturalStateReal naturalStateImag
  exact ⟨((Complex.continuous_re.comp hc.fst).smul continuous_const).add
      ((Complex.continuous_re.comp hc.snd).smul continuous_const),
    ((Complex.continuous_im.comp hc.fst).smul continuous_const).add
      ((Complex.continuous_im.comp hc.snd).smul continuous_const)⟩

theorem naturalProtocolStored_weight (u : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + u) ↔ Admitted n)
    (p t q : ℝ) (w : ℂ × ℂ) (τ : ℝ) :
    naturalStateWeight u (naturalProtocolStored p t q w τ) = naturalStateWeight u w := by
  unfold naturalProtocolStored
  rw [naturalStorage_weight u hrec, naturalProtocol_weight u hrec]

theorem naturalProtocolStored_support (u : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + u) ↔ Admitted n)
    (p t q : ℝ) (w : ℂ × ℂ) (τ : ℝ) (v : Vertex) (hv : v ∉ naturalRemoteCell u) :
    naturalStateReal u (naturalProtocolStored p t q w τ) v = 0 ∧
    naturalStateImag u (naturalProtocolStored p t q w τ) v = 0 :=
  naturalState_support u hrec _ v hv

theorem naturalProtocolStored_solves_first (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (p t q : ℝ) (w : ℂ × ℂ) {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    naturalSolvesAt v.val (1 / 16) p (naturalProtocolStored p t q w) s := by
  apply naturalSolvesAt_congr v.val (1 / 16) p (naturalProtocolPair p t q w)
    (naturalProtocolStored p t q w) s (naturalProtocol_solves_first v hr hrec p t q w h0 h1)
  filter_upwards [Ioo_mem_nhds h0 h1] with τ hτ
  exact (naturalProtocolStored_before p t q w τ (by linarith [hτ.2])).symm

theorem naturalProtocolStored_solves_second (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (p t q : ℝ) (w : ℂ × ℂ) {s : ℝ} (h1 : 1 < s) (h2 : s < 2) :
    naturalSolvesAt v.val (1 / 16 + -2*t) 0 (naturalProtocolStored p t q w) s := by
  apply naturalSolvesAt_congr v.val (1 / 16 + -2*t) 0 (naturalProtocolPair p t q w)
    (naturalProtocolStored p t q w) s (naturalProtocol_solves_second v hr hrec p t q w h1 h2)
  filter_upwards [Ioo_mem_nhds h1 h2] with τ hτ
  exact (naturalProtocolStored_before p t q w τ (by linarith [hτ.2])).symm

theorem naturalProtocolStored_solves_third (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (p t q : ℝ) (w : ℂ × ℂ) {s : ℝ} (h2 : 2 < s) (h3 : s < 3) :
    naturalSolvesAt v.val (1 / 16) q (naturalProtocolStored p t q w) s := by
  apply naturalSolvesAt_congr v.val (1 / 16) q (naturalProtocolPair p t q w)
    (naturalProtocolStored p t q w) s (naturalProtocol_solves_third v hr hrec p t q w h2 h3)
  filter_upwards [Ioo_mem_nhds h2 h3] with τ hτ
  exact (naturalProtocolStored_before p t q w τ hτ.2.le).symm

theorem naturalProtocolStored_solves_after (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (p t q : ℝ) (w : ℂ × ℂ) {s : ℝ} (h3 : 3 < s) :
    naturalFullSolvesAt canonicalPlateauHamiltonian
      (fun τ => naturalStateReal v.val (naturalProtocolStored p t q w τ))
      (fun τ => naturalStateImag v.val (naturalProtocolStored p t q w τ)) s := by
  have h : naturalSolvesAt v.val 0 0 (naturalProtocolStored p t q w) s := by
    apply naturalSolvesAt_congr v.val 0 0
      (fun τ => naturalStoragePair (τ-3) (naturalProtocolPair p t q w 3))
      (naturalProtocolStored p t q w) s
    · exact naturalSolvesAt_shift _ _ _ _ 3 s
        (naturalStorage_solvesAt v hr hrec (naturalProtocolPair p t q w 3) (s-3))
    · filter_upwards [Ioi_mem_nhds h3] with τ hτ
      exact (naturalProtocolStored_after p t q w τ hτ.le).symm
  unfold naturalSolvesAt at h
  simpa only [naturalRemoteDriven, zero_smul, add_zero] using h

/-- The prepared state recurs after a full free relative period. -/
theorem naturalProtocolStored_return (p t q : ℝ) (w : ℂ × ℂ) :
    naturalProtocolStored p t q w (3 + 32 * Real.pi) =
      let z := coordinatedPhase (-(canonicalPlateauHeight + 3 / 16) * (32 * Real.pi))
      let u := naturalProtocolPair p t q w 3
      (z * u.1,z * u.2) := by
  rw [naturalProtocolStored_after p t q w _ (by linarith [Real.pi_pos]),
    show (3 + 32 * Real.pi : ℝ) - 3 = 32 * Real.pi by ring]
  exact naturalStorage_period_return _

end
end SpectralGeometry.AmmannBeenker
