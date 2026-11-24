module

public import SpectralGeometry.AmmannBeenkerCoordinatedPulseComposition

public section

/-!
# Arbitrary normalized state preparation with exactly zero leakage (L7c.4)

The three actual natural-domain pulses realize the constructive Euler
state preparation, with a retained common scalar phase. The bundled
theorem states the initial and final states, continuity, domain
membership, norm conservation, zero leakage at every time and the
full graph Schroedinger equations on each open pulse interval.

This is an existence theorem for trajectories in the compact plane,
represented by real and imaginary full-space components. It is not
a general unitary propagator for arbitrary infinite-space initial data.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- The total scalar phase of the unit-duration Z-X-Z protocol. -/
@[expose] def coordinatedProtocolAngle (p t q : ℝ) : ℝ :=
  -(crossingEnergy + q) + -(crossingEnergy - t) + -(crossingEnergy + p)

theorem coordinatedProtocolAngle_eq (p t q : ℝ) :
    coordinatedProtocolAngle p t q = -3 * crossingEnergy + t - p - q := by
  unfold coordinatedProtocolAngle
  ring

theorem coordinatedProtocolPhase_norm (p t q : ℝ) :
    ‖coordinatedPhase (coordinatedProtocolAngle p t q)‖ = 1 :=
  coordinatedPhase_norm _

private theorem coordinatedScaledMatrix_mul (z u : ℂ)
    (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    (z • M) * (u • N) = (z * u) • (M * N) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The exact physical endpoint matrix retains the common phase.
All three pulse parameters may be arbitrary real numbers. -/
theorem coordinatedProtocolMatrix_rotation (p t q : ℝ) :
    coordinatedZAxisMatrix q 1 * coordinatedXAxisMatrix (-2*t) 1 *
      coordinatedZAxisMatrix p 1 =
    coordinatedPhase (coordinatedProtocolAngle p t q) •
      (coordinatedRotationZ q * coordinatedRotationX t * coordinatedRotationZ p) := by
  rw [coordinatedZAxisMatrix_rotation q 1, coordinatedXAxisMatrix_rotation,
    coordinatedZAxisMatrix_rotation p 1]
  have ht : -(-2*t) * (1 : ℝ) / 2 = t := by ring
  have he : -(crossingEnergy + (-2*t)/2) * (1 : ℝ) =
      -(crossingEnergy-t) := by ring
  rw [ht, he]
  simp only [mul_one]
  rw [coordinatedScaledMatrix_mul, coordinatedScaledMatrix_mul]
  unfold coordinatedProtocolAngle
  rw [coordinatedPhase_add, coordinatedPhase_add]

/-- The exact endpoint for any initial coefficient pair. -/
theorem coordinatedProtocol_final_rotation (p t q : ℝ) (w : ℂ × ℂ) :
    coordinatedProtocolPair p t q w 3 =
      let v := coordinatedApplyPair
        (coordinatedRotationZ q * coordinatedRotationX t * coordinatedRotationZ p)
        w.1 w.2
      (coordinatedPhase (coordinatedProtocolAngle p t q) * v.1,
       coordinatedPhase (coordinatedProtocolAngle p t q) * v.2) := by
  rw [coordinatedProtocol_final]
  unfold coordinatedPulseX coordinatedPulseZ
  rw [coordinatedApplyPair_mul, coordinatedApplyPair_mul]
  rw [coordinatedProtocolMatrix_rotation, coordinatedApplyPair_smul]

theorem coordinatedProtocol_final_dark (p t q : ℝ) :
    coordinatedProtocolPair p t q (1,0) 3 =
      (coordinatedPhase (coordinatedProtocolAngle p t q) *
        ((Real.cos t : ℂ) * coordinatedPhase (p+q)),
       coordinatedPhase (coordinatedProtocolAngle p t q) *
        (Complex.I * (Real.sin t : ℂ) * coordinatedPhase (p-q))) := by
  rw [coordinatedProtocol_final_rotation]
  dsimp only
  rw [coordinatedApplyPair_dark]
  dsimp only
  rw [(coordinatedEuler_dark_column p t q).1,
    (coordinatedEuler_dark_column p t q).2]

/-- The complex coefficient endpoint realizes every normalized target
from dark, up to the explicitly retained phase of modulus one. -/
theorem coordinatedProtocol_reaches_from_dark (a b : ℂ)
    (hn : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    ∃ p t q : ℝ, 0 ≤ t ∧ t ≤ Real.pi / 2 ∧
      coordinatedProtocolPair p t q (1,0) 3 =
        (coordinatedPhase (coordinatedProtocolAngle p t q) * a,
         coordinatedPhase (coordinatedProtocolAngle p t q) * b) := by
  obtain ⟨p,t,q,h0,h1,ha,hb⟩ := coordinatedEuler_reaches_from_dark a b hn
  refine ⟨p,t,q,h0,h1,?_⟩
  rw [coordinatedProtocol_final_rotation]
  dsimp only
  rw [coordinatedApplyPair_dark]
  dsimp only
  rw [ha,hb]

theorem coordinatedState_dark_initial :
    coordinatedStateReal (1,0) = crossingDark ∧
    coordinatedStateImag (1,0) = 0 := by
  simp [coordinatedStateReal, coordinatedStateImag,
    coordinatedEmbedReal, coordinatedEmbedImag]

theorem coordinatedProtocol_dark_weight (p t q τ : ℝ) :
    coordinatedStateWeight (coordinatedProtocolPair p t q (1,0) τ) = 1 := by
  rw [coordinatedProtocol_weight, coordinatedStateWeight_eq]
  norm_num

/-- Arbitrary normalized target preparation on the actual infinite graph.

The full Hilbert vectors are the real and imaginary components of
the coefficient trajectory. Both lie on the original natural domain
for every time, their squared complex norm is one, and both exterior
components vanish exactly, including at the switches. Their actual
Schroedinger equations hold on the three open intervals, with
(delta,eta) = (0,p), (-2*t,0), (0,q). The endpoint equals the target
up to the explicit common phase. No small-control or supplied
propagator assumption is made. -/
theorem coordinatedProtocol_exact_preparation (a b : ℂ)
    (hn : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    ∃ p t q : ℝ, 0 ≤ t ∧ t ≤ Real.pi / 2 ∧
      let f := coordinatedProtocolPair p t q (1,0)
      let z := coordinatedPhase (coordinatedProtocolAngle p t q)
      ‖z‖ = 1 ∧
      f 0 = (1,0) ∧
      coordinatedStateReal (f 0) = crossingDark ∧
      coordinatedStateImag (f 0) = 0 ∧
      f 3 = (z*a,z*b) ∧
      coordinatedStateReal (f 3) =
        (z*a).re • crossingDark + (z*b).re • crossingBright ∧
      coordinatedStateImag (f 3) =
        (z*a).im • crossingDark + (z*b).im • crossingBright ∧
      Continuous f ∧
      Continuous (fun τ => coordinatedStateReal (f τ)) ∧
      Continuous (fun τ => coordinatedStateImag (f τ)) ∧
      (∀ τ : ℝ, coordinatedStateReal (f τ) ∈ infiniteOnsiteDomain potential ∧
        coordinatedStateImag (f τ) ∈ infiniteOnsiteDomain potential ∧
        ‖coordinatedStateReal (f τ)‖ ^ 2 + ‖coordinatedStateImag (f τ)‖ ^ 2 = 1 ∧
        crossingLeakage (coordinatedStateReal (f τ)) = 0 ∧
        crossingLeakage (coordinatedStateImag (f τ)) = 0) ∧
      (∀ τ : ℝ, 0 < τ → τ < 1 → coordinatedSolvesAt 0 p f τ) ∧
      (∀ τ : ℝ, 1 < τ → τ < 2 → coordinatedSolvesAt (-2*t) 0 f τ) ∧
      (∀ τ : ℝ, 2 < τ → τ < 3 → coordinatedSolvesAt 0 q f τ) := by
  obtain ⟨p,t,q,h0,h1,hend⟩ := coordinatedProtocol_reaches_from_dark a b hn
  refine ⟨p,t,q,h0,h1,?_⟩
  dsimp only
  have hinit := coordinatedProtocol_initial p t q (1,0)
  have hc := coordinatedProtocol_state_continuous p t q (1,0)
  refine ⟨coordinatedProtocolPhase_norm p t q, hinit, ?_, ?_,
    hend, ?_, ?_, coordinatedProtocol_continuous p t q (1,0),
    hc.1, hc.2, ?_, ?_, ?_, ?_⟩
  · rw [hinit]
    exact coordinatedState_dark_initial.1
  · rw [hinit]
    exact coordinatedState_dark_initial.2
  · rw [hend]
    rfl
  · rw [hend]
    rfl
  · intro τ
    have hd := coordinatedProtocol_domain p t q (1,0) τ
    have hl := coordinatedProtocol_leakage_zero p t q (1,0) τ
    exact ⟨hd.1, hd.2, coordinatedProtocol_dark_weight p t q τ, hl.1, hl.2⟩
  · intro τ hτ0 hτ1
    exact coordinatedProtocol_solves_first p t q (1,0) hτ0 hτ1
  · intro τ hτ1 hτ2
    exact coordinatedProtocol_solves_second p t q (1,0) hτ1 hτ2
  · intro τ hτ2 hτ3
    exact coordinatedProtocol_solves_third p t q (1,0) hτ2 hτ3

end
end SpectralGeometry.AmmannBeenker
