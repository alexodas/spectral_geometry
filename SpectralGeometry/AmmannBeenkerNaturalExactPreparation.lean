module

public import SpectralGeometry.AmmannBeenkerNaturalPulseComposition

public section

/-!
# Exact arbitrary state preparation on a natural recurring plateau cell

The compensated pulses have the same rotation generators as the
central protocol but a different common physical energy. We retain
that phase and certify the endpoint of the actual remote trajectories.
This establishes reachability from the normalized dark state with
continuous full-space dynamics and no leakage. No positive collective
gap, arbitrarily weak control or tensor-product register is assumed.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- The actual detuning evolution in dark/bright coordinates, obtained
from the two compact eigenmode phases, before removing any common phase. -/
@[expose] def naturalXAxisMatrix (δ τ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let p := coordinatedPhase (-(naturalPulseEnergy + δ) * τ)
  let q := coordinatedPhase (-naturalPulseEnergy * τ)
  !![(p + q) / 2, (p - q) / 2; (p - q) / 2, (p + q) / 2]

/-- The actual coordinated-edge evolution in dark/bright coordinates. -/
@[expose] def naturalZAxisMatrix (η τ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![coordinatedPhase (-naturalPulseEnergy * τ), 0;
     0, coordinatedPhase (-(naturalPulseEnergy + 2 * η) * τ)]

private theorem naturalPhase_sum_diff (c t : ℝ) :
    (coordinatedPhase (c + t) + coordinatedPhase (c - t)) / 2 =
      coordinatedPhase c * (Real.cos t : ℂ) ∧
    (coordinatedPhase (c + t) - coordinatedPhase (c - t)) / 2 =
      coordinatedPhase c * (Complex.I * (Real.sin t : ℂ)) := by
  rw [coordinatedPhase_add, sub_eq_add_neg, coordinatedPhase_add,
    coordinatedPhase_trig t, coordinatedPhase_trig (-t)]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  constructor <;> ring

/-- Detuning is precisely an X rotation, times the common energy phase. -/
theorem naturalXAxisMatrix_rotation (δ τ : ℝ) :
    naturalXAxisMatrix δ τ =
      coordinatedPhase (-(naturalPulseEnergy + δ / 2) * τ) •
        coordinatedRotationX (-δ * τ / 2) := by
  have hp : -(naturalPulseEnergy + δ) * τ =
      -(naturalPulseEnergy + δ / 2) * τ + (-δ * τ / 2) := by ring
  have hq : -naturalPulseEnergy * τ =
      -(naturalPulseEnergy + δ / 2) * τ - (-δ * τ / 2) := by ring
  have h := naturalPhase_sum_diff (-(naturalPulseEnergy + δ / 2) * τ)
    (-δ * τ / 2)
  unfold naturalXAxisMatrix
  dsimp only
  rw [hp, hq]
  ext i j
  fin_cases i <;> fin_cases j
  · exact h.1
  · exact h.2
  · exact h.2
  · exact h.1

/-- Coordinated inter-ring changes are precisely a Z rotation, times
the common energy phase. -/
theorem naturalZAxisMatrix_rotation (η τ : ℝ) :
    naturalZAxisMatrix η τ =
      coordinatedPhase (-(naturalPulseEnergy + η) * τ) •
        coordinatedRotationZ (η * τ) := by
  have hp : -naturalPulseEnergy * τ =
      -(naturalPulseEnergy + η) * τ + η * τ := by ring
  have hq : -(naturalPulseEnergy + 2 * η) * τ =
      -(naturalPulseEnergy + η) * τ + -(η * τ) := by ring
  unfold naturalZAxisMatrix
  rw [hp, hq, coordinatedPhase_add, coordinatedPhase_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coordinatedRotationZ]

/-- The coefficient pair after a detuning pulse, using the original
unnormalized compact modes with coefficients (a+b)/4 and (a-b)/4. -/
theorem naturalXAxisMatrix_coefficients (δ τ : ℝ) (a b : ℂ) :
    coordinatedApplyPair (naturalXAxisMatrix δ τ) a b =
      (2 * (coordinatedEigenCoeff (naturalPulseEnergy + δ) ((a + b) / 4) τ +
            coordinatedEigenCoeff naturalPulseEnergy ((a - b) / 4) τ),
       2 * (coordinatedEigenCoeff (naturalPulseEnergy + δ) ((a + b) / 4) τ -
            coordinatedEigenCoeff naturalPulseEnergy ((a - b) / 4) τ)) := by
  apply Prod.ext <;>
    simp [coordinatedApplyPair, naturalXAxisMatrix, coordinatedEigenCoeff] <;> ring

theorem naturalZAxisMatrix_coefficients (η τ : ℝ) (a b : ℂ) :
    coordinatedApplyPair (naturalZAxisMatrix η τ) a b =
      (coordinatedEigenCoeff naturalPulseEnergy a τ,
       coordinatedEigenCoeff (naturalPulseEnergy + 2 * η) b τ) := by
  apply Prod.ext <;>
    simp [coordinatedApplyPair, naturalZAxisMatrix, coordinatedEigenCoeff]


theorem naturalPulseX_eq_matrix (d τ : ℝ) (w : ℂ × ℂ) :
    naturalPulseX d τ w = coordinatedApplyPair (naturalXAxisMatrix d τ) w.1 w.2 := by
  rw [naturalXAxisMatrix_coefficients]
  rfl

theorem naturalPulseZ_eq_matrix (η τ : ℝ) (w : ℂ × ℂ) :
    naturalPulseZ η τ w = coordinatedApplyPair (naturalZAxisMatrix η τ) w.1 w.2 := by
  rw [naturalZAxisMatrix_coefficients]
  rfl

/-- The total scalar phase of the unit-duration Z-X-Z protocol. -/
@[expose] def naturalProtocolAngle (p t q : ℝ) : ℝ :=
  -(naturalPulseEnergy + q) + -(naturalPulseEnergy - t) + -(naturalPulseEnergy + p)

theorem naturalProtocolAngle_eq (p t q : ℝ) :
    naturalProtocolAngle p t q = -3 * naturalPulseEnergy + t - p - q := by
  unfold naturalProtocolAngle
  ring

theorem naturalProtocolPhase_norm (p t q : ℝ) :
    ‖coordinatedPhase (naturalProtocolAngle p t q)‖ = 1 :=
  coordinatedPhase_norm _

private theorem naturalScaledMatrix_mul (z u : ℂ)
    (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    (z • M) * (u • N) = (z * u) • (M * N) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The exact physical endpoint matrix retains the common phase.
All three pulse parameters may be arbitrary real numbers. -/
theorem naturalProtocolMatrix_rotation (p t q : ℝ) :
    naturalZAxisMatrix q 1 * naturalXAxisMatrix (-2*t) 1 *
      naturalZAxisMatrix p 1 =
    coordinatedPhase (naturalProtocolAngle p t q) •
      (coordinatedRotationZ q * coordinatedRotationX t * coordinatedRotationZ p) := by
  rw [naturalZAxisMatrix_rotation q 1, naturalXAxisMatrix_rotation,
    naturalZAxisMatrix_rotation p 1]
  have ht : -(-2*t) * (1 : ℝ) / 2 = t := by ring
  have he : -(naturalPulseEnergy + (-2*t)/2) * (1 : ℝ) =
      -(naturalPulseEnergy-t) := by ring
  rw [ht, he]
  simp only [mul_one]
  rw [naturalScaledMatrix_mul, naturalScaledMatrix_mul]
  unfold naturalProtocolAngle
  rw [coordinatedPhase_add, coordinatedPhase_add]

/-- The exact endpoint for any initial coefficient pair. -/
theorem naturalProtocol_final_rotation (p t q : ℝ) (w : ℂ × ℂ) :
    naturalProtocolPair p t q w 3 =
      let v := coordinatedApplyPair
        (coordinatedRotationZ q * coordinatedRotationX t * coordinatedRotationZ p)
        w.1 w.2
      (coordinatedPhase (naturalProtocolAngle p t q) * v.1,
       coordinatedPhase (naturalProtocolAngle p t q) * v.2) := by
  rw [naturalProtocol_final]
  simp only [naturalPulseX_eq_matrix, naturalPulseZ_eq_matrix]
  rw [coordinatedApplyPair_mul, coordinatedApplyPair_mul]
  rw [naturalProtocolMatrix_rotation, coordinatedApplyPair_smul]

theorem naturalProtocol_final_dark (p t q : ℝ) :
    naturalProtocolPair p t q (1,0) 3 =
      (coordinatedPhase (naturalProtocolAngle p t q) *
        ((Real.cos t : ℂ) * coordinatedPhase (p+q)),
       coordinatedPhase (naturalProtocolAngle p t q) *
        (Complex.I * (Real.sin t : ℂ) * coordinatedPhase (p-q))) := by
  rw [naturalProtocol_final_rotation]
  dsimp only
  rw [coordinatedApplyPair_dark]
  dsimp only
  rw [(coordinatedEuler_dark_column p t q).1,
    (coordinatedEuler_dark_column p t q).2]

/-- The complex coefficient endpoint realizes every normalized target
from dark, up to the explicitly retained phase of modulus one. -/
theorem naturalProtocol_reaches_from_dark (a b : ℂ)
    (hn : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    ∃ p t q : ℝ, 0 ≤ t ∧ t ≤ Real.pi / 2 ∧
      naturalProtocolPair p t q (1,0) 3 =
        (coordinatedPhase (naturalProtocolAngle p t q) * a,
         coordinatedPhase (naturalProtocolAngle p t q) * b) := by
  obtain ⟨p,t,q,h0,h1,ha,hb⟩ := coordinatedEuler_reaches_from_dark a b hn
  refine ⟨p,t,q,h0,h1,?_⟩
  rw [naturalProtocol_final_rotation]
  dsimp only
  rw [coordinatedApplyPair_dark]
  dsimp only
  rw [ha,hb]


theorem naturalState_dark_initial (u : Lattice) :
    naturalStateReal u (1,0) = naturalRemoteDark u ∧
    naturalStateImag u (1,0) = 0 := by
  simp [naturalStateReal, naturalStateImag]

theorem naturalProtocol_dark_weight (u : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + u) ↔ Admitted n)
    (p t q τ : ℝ) : naturalStateWeight u (naturalProtocolPair p t q (1,0) τ) = 1 := by
  rw [naturalProtocol_weight u hrec, naturalStateWeight_eq u hrec]
  norm_num

/-- Every normalized target in a certified remote natural plane is
reached from dark, up to a unit scalar phase, by three local pulses.
The actual bounded infinite-space equations hold on each open
segment and both components have zero amplitude off the cell at all
times, including the switches. The compensating detuning is explicit. -/
theorem naturalProtocol_exact_preparation (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (a b : ℂ) (hn : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    ∃ p t q : ℝ, 0 ≤ t ∧ t ≤ Real.pi / 2 ∧
      let f := naturalProtocolPair p t q (1,0)
      let z := coordinatedPhase (naturalProtocolAngle p t q)
      ‖z‖ = 1 ∧
      f 0 = (1,0) ∧
      naturalStateReal v.val (f 0) = naturalRemoteDark v.val ∧
      naturalStateImag v.val (f 0) = 0 ∧
      f 3 = (z*a,z*b) ∧
      naturalStateReal v.val (f 3) =
        (z*a).re • naturalRemoteDark v.val + (z*b).re • naturalRemoteBright v.val ∧
      naturalStateImag v.val (f 3) =
        (z*a).im • naturalRemoteDark v.val + (z*b).im • naturalRemoteBright v.val ∧
      Continuous f ∧
      Continuous (fun τ => naturalStateReal v.val (f τ)) ∧
      Continuous (fun τ => naturalStateImag v.val (f τ)) ∧
      (∀ τ : ℝ, ‖naturalStateReal v.val (f τ)‖ ^ 2 +
        ‖naturalStateImag v.val (f τ)‖ ^ 2 = 1 ∧
        ∀ w : Vertex, w ∉ naturalRemoteCell v.val →
          naturalStateReal v.val (f τ) w = 0 ∧ naturalStateImag v.val (f τ) w = 0) ∧
      (∀ τ : ℝ, 0 < τ → τ < 1 → naturalSolvesAt v.val (1 / 16) p f τ) ∧
      (∀ τ : ℝ, 1 < τ → τ < 2 → naturalSolvesAt v.val (1 / 16 + -2*t) 0 f τ) ∧
      (∀ τ : ℝ, 2 < τ → τ < 3 → naturalSolvesAt v.val (1 / 16) q f τ) := by
  obtain ⟨p,t,q,h0,h1,hend⟩ := naturalProtocol_reaches_from_dark a b hn
  refine ⟨p,t,q,h0,h1,?_⟩
  dsimp only
  have hinit := naturalProtocol_initial p t q (1,0)
  have hc := naturalProtocol_state_continuous v.val p t q (1,0)
  refine ⟨naturalProtocolPhase_norm p t q, hinit, ?_, ?_,
    hend, ?_, ?_, naturalProtocol_continuous p t q (1,0),
    hc.1, hc.2, ?_, ?_, ?_, ?_⟩
  · rw [hinit]
    exact (naturalState_dark_initial v.val).1
  · rw [hinit]
    exact (naturalState_dark_initial v.val).2
  · rw [hend]
    rfl
  · rw [hend]
    rfl
  · intro τ
    refine ⟨naturalProtocol_dark_weight v.val hrec p t q τ, ?_⟩
    intro w hw
    exact naturalProtocol_support v.val hrec p t q (1,0) τ w hw
  · intro τ hτ0 hτ1
    exact naturalProtocol_solves_first v hr hrec p t q (1,0) hτ0 hτ1
  · intro τ hτ1 hτ2
    exact naturalProtocol_solves_second v hr hrec p t q (1,0) hτ1 hτ2
  · intro τ hτ2 hτ3
    exact naturalProtocol_solves_third v hr hrec p t q (1,0) hτ2 hτ3

end
end SpectralGeometry.AmmannBeenker
