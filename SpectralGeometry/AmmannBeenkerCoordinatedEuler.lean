module

public import SpectralGeometry.AmmannBeenkerCoordinatedLieAlgebra

public section

/-!
# Constructive Euler state preparation in two complex coordinates (L7b)

These are exact finite-dimensional rotation identities, not a construction
of the infinite complex Hamiltonian or of its time-dependent propagator.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

@[expose] def coordinatedPhase (t : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) * Complex.I)

theorem coordinatedPhase_add (s t : ℝ) :
    coordinatedPhase (s + t) = coordinatedPhase s * coordinatedPhase t := by
  unfold coordinatedPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem coordinatedPhase_norm (t : ℝ) : ‖coordinatedPhase t‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I t

/-- Rotation with generator i sigma_x. The parameter is the half-angle
in the Bloch-sphere convention. -/
@[expose] def coordinatedRotationX (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos t : ℂ), Complex.I * (Real.sin t : ℂ);
     Complex.I * (Real.sin t : ℂ), (Real.cos t : ℂ)]

/-- Rotation with generator i sigma_z. -/
@[expose] def coordinatedRotationZ (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![coordinatedPhase t, 0; 0, coordinatedPhase (-t)]

/-- The first column of a Z-X-Z sequence, i.e. its action on dark. -/
theorem coordinatedEuler_dark_column (p t q : ℝ) :
    ((coordinatedRotationZ q * coordinatedRotationX t * coordinatedRotationZ p) 0 0 =
      (Real.cos t : ℂ) * coordinatedPhase (p + q)) ∧
    ((coordinatedRotationZ q * coordinatedRotationX t * coordinatedRotationZ p) 1 0 =
      Complex.I * (Real.sin t : ℂ) * coordinatedPhase (p - q)) := by
  constructor
  · rw [coordinatedPhase_add]
    simp [coordinatedRotationZ, coordinatedRotationX, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · rw [sub_eq_add_neg, coordinatedPhase_add]
    simp [coordinatedRotationZ, coordinatedRotationX, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Every normalized complex pair is obtained from the dark coordinate
by three rotations. The angle of the middle rotation is nonnegative
and at most pi/2. No nonzero-coordinate assumption is needed. -/
theorem coordinatedEuler_reaches_from_dark (a b : ℂ)
    (hn : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    ∃ p t q : ℝ, 0 ≤ t ∧ t ≤ Real.pi / 2 ∧
      (coordinatedRotationZ q * coordinatedRotationX t * coordinatedRotationZ p) 0 0 = a ∧
      (coordinatedRotationZ q * coordinatedRotationX t * coordinatedRotationZ p) 1 0 = b := by
  let u := Complex.arg a
  let v := Complex.arg (-Complex.I * b)
  let t := Real.arccos ‖a‖
  have hle : ‖a‖ ≤ 1 := by
    nlinarith [norm_nonneg a, sq_nonneg ‖b‖]
  have hcos : Real.cos t = ‖a‖ := by
    exact Real.cos_arccos (by linarith [norm_nonneg a]) hle
  have hsin : Real.sin t = ‖b‖ := by
    dsimp [t]
    rw [Real.sin_arccos, show 1 - ‖a‖ ^ 2 = ‖b‖ ^ 2 by linarith,
      Real.sqrt_sq (norm_nonneg b)]
  have ha : (‖a‖ : ℂ) * coordinatedPhase u = a := by
    exact Complex.norm_mul_exp_arg_mul_I a
  have hbNorm : ‖-Complex.I * b‖ = ‖b‖ := by simp [norm_mul]
  have hb : (‖b‖ : ℂ) * coordinatedPhase v = -Complex.I * b := by
    simpa only [v, coordinatedPhase, hbNorm] using
      (Complex.norm_mul_exp_arg_mul_I (-Complex.I * b))
  refine ⟨(u + v) / 2, t, (u - v) / 2, Real.arccos_nonneg _,
    Real.arccos_le_pi_div_two.mpr (norm_nonneg a), ?_, ?_⟩
  · rw [(coordinatedEuler_dark_column _ _ _).1, hcos,
      show (u + v) / 2 + (u - v) / 2 = u by ring, ha]
  · rw [(coordinatedEuler_dark_column _ _ _).2, hsin,
      show (u + v) / 2 - (u - v) / 2 = v by ring,
      mul_assoc, hb]
    calc
      Complex.I * (-Complex.I * b) = -(Complex.I * Complex.I) * b := by ring
      _ = b := by rw [Complex.I_mul_I]; ring

/-- The two independent traceless generator coefficients after removing
the common scalar energy. This is an algebraic pulse parametrization. -/
@[expose] def coordinatedReducedGenerator (δ η : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((-δ / 2 : ℝ) : ℂ) • coordinatedLieX + (η : ℂ) • coordinatedLieZ

/-- Arbitrary signed rotation strengths can be selected independently.
For a unit-duration segment, the corresponding detuning is -2*t. -/
theorem coordinatedReducedGenerator_X (t : ℝ) :
    coordinatedReducedGenerator (-2 * t) 0 = (t : ℂ) • coordinatedLieX := by
  unfold coordinatedReducedGenerator
  rw [show -(-2 * t) / 2 = t by ring]
  simp

theorem coordinatedReducedGenerator_Z (t : ℝ) :
    coordinatedReducedGenerator 0 t = (t : ℂ) • coordinatedLieZ := by
  simp [coordinatedReducedGenerator]

end
end SpectralGeometry.AmmannBeenker
