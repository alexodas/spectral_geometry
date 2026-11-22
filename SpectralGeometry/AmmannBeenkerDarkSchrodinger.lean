module

public import SpectralGeometry.AmmannBeenkerPostpulseSwitchOff
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul

public section

/-!
# An explicit exact Schrödinger trajectory for the selected-edge dark state

The full quantum propagator on the complex infinite graph has not
yet been built. Nevertheless, the selected edge has an exceptional
eigenvector: the normalized dark mode (compactA + compactB)/4 is
an exact full-natural-domain eigenstate at energy E_* for EVERY
real strength ε, because the edge annihilates it.

We construct its exact time-dependent phase, using the real and
imaginary components of exp(-i E_* τ) dark. These components are
ordinary real full-graph Hilbert vectors, both coming from the
same natural-domain dark eigenvector. The pair represents an
explicit complex trajectory; the two derivative identities
verify the real and imaginary parts of

    i ∂_τ ψ(τ) = (K_* + ε W) ψ(τ).

Its squared complex norm is one and its two components have
zero leakage at all times. This constructs ONE genuine exact
Schrödinger solution, not the full complex Hilbert-space
propagator, not an arbitrary initial-state solution, and not
a controlled A/B rotation.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- Real part of the exact dark-state phase exp(-i E_* τ). -/
@[expose] def crossingDarkPhaseReal (τ : ℝ) : TileHilbert Vertex :=
  Real.cos (crossingEnergy * τ) • crossingDark

/-- Imaginary part of the same phase, with the physical minus
sign in exp(-i E_* τ). -/
@[expose] def crossingDarkPhaseImag (τ : ℝ) : TileHilbert Vertex :=
  (-Real.sin (crossingEnergy * τ)) • crossingDark

/-- Real phase component, regarded as a vector in the natural
domain of the exact unbounded graph Hamiltonian. -/
@[expose] def domainCrossingDarkPhaseReal (τ : ℝ) :
    infiniteOnsiteDomain potential :=
  Real.cos (crossingEnergy * τ) • domainCrossingDark

/-- Imaginary phase component in the same natural domain. -/
@[expose] def domainCrossingDarkPhaseImag (τ : ℝ) :
    infiniteOnsiteDomain potential :=
  (-Real.sin (crossingEnergy * τ)) • domainCrossingDark

theorem crossingDarkPhaseReal_coe (τ : ℝ) :
    (domainCrossingDarkPhaseReal τ : TileHilbert Vertex) =
      crossingDarkPhaseReal τ := by
  rfl

theorem crossingDarkPhaseImag_coe (τ : ℝ) :
    (domainCrossingDarkPhaseImag τ : TileHilbert Vertex) =
      crossingDarkPhaseImag τ := by
  rfl

/-- Both phase components remain exact eigenvectors of the
full selected-edge Hamiltonian on its original natural domain. -/
theorem crossingDarkPhaseReal_eigen (ε τ : ℝ) :
    onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge)
        (domainCrossingDarkPhaseReal τ) =
      crossingEnergy • crossingDarkPhaseReal τ := by
  simp only [domainCrossingDarkPhaseReal, crossingDarkPhaseReal,
    map_smul, crossingDark_full_eigenvector, smul_comm]

theorem crossingDarkPhaseImag_eigen (ε τ : ℝ) :
    onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge)
        (domainCrossingDarkPhaseImag τ) =
      crossingEnergy • crossingDarkPhaseImag τ := by
  simp only [domainCrossingDarkPhaseImag, crossingDarkPhaseImag,
    map_smul, crossingDark_full_eigenvector, smul_comm]

/-- Exact initial condition: at time zero the complex state
has real part dark and zero imaginary part. -/
theorem crossingDarkPhase_initial :
    crossingDarkPhaseReal 0 = crossingDark ∧
      crossingDarkPhaseImag 0 = 0 := by
  simp [crossingDarkPhaseReal, crossingDarkPhaseImag]

/-- The dark mode is normalized in the real full Hilbert space. -/
theorem crossingDark_norm_one : ‖crossingDark‖ = 1 := by
  have h := crossingDark_norm_sq
  nlinarith [norm_nonneg crossingDark]

/-- The squared norm of the real and imaginary components
sums to one for every time: an exact complex normalization
identity, with no leakage or small-pulse assumption. -/
theorem crossingDarkPhase_complex_norm_sq (τ : ℝ) :
    ‖crossingDarkPhaseReal τ‖ ^ 2 +
      ‖crossingDarkPhaseImag τ‖ ^ 2 = 1 := by
  simp only [crossingDarkPhaseReal, crossingDarkPhaseImag,
    norm_smul, Real.norm_eq_abs, crossingDark_norm_one,
    mul_one, abs_neg, sq_abs]
  exact Real.cos_sq_add_sin_sq (crossingEnergy * τ)

/-- Derivative of the real part of the exact complex phase. -/
theorem crossingDarkPhaseReal_hasDerivAt (τ : ℝ) :
    HasDerivAt crossingDarkPhaseReal
      ((-Real.sin (crossingEnergy * τ) * crossingEnergy) •
        crossingDark) τ := by
  have hlin :
      HasDerivAt (fun s : ℝ => crossingEnergy * s)
        crossingEnergy τ :=
    hasDerivAt_const_mul crossingEnergy
  have hcos :
      HasDerivAt (fun s : ℝ => Real.cos (crossingEnergy * s))
        (-Real.sin (crossingEnergy * τ) * crossingEnergy) τ := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_cos (crossingEnergy * τ)).comp τ hlin
  exact hcos.smul_const crossingDark

/-- Derivative of the imaginary part of the exact complex phase. -/
theorem crossingDarkPhaseImag_hasDerivAt (τ : ℝ) :
    HasDerivAt crossingDarkPhaseImag
      (-(Real.cos (crossingEnergy * τ) * crossingEnergy) •
        crossingDark) τ := by
  have hlin :
      HasDerivAt (fun s : ℝ => crossingEnergy * s)
        crossingEnergy τ :=
    hasDerivAt_const_mul crossingEnergy
  have hsin :
      HasDerivAt (fun s : ℝ => Real.sin (crossingEnergy * s))
        (Real.cos (crossingEnergy * τ) * crossingEnergy) τ := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_sin (crossingEnergy * τ)).comp τ hlin
  exact hsin.neg.smul_const crossingDark

/-- The REAL part of the Schrödinger equation:
∂_τ Re ψ = K_ε Im ψ.
The operator is the ACTUAL unbounded infinite-graph operator,
on the natural domain, with the chosen edge at strength ε. -/
theorem crossingDarkPhase_real_Schrodinger (ε τ : ℝ) :
    HasDerivAt crossingDarkPhaseReal
      (onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge)
        (domainCrossingDarkPhaseImag τ)) τ := by
  have h := crossingDarkPhaseReal_hasDerivAt τ
  simpa only [crossingDarkPhaseImag_eigen, crossingDarkPhaseImag,
    smul_smul] using h

/-- The IMAGINARY part of the Schrödinger equation:
∂_τ Im ψ = - K_ε Re ψ. Together with the preceding theorem
this verifies i ∂_τ ψ = K_ε ψ for the exact dark trajectory. -/
theorem crossingDarkPhase_imag_Schrodinger (ε τ : ℝ) :
    HasDerivAt crossingDarkPhaseImag
      (-(onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge)
        (domainCrossingDarkPhaseReal τ))) τ := by
  have h := crossingDarkPhaseImag_hasDerivAt τ
  simpa only [crossingDarkPhaseReal_eigen, crossingDarkPhaseReal,
    smul_smul, neg_smul] using h

/-- The two-mode projection fixes the normalized dark eigenstate. -/
theorem crossingDark_qubitPart_eq :
    crossingQubitPart crossingDark = crossingDark := by
  have ha : crossingCoeffA crossingDark = 1 / 4 := by
    simp only [crossingCoeffA, crossingDark, real_inner_smul_right,
      inner_add_right, compactA_inner_self, compactA_inner_compactB]
    norm_num
  have hb : crossingCoeffB crossingDark = 1 / 4 := by
    simp only [crossingCoeffB, crossingDark, real_inner_smul_right,
      inner_add_right, compactB_inner_self, real_inner_comm,
      compactA_inner_compactB]
    norm_num
  simp only [crossingQubitPart, ha, hb, crossingDark, smul_add]

/-- The dark mode has exactly zero amplitude outside the A/B plane. -/
theorem crossingDark_leakage_zero : crossingLeakage crossingDark = 0 :=
  (crossingLeakage_eq_zero_iff crossingDark).mpr
    crossingDark_qubitPart_eq.symm

/-- The real component of the exact dark quantum trajectory
never leaks outside the two-mode plane. -/
theorem crossingDarkPhaseReal_leakage_zero (τ : ℝ) :
    crossingLeakage (crossingDarkPhaseReal τ) = 0 := by
  rw [crossingDarkPhaseReal, crossingLeakage_smul,
    crossingDark_leakage_zero, smul_zero]

/-- Neither does the imaginary component. Thus the physical
complex trajectory has exactly zero leakage for all times. -/
theorem crossingDarkPhaseImag_leakage_zero (τ : ℝ) :
    crossingLeakage (crossingDarkPhaseImag τ) = 0 := by
  rw [crossingDarkPhaseImag, crossingLeakage_smul,
    crossingDark_leakage_zero, smul_zero]

end
end SpectralGeometry.AmmannBeenker
