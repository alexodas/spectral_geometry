module

public import SpectralGeometry.AmmannBeenkerNaturalControlNorms
public import SpectralGeometry.AmmannBeenkerCoordinatedExactPreparation

public section

/-!
# Exact bounded-Hamiltonian dynamics on a natural cell

The two real Hilbert components represent a complex state. The actual
bounded infinite Hamiltonian appears in their differential equations.
Free evolution uses the distinct natural energies; a compensated
inter-ring pulse uses the normalized dark and bright directions.
No spectral gap or general infinite-space propagator is required.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

/-- Full infinite-space real component of a superposition of two eigenmodes. -/
@[expose] def naturalPairReal (x y : TileHilbert Vertex)
    (E F : ℝ) (a b : ℂ) (τ : ℝ) : TileHilbert Vertex :=
  (coordinatedEigenCoeff E a τ).re • x +
    (coordinatedEigenCoeff F b τ).re • y

@[expose] def naturalPairImag (x y : TileHilbert Vertex)
    (E F : ℝ) (a b : ℂ) (τ : ℝ) : TileHilbert Vertex :=
  (coordinatedEigenCoeff E a τ).im • x +
    (coordinatedEigenCoeff F b τ).im • y

theorem naturalPair_initial (x y : TileHilbert Vertex)
    (E F : ℝ) (a b : ℂ) :
    naturalPairReal x y E F a b 0 =
      a.re • x + b.re • y ∧
    naturalPairImag x y E F a b 0 =
      a.im • x + b.im • y := by
  simp [naturalPairReal, naturalPairImag, coordinatedEigenCoeff_initial]

/-- The actual full natural-domain Hamiltonian, not its compression,
appears in both real and imaginary equations. -/
theorem naturalPair_Schrodinger
    (B : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (x y : TileHilbert Vertex) (E F : ℝ)
    (hx : B x = E • x)
    (hy : B y = F • y)
    (a b : ℂ) (τ : ℝ) :
    HasDerivAt (naturalPairReal x y E F a b)
      (B (naturalPairImag x y E F a b τ)) τ ∧
    HasDerivAt (naturalPairImag x y E F a b)
      (-(B (naturalPairReal x y E F a b τ))) τ := by
  constructor
  · have hd := ((coordinatedEigenCoeff_re_deriv E a τ).smul_const
        x).add
        ((coordinatedEigenCoeff_re_deriv F b τ).smul_const y)
    have he :
        B (naturalPairImag x y E F a b τ) =
          (E * (coordinatedEigenCoeff E a τ).im) • x +
          (F * (coordinatedEigenCoeff F b τ).im) • y := by
      simp only [naturalPairImag, map_add, map_smul, hx, hy]
      module
    rw [he]
    exact hd
  · have hd := ((coordinatedEigenCoeff_im_deriv E a τ).smul_const
        x).add
        ((coordinatedEigenCoeff_im_deriv F b τ).smul_const y)
    have he :
        -(B (naturalPairReal x y E F a b τ)) =
          (-(E * (coordinatedEigenCoeff E a τ).re)) • x +
          (-(F * (coordinatedEigenCoeff F b τ).re)) • y := by
      simp only [naturalPairReal, map_add, map_smul, hx, hy]
      module
    rw [he]
    exact hd

private theorem naturalPair_real_norm_sq (x y : TileHilbert Vertex)
    (hxy : inner ℝ x y = 0) (u v : ℝ) :
    ‖u • x + v • y‖ ^ 2 =
      u ^ 2 * ‖x‖ ^ 2 + v ^ 2 * ‖y‖ ^ 2 := by
  have hyx : inner ℝ y x = 0 := by rw [real_inner_comm, hxy]
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hxy, hyx]
  ring

private theorem naturalComplex_norm_sq (z : ℂ) :
    z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Exact conserved squared complex norm for any orthogonal eigenpair,
including non-normalized eigenvectors. -/
theorem naturalPair_norm_sq (x y : TileHilbert Vertex)
    (hxy : inner ℝ x y = 0)
    (E F : ℝ) (a b : ℂ) (τ : ℝ) :
    ‖naturalPairReal x y E F a b τ‖ ^ 2 +
      ‖naturalPairImag x y E F a b τ‖ ^ 2 =
      ‖a‖ ^ 2 * ‖x‖ ^ 2 +
        ‖b‖ ^ 2 * ‖y‖ ^ 2 := by
  unfold naturalPairReal naturalPairImag
  rw [naturalPair_real_norm_sq _ _ hxy, naturalPair_real_norm_sq _ _ hxy]
  calc
    _ = ((coordinatedEigenCoeff E a τ).re ^ 2 +
          (coordinatedEigenCoeff E a τ).im ^ 2) * ‖x‖ ^ 2 +
        ((coordinatedEigenCoeff F b τ).re ^ 2 +
          (coordinatedEigenCoeff F b τ).im ^ 2) * ‖y‖ ^ 2 := by ring
    _ = _ := by rw [naturalComplex_norm_sq, naturalComplex_norm_sq,
        coordinatedEigenCoeff_norm, coordinatedEigenCoeff_norm]


@[expose] def naturalRemoteDark (t : Lattice) : TileHilbert Vertex :=
  (1 / 4 : ℝ) • (translatedCompactA t + translatedCompactB t)

@[expose] def naturalRemoteBright (t : Lattice) : TileHilbert Vertex :=
  (1 / 4 : ℝ) • (translatedCompactA t - translatedCompactB t)

theorem naturalRemoteDarkBright_orthonormal (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) :
    ‖naturalRemoteDark t‖ ^ 2 = 1 ∧
    ‖naturalRemoteBright t‖ ^ 2 = 1 ∧
    inner ℝ (naturalRemoteDark t) (naturalRemoteBright t) = 0 := by
  obtain ⟨ha, hb, hab⟩ := translatedCompact_inner_products t hrec
  have hba : inner ℝ (translatedCompactB t) (translatedCompactA t) = 0 := by
    rw [real_inner_comm, hab]
  simp only [← real_inner_self_eq_norm_sq, naturalRemoteDark, naturalRemoteBright,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, ha, hb, hab, hba]
  norm_num

@[expose] def naturalRemoteDriven (t : Lattice) (δ η : ℝ) :
    TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  canonicalPlateauHamiltonian + δ • naturalRemoteOnsiteControl t +
    η • naturalRemoteMatchingControl t

theorem naturalRemoteDetuning_eigenpair (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (δ : ℝ) :
    naturalRemoteDriven v.val δ 0 (translatedCompactA v.val) =
      (canonicalPlateauHeight + 3 / 16 + δ) • translatedCompactA v.val ∧
    naturalRemoteDriven v.val δ 0 (translatedCompactB v.val) =
      (canonicalPlateauHeight + 1 / 4) • translatedCompactB v.val := by
  obtain ⟨ha, hb⟩ := naturalPlateauPair_eigenvectors v hr hrec
  constructor <;>
    simp only [naturalRemoteDriven, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ha, hb, naturalRemoteOnsite_compactA v.val hrec,
      naturalRemoteOnsite_compactB v.val hrec, smul_zero, zero_smul, add_zero] <;> module

theorem naturalRemoteCompensated_eigenpair (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (η : ℝ) :
    naturalRemoteDriven v.val (1 / 16) η (naturalRemoteDark v.val) =
      (canonicalPlateauHeight + 1 / 4) • naturalRemoteDark v.val ∧
    naturalRemoteDriven v.val (1 / 16) η (naturalRemoteBright v.val) =
      (canonicalPlateauHeight + 1 / 4 + 2 * η) • naturalRemoteBright v.val := by
  have hD := naturalRemote_compensated_pair_action v hr hrec 0 η (1 / 4) (1 / 4)
  have hF := naturalRemote_compensated_pair_action v hr hrec 0 η (1 / 4) (-1 / 4)
  have hDark : naturalRemoteDark v.val =
      (1 / 4 : ℝ) • translatedCompactA v.val + (1 / 4 : ℝ) • translatedCompactB v.val := by
    unfold naturalRemoteDark
    module
  have hBright : naturalRemoteBright v.val =
      (1 / 4 : ℝ) • translatedCompactA v.val + (-1 / 4 : ℝ) • translatedCompactB v.val := by
    unfold naturalRemoteBright
    module
  unfold naturalRemoteDriven
  rw [hDark, hBright]
  norm_num only [add_zero] at hD hF
  constructor
  · rw [hD]
    module
  · rw [hF]
    module

theorem naturalRemoteFree_Schrodinger (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (a b : ℂ) (τ : ℝ) :
    HasDerivAt (naturalPairReal (translatedCompactA v.val) (translatedCompactB v.val)
      (canonicalPlateauHeight + 3 / 16) (canonicalPlateauHeight + 1 / 4) a b)
      (canonicalPlateauHamiltonian
        (naturalPairImag (translatedCompactA v.val) (translatedCompactB v.val)
          (canonicalPlateauHeight + 3 / 16) (canonicalPlateauHeight + 1 / 4) a b τ)) τ ∧
    HasDerivAt (naturalPairImag (translatedCompactA v.val) (translatedCompactB v.val)
      (canonicalPlateauHeight + 3 / 16) (canonicalPlateauHeight + 1 / 4) a b)
      (-(canonicalPlateauHamiltonian
        (naturalPairReal (translatedCompactA v.val) (translatedCompactB v.val)
          (canonicalPlateauHeight + 3 / 16) (canonicalPlateauHeight + 1 / 4) a b τ))) τ := by
  obtain ⟨ha, hb⟩ := naturalPlateauPair_eigenvectors v hr hrec
  exact naturalPair_Schrodinger _ _ _ _ _ ha hb a b τ

theorem naturalRemoteDetuning_Schrodinger (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (δ : ℝ) (a b : ℂ) (τ : ℝ) :
    HasDerivAt (naturalPairReal (translatedCompactA v.val) (translatedCompactB v.val)
      (canonicalPlateauHeight + 3 / 16 + δ) (canonicalPlateauHeight + 1 / 4) a b)
      (naturalRemoteDriven v.val δ 0
        (naturalPairImag (translatedCompactA v.val) (translatedCompactB v.val)
          (canonicalPlateauHeight + 3 / 16 + δ) (canonicalPlateauHeight + 1 / 4) a b τ)) τ ∧
    HasDerivAt (naturalPairImag (translatedCompactA v.val) (translatedCompactB v.val)
      (canonicalPlateauHeight + 3 / 16 + δ) (canonicalPlateauHeight + 1 / 4) a b)
      (-(naturalRemoteDriven v.val δ 0
        (naturalPairReal (translatedCompactA v.val) (translatedCompactB v.val)
          (canonicalPlateauHeight + 3 / 16 + δ) (canonicalPlateauHeight + 1 / 4) a b τ))) τ := by
  obtain ⟨ha, hb⟩ := naturalRemoteDetuning_eigenpair v hr hrec δ
  exact naturalPair_Schrodinger _ _ _ _ _ ha hb a b τ

theorem naturalRemoteCompensated_Schrodinger (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (η : ℝ) (a b : ℂ) (τ : ℝ) :
    HasDerivAt (naturalPairReal (naturalRemoteDark v.val) (naturalRemoteBright v.val)
      (canonicalPlateauHeight + 1 / 4) (canonicalPlateauHeight + 1 / 4 + 2 * η) a b)
      (naturalRemoteDriven v.val (1 / 16) η
        (naturalPairImag (naturalRemoteDark v.val) (naturalRemoteBright v.val)
          (canonicalPlateauHeight + 1 / 4) (canonicalPlateauHeight + 1 / 4 + 2 * η) a b τ)) τ ∧
    HasDerivAt (naturalPairImag (naturalRemoteDark v.val) (naturalRemoteBright v.val)
      (canonicalPlateauHeight + 1 / 4) (canonicalPlateauHeight + 1 / 4 + 2 * η) a b)
      (-(naturalRemoteDriven v.val (1 / 16) η
        (naturalPairReal (naturalRemoteDark v.val) (naturalRemoteBright v.val)
          (canonicalPlateauHeight + 1 / 4) (canonicalPlateauHeight + 1 / 4 + 2 * η) a b τ))) τ := by
  obtain ⟨ha, hb⟩ := naturalRemoteCompensated_eigenpair v hr hrec η
  exact naturalPair_Schrodinger _ _ _ _ _ ha hb a b τ

theorem naturalRemoteDarkBright_norm_sq (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (E F : ℝ) (a b : ℂ) (τ : ℝ) :
    ‖naturalPairReal (naturalRemoteDark t) (naturalRemoteBright t) E F a b τ‖ ^ 2 +
    ‖naturalPairImag (naturalRemoteDark t) (naturalRemoteBright t) E F a b τ‖ ^ 2 =
    ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  obtain ⟨hd, hf, horth⟩ := naturalRemoteDarkBright_orthonormal t hrec
  rw [naturalPair_norm_sq _ _ horth, hd, hf, mul_one, mul_one]

theorem naturalRemoteAB_norm_sq (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (E F : ℝ) (a b : ℂ) (τ : ℝ) :
    ‖naturalPairReal (translatedCompactA t) (translatedCompactB t) E F a b τ‖ ^ 2 +
    ‖naturalPairImag (translatedCompactA t) (translatedCompactB t) E F a b τ‖ ^ 2 =
    8 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  obtain ⟨ha, hb, hab⟩ := translatedCompact_inner_products t hrec
  rw [naturalPair_norm_sq _ _ hab, ← real_inner_self_eq_norm_sq (translatedCompactA t),
    ← real_inner_self_eq_norm_sq (translatedCompactB t), ha, hb]
  ring

theorem naturalRemote_translated_supported (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (x : TileHilbert Vertex) (w : Vertex) (hw : w ∉ naturalRemoteCell t) :
    translateFiniteState centralPatch t x w = 0 := by
  apply translateFiniteState_apply_zero
  intro u hu he
  exact hw ((naturalRemoteCell_mem_iff t hrec w).mpr ⟨u, hu, he⟩)

theorem naturalRemotePair_support (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (E F : ℝ) (a b : ℂ) (τ : ℝ) (w : Vertex) (hw : w ∉ naturalRemoteCell t) :
    naturalPairReal (translatedCompactA t) (translatedCompactB t) E F a b τ w = 0 ∧
    naturalPairImag (translatedCompactA t) (translatedCompactB t) E F a b τ w = 0 ∧
    naturalPairReal (naturalRemoteDark t) (naturalRemoteBright t) E F a b τ w = 0 ∧
    naturalPairImag (naturalRemoteDark t) (naturalRemoteBright t) E F a b τ w = 0 := by
  have ha : translatedCompactA t w = 0 :=
    naturalRemote_translated_supported t hrec compactA w hw
  have hb : translatedCompactB t w = 0 :=
    naturalRemote_translated_supported t hrec compactB w hw
  simp [naturalPairReal, naturalPairImag, naturalRemoteDark, naturalRemoteBright,
    lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, ha, hb]

/-- The relative phase factor between the two freely evolving natural
modes is the phase at angular frequency 1/16, independent of height. -/
theorem naturalRemote_free_relative_phase (C τ : ℝ) :
    coordinatedEigenCoeff (C + 1 / 4) 1 τ =
      coordinatedPhase (-τ / 16) * coordinatedEigenCoeff (C + 3 / 16) 1 τ := by
  unfold coordinatedEigenCoeff
  rw [mul_one, mul_one, ← coordinatedPhase_add]
  congr 1
  ring

end
end SpectralGeometry.AmmannBeenker
