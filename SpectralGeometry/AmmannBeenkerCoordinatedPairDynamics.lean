module

public import SpectralGeometry.AmmannBeenkerCoordinatedEuler
public import SpectralGeometry.AmmannBeenkerDarkSchrodinger
public import SpectralGeometry.AmmannBeenkerBrightAmplitude

public section

/-!
# Exact complex coefficient trajectories on the natural domain (L7c)

Represent a complex full-space state by its real and imaginary Hilbert
vectors, as in the earlier dark-phase theorem. For a pair of exact
real natural-domain eigenvectors, construct both components for arbitrary
complex initial coefficients, differentiate them and prove the coupled
Schroedinger equations and exact norm conservation. This does not assume
a full-space complex unitary propagator.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- Complex coefficient of an eigenmode of energy E. -/
@[expose] def coordinatedEigenCoeff (E : ℝ) (z : ℂ) (τ : ℝ) : ℂ :=
  coordinatedPhase (-E * τ) * z

theorem coordinatedEigenCoeff_initial (E : ℝ) (z : ℂ) :
    coordinatedEigenCoeff E z 0 = z := by
  simp [coordinatedEigenCoeff, coordinatedPhase]

theorem coordinatedEigenCoeff_norm (E : ℝ) (z : ℂ) (τ : ℝ) :
    ‖coordinatedEigenCoeff E z τ‖ = ‖z‖ := by
  rw [coordinatedEigenCoeff, norm_mul, coordinatedPhase_norm, one_mul]

theorem coordinatedEigenCoeff_re (E : ℝ) (z : ℂ) (τ : ℝ) :
    (coordinatedEigenCoeff E z τ).re =
      Real.cos (E * τ) * z.re + Real.sin (E * τ) * z.im := by
  simp [coordinatedEigenCoeff, coordinatedPhase, Complex.mul_re, Complex.mul_im,
    Complex.exp_re, Complex.exp_im, neg_mul, Real.cos_neg, Real.sin_neg] <;> ring

theorem coordinatedEigenCoeff_im (E : ℝ) (z : ℂ) (τ : ℝ) :
    (coordinatedEigenCoeff E z τ).im =
      Real.cos (E * τ) * z.im - Real.sin (E * τ) * z.re := by
  simp [coordinatedEigenCoeff, coordinatedPhase, Complex.mul_re, Complex.mul_im,
    Complex.exp_re, Complex.exp_im, neg_mul, Real.cos_neg, Real.sin_neg] <;> ring

theorem coordinatedEigenCoeff_re_deriv (E : ℝ) (z : ℂ) (τ : ℝ) :
    HasDerivAt (fun s : ℝ => (coordinatedEigenCoeff E z s).re)
      (E * (coordinatedEigenCoeff E z τ).im) τ := by
  have hlin : HasDerivAt (fun s : ℝ => E * s) E τ := hasDerivAt_const_mul E
  have hc : HasDerivAt (fun s : ℝ => Real.cos (E * s))
      (-Real.sin (E * τ) * E) τ := by
    simpa only [Function.comp_def] using (Real.hasDerivAt_cos (E * τ)).comp τ hlin
  have hs : HasDerivAt (fun s : ℝ => Real.sin (E * s))
      (Real.cos (E * τ) * E) τ := by
    simpa only [Function.comp_def] using (Real.hasDerivAt_sin (E * τ)).comp τ hlin
  simp only [coordinatedEigenCoeff_re, coordinatedEigenCoeff_im]
  convert (hc.mul_const z.re).add (hs.mul_const z.im) using 1 <;> ring

theorem coordinatedEigenCoeff_im_deriv (E : ℝ) (z : ℂ) (τ : ℝ) :
    HasDerivAt (fun s : ℝ => (coordinatedEigenCoeff E z s).im)
      (-(E * (coordinatedEigenCoeff E z τ).re)) τ := by
  have hlin : HasDerivAt (fun s : ℝ => E * s) E τ := hasDerivAt_const_mul E
  have hc : HasDerivAt (fun s : ℝ => Real.cos (E * s))
      (-Real.sin (E * τ) * E) τ := by
    simpa only [Function.comp_def] using (Real.hasDerivAt_cos (E * τ)).comp τ hlin
  have hs : HasDerivAt (fun s : ℝ => Real.sin (E * s))
      (Real.cos (E * τ) * E) τ := by
    simpa only [Function.comp_def] using (Real.hasDerivAt_sin (E * τ)).comp τ hlin
  simp only [coordinatedEigenCoeff_re, coordinatedEigenCoeff_im]
  convert (hc.mul_const z.im).sub (hs.mul_const z.re) using 1 <;> ring

/-- Full infinite-space real component of a superposition of two eigenmodes. -/
@[expose] def coordinatedPairReal (x y : infiniteOnsiteDomain potential)
    (E F : ℝ) (a b : ℂ) (τ : ℝ) : TileHilbert Vertex :=
  (coordinatedEigenCoeff E a τ).re • (x : TileHilbert Vertex) +
    (coordinatedEigenCoeff F b τ).re • (y : TileHilbert Vertex)

@[expose] def coordinatedPairImag (x y : infiniteOnsiteDomain potential)
    (E F : ℝ) (a b : ℂ) (τ : ℝ) : TileHilbert Vertex :=
  (coordinatedEigenCoeff E a τ).im • (x : TileHilbert Vertex) +
    (coordinatedEigenCoeff F b τ).im • (y : TileHilbert Vertex)

@[expose] def domainCoordinatedPairReal (x y : infiniteOnsiteDomain potential)
    (E F : ℝ) (a b : ℂ) (τ : ℝ) : infiniteOnsiteDomain potential :=
  (coordinatedEigenCoeff E a τ).re • x + (coordinatedEigenCoeff F b τ).re • y

@[expose] def domainCoordinatedPairImag (x y : infiniteOnsiteDomain potential)
    (E F : ℝ) (a b : ℂ) (τ : ℝ) : infiniteOnsiteDomain potential :=
  (coordinatedEigenCoeff E a τ).im • x + (coordinatedEigenCoeff F b τ).im • y

theorem coordinatedPair_domain_coe (x y : infiniteOnsiteDomain potential)
    (E F : ℝ) (a b : ℂ) (τ : ℝ) :
    (domainCoordinatedPairReal x y E F a b τ : TileHilbert Vertex) =
      coordinatedPairReal x y E F a b τ ∧
    (domainCoordinatedPairImag x y E F a b τ : TileHilbert Vertex) =
      coordinatedPairImag x y E F a b τ := ⟨rfl, rfl⟩

theorem coordinatedPair_initial (x y : infiniteOnsiteDomain potential)
    (E F : ℝ) (a b : ℂ) :
    coordinatedPairReal x y E F a b 0 =
      a.re • (x : TileHilbert Vertex) + b.re • (y : TileHilbert Vertex) ∧
    coordinatedPairImag x y E F a b 0 =
      a.im • (x : TileHilbert Vertex) + b.im • (y : TileHilbert Vertex) := by
  simp [coordinatedPairReal, coordinatedPairImag, coordinatedEigenCoeff_initial]

/-- The actual full natural-domain Hamiltonian, not its compression,
appears in both real and imaginary equations. -/
theorem coordinatedPair_Schrodinger
    (B : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (x y : infiniteOnsiteDomain potential) (E F : ℝ)
    (hx : onsitePlusBounded potential B x = E • (x : TileHilbert Vertex))
    (hy : onsitePlusBounded potential B y = F • (y : TileHilbert Vertex))
    (a b : ℂ) (τ : ℝ) :
    HasDerivAt (coordinatedPairReal x y E F a b)
      (onsitePlusBounded potential B (domainCoordinatedPairImag x y E F a b τ)) τ ∧
    HasDerivAt (coordinatedPairImag x y E F a b)
      (-(onsitePlusBounded potential B (domainCoordinatedPairReal x y E F a b τ))) τ := by
  constructor
  · have hd := ((coordinatedEigenCoeff_re_deriv E a τ).smul_const
        (x : TileHilbert Vertex)).add
        ((coordinatedEigenCoeff_re_deriv F b τ).smul_const (y : TileHilbert Vertex))
    convert hd using 1
    simp only [domainCoordinatedPairImag, map_add, map_smul, hx, hy]
    module
  · have hd := ((coordinatedEigenCoeff_im_deriv E a τ).smul_const
        (x : TileHilbert Vertex)).add
        ((coordinatedEigenCoeff_im_deriv F b τ).smul_const (y : TileHilbert Vertex))
    convert hd using 1
    simp only [domainCoordinatedPairReal, map_add, map_smul, hx, hy]
    module

private theorem coordinatedPair_real_norm_sq (x y : TileHilbert Vertex)
    (hxy : inner ℝ x y = 0) (u v : ℝ) :
    ‖u • x + v • y‖ ^ 2 =
      u ^ 2 * ‖x‖ ^ 2 + v ^ 2 * ‖y‖ ^ 2 := by
  have hyx : inner ℝ y x = 0 := by rw [real_inner_comm, hxy]
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hxy, hyx]
  ring

private theorem coordinatedComplex_norm_sq (z : ℂ) :
    z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Exact conserved squared complex norm for any orthogonal eigenpair,
including non-normalized eigenvectors. -/
theorem coordinatedPair_norm_sq (x y : infiniteOnsiteDomain potential)
    (hxy : inner ℝ (x : TileHilbert Vertex) (y : TileHilbert Vertex) = 0)
    (E F : ℝ) (a b : ℂ) (τ : ℝ) :
    ‖coordinatedPairReal x y E F a b τ‖ ^ 2 +
      ‖coordinatedPairImag x y E F a b τ‖ ^ 2 =
      ‖a‖ ^ 2 * ‖(x : TileHilbert Vertex)‖ ^ 2 +
        ‖b‖ ^ 2 * ‖(y : TileHilbert Vertex)‖ ^ 2 := by
  unfold coordinatedPairReal coordinatedPairImag
  rw [coordinatedPair_real_norm_sq _ _ hxy, coordinatedPair_real_norm_sq _ _ hxy]
  calc
    _ = ((coordinatedEigenCoeff E a τ).re ^ 2 +
          (coordinatedEigenCoeff E a τ).im ^ 2) * ‖(x : TileHilbert Vertex)‖ ^ 2 +
        ((coordinatedEigenCoeff F b τ).re ^ 2 +
          (coordinatedEigenCoeff F b τ).im ^ 2) * ‖(y : TileHilbert Vertex)‖ ^ 2 := by ring
    _ = _ := by rw [coordinatedComplex_norm_sq, coordinatedComplex_norm_sq,
        coordinatedEigenCoeff_norm, coordinatedEigenCoeff_norm]

/-- Both complex components have zero exterior part at every real time,
if the two eigenmodes lie in the original compact plane. -/
theorem coordinatedPair_leakage_zero (x y : infiniteOnsiteDomain potential)
    (hx : crossingLeakage (x : TileHilbert Vertex) = 0)
    (hy : crossingLeakage (y : TileHilbert Vertex) = 0)
    (E F : ℝ) (a b : ℂ) (τ : ℝ) :
    crossingLeakage (coordinatedPairReal x y E F a b τ) = 0 ∧
    crossingLeakage (coordinatedPairImag x y E F a b τ) = 0 := by
  simp [coordinatedPairReal, coordinatedPairImag, crossingLeakage_add,
    crossingLeakage_smul, hx, hy]

end
end SpectralGeometry.AmmannBeenker
