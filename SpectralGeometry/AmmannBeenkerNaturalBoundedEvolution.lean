module

public import SpectralGeometry.AmmannBeenkerNaturalLeakage
public import Mathlib.Analysis.SpecialFunctions.Exponential

public section

/-!
# Full bounded evolution and unconditional finite-time storage bounds

The real/imaginary equations form a single bounded linear ODE on a
product of two complete real Hilbert spaces. Its solution is the
Banach-algebra exponential of the block generator. This constructs
the perturbed solution on the full infinite space, including for
errors that do not preserve a compact plane. The norm used to
construct the exponential is the product Banach norm; physical
weight is the sum of the two squared Hilbert norms.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

@[expose] def naturalEvolutionGenerator (H : TileHilbert Vertex →L[ℝ] TileHilbert Vertex) :
    (TileHilbert Vertex × TileHilbert Vertex) →L[ℝ]
      (TileHilbert Vertex × TileHilbert Vertex) :=
  (H.comp (ContinuousLinearMap.snd ℝ (TileHilbert Vertex) (TileHilbert Vertex))).prod
    ((-H).comp (ContinuousLinearMap.fst ℝ (TileHilbert Vertex) (TileHilbert Vertex)))

theorem naturalEvolutionGenerator_apply (H : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (x : TileHilbert Vertex × TileHilbert Vertex) :
    naturalEvolutionGenerator H x = (H x.2, -(H x.1)) := by
  rfl

@[expose] def naturalBoundedEvolution (H : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (x : TileHilbert Vertex × TileHilbert Vertex) (τ : ℝ) :
    TileHilbert Vertex × TileHilbert Vertex :=
  NormedSpace.exp (τ • naturalEvolutionGenerator H) x

theorem naturalBoundedEvolution_initial (H : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (x : TileHilbert Vertex × TileHilbert Vertex) :
    naturalBoundedEvolution H x 0 = x := by
  unfold naturalBoundedEvolution
  rw [zero_smul, NormedSpace.exp_zero]
  rfl

theorem naturalBoundedEvolution_deriv (H : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (x : TileHilbert Vertex × TileHilbert Vertex) (τ : ℝ) :
    HasDerivAt (naturalBoundedEvolution H x)
      (naturalEvolutionGenerator H (naturalBoundedEvolution H x τ)) τ := by
  let G := naturalEvolutionGenerator H
  have he := hasDerivAt_exp_smul_const' G τ
  let L := ContinuousLinearMap.apply ℝ (TileHilbert Vertex × TileHilbert Vertex) x
  have hd := L.hasFDerivAt.comp_hasDerivAt τ he
  change HasDerivAt (fun s => NormedSpace.exp (s • G) x)
    ((G * NormedSpace.exp (τ • G)) x) τ at hd
  exact hd

theorem naturalBoundedEvolution_solvesAt (H : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (x : TileHilbert Vertex × TileHilbert Vertex) (τ : ℝ) :
    naturalFullSolvesAt H (fun s => (naturalBoundedEvolution H x s).1)
      (fun s => (naturalBoundedEvolution H x s).2) τ := by
  have hd := naturalBoundedEvolution_deriv H x τ
  rw [naturalEvolutionGenerator_apply] at hd
  unfold naturalFullSolvesAt
  constructor
  · exact (ContinuousLinearMap.fst ℝ (TileHilbert Vertex) (TileHilbert Vertex)).hasFDerivAt.comp_hasDerivAt τ hd
  · exact (ContinuousLinearMap.snd ℝ (TileHilbert Vertex) (TileHilbert Vertex)).hasFDerivAt.comp_hasDerivAt τ hd

theorem naturalBoundedEvolution_weight (H : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hs : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y))
    (x : TileHilbert Vertex × TileHilbert Vertex) (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖(naturalBoundedEvolution H x τ).1‖ ^ 2 + ‖(naturalBoundedEvolution H x τ).2‖ ^ 2 =
      ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 := by
  have h := naturalTrajectoryWeight_constant H hs
    (fun s => (naturalBoundedEvolution H x s).1)
    (fun s => (naturalBoundedEvolution H x s).2)
    (naturalBoundedEvolution_solvesAt H x) τ hτ
  simpa only [naturalTrajectoryWeight, naturalBoundedEvolution_initial] using h

/-- Actual full-space evolution exists for every bounded Hamiltonian
and all real times, without an assumed solution. -/
theorem naturalFullSolves_exists (H : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (x y : TileHilbert Vertex) :
    ∃ r i : ℝ → TileHilbert Vertex, r 0 = x ∧ i 0 = y ∧
      ∀ τ, naturalFullSolvesAt H r i τ := by
  refine ⟨fun s => (naturalBoundedEvolution H (x,y) s).1,
    fun s => (naturalBoundedEvolution H (x,y) s).2, ?_, ?_,
    naturalBoundedEvolution_solvesAt H (x,y)⟩
  · change (naturalBoundedEvolution H (x, y) 0).1 = x
    rw [naturalBoundedEvolution_initial]
  · change (naturalBoundedEvolution H (x, y) 0).2 = y
    rw [naturalBoundedEvolution_initial]

/-- Quadratic leakage and retained-weight estimates for the
constructed evolution of a normalized remote state. -/
theorem naturalBoundedStorage_leakage_and_retention (v : Vertex) (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (w : ℂ × ℂ) (hw : ‖w.1‖ ^ 2 + ‖w.2‖ ^ 2 = 1)
    (P : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hp : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (τ : ℝ) (hτ : 0 ≤ τ) :
    let z := naturalBoundedEvolution (canonicalPlateauHamiltonian + P)
      (naturalStateReal v.val w, naturalStateImag v.val w) τ
    naturalRemoteLeakageWeight v.val z.1 z.2 ≤ ‖P‖ ^ 2 * τ ^ 2 ∧
      1 - ‖P‖ ^ 2 * τ ^ 2 ≤
        ‖naturalRemotePart v.val z.1‖ ^ 2 + ‖naturalRemotePart v.val z.2‖ ^ 2 := by
  let H := canonicalPlateauHamiltonian + P
  let x := (naturalStateReal v.val w, naturalStateImag v.val w)
  let u := fun s => (naturalBoundedEvolution H x s).1
  let j := fun s => (naturalBoundedEvolution H x s).2
  have hk : ∀ s, naturalFullSolvesAt H u j s :=
    naturalBoundedEvolution_solvesAt H x
  have hR : u 0 = naturalStateReal v.val w := by
    change (naturalBoundedEvolution H x 0).1 = _
    rw [naturalBoundedEvolution_initial]
  have hI : j 0 = naturalStateImag v.val w := by
    change (naturalBoundedEvolution H x 0).2 = _
    rw [naturalBoundedEvolution_initial]
  exact ⟨naturalStorage_leakage_quadratic_le v hr hrec w hw P hp u j hk hR hI τ hτ,
    naturalStorage_retained_weight_ge v hr hrec w hw P hp u j hk hR hI τ hτ⟩

end
end SpectralGeometry.AmmannBeenker
