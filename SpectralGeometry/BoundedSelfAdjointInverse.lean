module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

public section

/-!
# Bounded inverse from a uniform lower norm bound

A self-adjoint bounded operator with a positive lower norm bound has
closed range and trivial kernel. Its range is dense by self-adjointness,
so it is bijective and its inverse is bounded. No compactness is needed.
-/

namespace SpectralGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem boundedSelfAdjoint_isUnit_of_norm_lower
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (k : ℝ) (hk : 0 ≤ k) (hbound : ∀ x : E, ‖x‖ ≤ k * ‖T x‖) :
    IsUnit T := by
  let K : ℝ≥0 := ⟨k, hk⟩
  have ha : AntilipschitzWith K T := by
    apply antilipschitzWith_iff_le_mul_dist.mpr
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact hbound (x - y)
  have hker : T.ker = ⊥ := LinearMap.ker_eq_bot.mpr ha.injective
  have horth : T.rangeᗮ = ⊥ := by
    rw [T.orthogonal_range, hT.adjoint_eq, hker]
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  apply (T.bijective_iff_dense_range_and_antilipschitz).mpr
  refine ⟨?_, ⟨K, ha⟩⟩
  rw [← T.range.orthogonal_orthogonal_eq_closure, horth,
    Submodule.bot_orthogonal_eq_top]

end SpectralGeometry
