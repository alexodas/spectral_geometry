module

public import SpectralGeometry.AmmannBeenkerBrightAmplitude
public import SpectralGeometry.InfiniteBoundedSpectralStability

public section

/-!
# First spectral-splitting ingredients for the infinite crossing

A nonzero edge change leaves exactly the dark direction at the
original crossing energy. Here we begin proving existence of the
distinct moving bright eigenvalue in the actual infinite graph.

The existing ordered-eigenbasis and bounded-perturbation theorems
provide complete monotone spectra of both Hamiltonians and a uniform
2|epsilon| bound for corresponding ordered levels. Identifying
the two slots of the original crossing is still a separate obligation.

An additional theorem names the exact size of the bright edge force
outside the original two-mode plane. No moving eigenvalue or
quadratic error bound is claimed by these ingredients alone.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- Both the original and single-edge-perturbed infinite Hamiltonians
have complete, nondecreasing natural-domain eigenbases, and every
corresponding ordered eigenvalue changes by at most 2|epsilon|. -/
theorem crossingEdge_exists_ordered_eigenbases_and_stability (ε : ℝ) :
    ∃ (ev μ : ℕ → ℝ)
      (b : DomainEigenbasis
        (infiniteOnsiteDomain potential)
        (onsitePlusBounded potential
          (ringInteraction crossingParameter)) ev)
      (bt : DomainEigenbasis
        (infiniteOnsiteDomain potential)
        (onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge)) μ),
      Monotone ev ∧ Monotone μ ∧
        ∀ n : ℕ, |μ n - ev n| ≤ 2 * |ε| := by
  have hring :
      ∀ x y : TileHilbert Vertex,
        inner ℝ ((ringInteraction crossingParameter) x) y =
          inner ℝ x ((ringInteraction crossingParameter) y) := by
    simpa only [ringInteraction] using
      (finiteSectorCorrection_symmetric interaction interaction_symmetric
        (neighbors origin) crossingParameter)
  have hedge :
      ∀ x y : TileHilbert Vertex,
        inner ℝ ((ε • crossingEdge) x) y =
          inner ℝ x ((ε • crossingEdge) y) := by
    intro x y
    simp only [smul_apply,
      real_inner_smul_left, real_inner_smul_right]
    rw [crossingEdge_symmetric_full x y]
  obtain ⟨ev, hev, ⟨b⟩⟩ :=
    onsitePlusBounded_exists_orderedEigenbasis
      potential 1 potential_lower potential_proper
      (ringInteraction crossingParameter) hring
  obtain ⟨μ, hμ, ⟨bt⟩⟩ :=
    onsitePlusBounded_exists_orderedEigenbasis
      potential 1 potential_lower potential_proper
      (ringInteraction crossingParameter + ε • crossingEdge)
      (crossingEdgePulseCorrection_symmetric ε)
  refine ⟨ev, μ, b, bt, hev, hμ, ?_⟩
  intro n
  have hbound :=
    onsitePlusBounded_ordered_perturbation_bound
      potential (ringInteraction crossingParameter) (ε • crossingEdge)
      hring hedge ev μ hev hμ b bt n
  calc
    |μ n - ev n| ≤ ‖ε • crossingEdge‖ := hbound
    _ = 2 * |ε| := by
      rw [norm_smul, crossingEdge_opNorm]
      simp only [Real.norm_eq_abs]
      ring

/-- Exact squared external edge force of the normalized bright state:
7/16 on the full infinite graph, not a finite-patch approximation. -/
theorem crossingBright_external_edge_norm_sq :
    ‖crossingLeakage (crossingEdge crossingBright)‖ ^ 2 = 7 / 16 := by
  have hb :
      crossingBright =
        (1 / 4 : ℝ) • compactA + (-(1 / 4 : ℝ)) • compactB := by
    rw [crossingBright, smul_sub, neg_smul]
  rw [hb, crossingEdge_two_mode_leakage_norm_sq]
  norm_num

end
end SpectralGeometry.AmmannBeenker
