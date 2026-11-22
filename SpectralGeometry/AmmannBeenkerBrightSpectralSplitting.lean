module

public import SpectralGeometry.AmmannBeenkerBrightAmplitude
public import SpectralGeometry.InfiniteBoundedSpectralStability
public import SpectralGeometry.InfiniteFullSpectralProduct

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
    simp only [sub_eq_add_neg]
  rw [hb, crossingEdge_two_mode_leakage_norm_sq]
  norm_num


/-- A multiplicity-faithful ordered eigenbasis for the *unperturbed*
infinite crossing: the crossing energy occurs exactly twice, not just
at least twice, among the natural-number spectral slots.

The proof uses the existing multiplicity-tag enumeration and the
verified full-domain equivalence between resolvent and original
eigenspaces. This is the index bridge required by the moving-level
existence argument. -/
theorem crossing_exists_ordered_eigenbasis_exact_double :
    ∃ (ev : ℕ → ℝ),
      Monotone ev ∧
      Nonempty (DomainEigenbasis
        (infiniteOnsiteDomain potential)
        (onsitePlusBounded potential
          (ringInteraction crossingParameter)) ev) ∧
      levelMultiplicity ev crossingEnergy = 2 := by
  classical
  let B := ringInteraction crossingParameter
  let σ : Fin 0 → Vertex ≃ Vertex := fun i => Fin.elim0 i
  let w : Fin 0 → ℝ := fun i => Fin.elim0 i
  have hc :
      infiniteLocalBoundedCorrection 0 σ w B 1 0 = B :=
    zeroMatching_correction B
  have hsymB :
      ∀ x y : TileHilbert Vertex,
        inner ℝ (B x) y = inner ℝ x (B y) := by
    simpa only [B, ringInteraction] using
      (finiteSectorCorrection_symmetric interaction interaction_symmetric
        (neighbors origin) crossingParameter)
  obtain ⟨a, hgap, hsmall, _⟩ :=
    infiniteBoundedOnsite_exists_compact_shift
      potential 1 potential_lower potential_proper B
  have hs :
      ‖(infiniteLocalBoundedCorrection 0 σ w B 1 0).comp
        (infiniteOnsiteResolventCLM potential a hgap)‖ < 1 := by
    simpa only [hc] using hsmall
  have hσ : ∀ i t, σ i (σ i t) = t := fun i => Fin.elim0 i
  have hP :
      ∀ x y : TileHilbert Vertex,
        inner ℝ x (B y) = inner ℝ (B x) y :=
    fun x y => (hsymB x y).symm
  have hinfinite :=
    infiniteLocalMatching_full_tags_infinite
      0 potential σ w B 1 0 a hgap potential_proper hs hσ hP
  have hlo (ev : ℝ)
      (he : infiniteLocalMatchingHasFullEigenvalue
        0 potential σ w B 1 0 ev) :
      (1 : ℝ) - ‖infiniteLocalBoundedCorrection 0 σ w B 1 0‖ ≤ ev := by
    obtain ⟨x, hx, heigen⟩ := he
    exact infiniteLocalShiftedPerturbed_eigenvalue_ge_onsite_lower_sub_norm
      0 potential σ w B 1 0 1 potential_lower x ev heigen hx
  obtain ⟨seq, hseq, hrange⟩ :=
    infiniteLocalMatching_full_infinite_tags_exists_strictMono_enumeration
      0 potential σ w B 1 0 a hgap potential_proper hs hσ hP
      (1 - ‖infiniteLocalBoundedCorrection 0 σ w B 1 0‖)
      hlo hinfinite
  obtain ⟨b⟩ :=
    infiniteLocalMatching_full_exists_domainEigenbasis
      0 potential σ w B 1 0 a hgap potential_proper hs hσ hP
      seq hseq hrange
  have hne : crossingEnergy ≠ a := by
    intro heq
    have heigen :
        infiniteLocalShiftedPerturbedOperator
          0 potential σ w B 1 0 domainCompactA =
            a • compactA := by
      rw [← onsitePlusBounded_eq_local, hc]
      rw [← heq]
      exact compact_crossing.2.1
    have hz :=
      infiniteLocalMatching_no_eigenvector_at_shift
        0 potential σ w B 1 0 a hgap hs domainCompactA heigen
    exact compactA_ne_zero hz
  have hm :
      Module.finrank ℝ
        (domainEigenspace (infiniteOnsiteDomain potential)
          (onsitePlusBounded potential
            (infiniteLocalBoundedCorrection 0 σ w B 1 0))
          crossingEnergy) =
      infiniteLocalMatchingFullMultiplicity
        0 potential σ w B 1 0 a hgap potential_proper hs crossingEnergy :=
    domainEigenspace_finrank_eq_fullMultiplicity
      0 potential σ w B 1 0 a hgap potential_proper hs crossingEnergy hne
  have hcount :
      levelMultiplicity (fun n => (ofLex (seq n)).1) crossingEnergy = 2 := by
    calc
      levelMultiplicity (fun n => (ofLex (seq n)).1) crossingEnergy =
          infiniteLocalMatchingFullMultiplicity
            0 potential σ w B 1 0 a hgap potential_proper hs crossingEnergy :=
        infiniteLocalMatching_full_sequence_levelMultiplicity
          0 potential σ w B 1 0 a hgap potential_proper hs
          seq hseq hrange crossingEnergy
      _ = Module.finrank ℝ
            (domainEigenspace (infiniteOnsiteDomain potential)
              (onsitePlusBounded potential
                (infiniteLocalBoundedCorrection 0 σ w B 1 0))
              crossingEnergy) := hm.symm
      _ = Module.finrank ℝ crossingEigenspace := by
        rw [hc]
        rfl
      _ = 2 := crossingEigenspace_finrank
  refine ⟨(fun n => (ofLex (seq n)).1), ?_, ?_, hcount⟩
  · intro i j hij
    exact Prod.Lex.monotone_fst _ _ (hseq.monotone hij)
  · simpa only [hc] using (show Nonempty
        (DomainEigenbasis (infiniteOnsiteDomain potential)
          (onsitePlusBounded potential
            (infiniteLocalBoundedCorrection 0 σ w B 1 0))
          (fun n => (ofLex (seq n)).1)) from ⟨b⟩)

end
end SpectralGeometry.AmmannBeenker
