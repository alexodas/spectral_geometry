module

public import SpectralGeometry.AmmannBeenkerBrightAmplitude
public import SpectralGeometry.AmmannBeenkerNearCrossingEigenvectors
public import SpectralGeometry.InfiniteBoundedSpectralStability
public import SpectralGeometry.OrderedLevelMultiplicityTwo

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


/-- Exact geometric multiplicity two becomes a genuinely consecutive
pair of spectral slots for the original infinite Hamiltonian.
This identifies the two slots but does not yet construct the moving
eigenvalue of the perturbed Hamiltonian. -/
theorem crossing_exists_ordered_eigenbasis_consecutive_pair :
    ∃ (ev : ℕ → ℝ)
      (b : DomainEigenbasis
        (infiniteOnsiteDomain potential)
        (onsitePlusBounded potential
          (ringInteraction crossingParameter)) ev),
      Monotone ev ∧
        ∃ n : ℕ,
          ev n = crossingEnergy ∧
          ev (n + 1) = crossingEnergy ∧
          ∀ k : ℕ, ev k = crossingEnergy →
            k = n ∨ k = n + 1 := by
  obtain ⟨ev, hmono, ⟨b⟩, hcount⟩ :=
    crossing_exists_ordered_eigenbasis_exact_double
  obtain ⟨n, hn, hnext, hunique⟩ :=
    ordered_levelMultiplicity_two_consecutive ev crossingEnergy hmono hcount
  exact ⟨ev, b, hmono, n, hn, hnext, hunique⟩


/-- For every nonzero one-edge perturbation, at least one of the two
perturbed spectral slots arising from the exact crossing is a genuine
*distinct* infinite-operator eigenvalue within the global operator-norm
bound. This statement needs no small-epsilon assumption.

The ordered sequences used in the multiplicity theorem and the
perturbation theorem are identified via their complete eigenbases;
the two perturbed eigenvectors cannot both lie in the one-dimensional
dark eigenspace. Simplicity of the moving eigenvalue and its sharp
asymptotic expansion are separate obligations. -/
theorem crossing_exists_distinct_perturbed_level_near
    (ε : ℝ) (hε : ε ≠ 0) :
    ∃ (energy : ℝ) (x : infiniteOnsiteDomain potential),
      energy ≠ crossingEnergy ∧
      |energy - crossingEnergy| ≤ 2 * |ε| ∧
      (x : TileHilbert Vertex) ≠ 0 ∧
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x =
        energy • (x : TileHilbert Vertex) := by
  obtain ⟨ev, b, hev, n, hn, hnext, _⟩ :=
    crossing_exists_ordered_eigenbasis_consecutive_pair
  obtain ⟨baseline, μ, b0, bt, hbaseline, _, hstab⟩ :=
    crossingEdge_exists_ordered_eigenbases_and_stability ε
  have hring :
      ∀ x y : TileHilbert Vertex,
        inner ℝ ((ringInteraction crossingParameter) x) y =
          inner ℝ x ((ringInteraction crossingParameter) y) := by
    simpa only [ringInteraction] using
      (finiteSectorCorrection_symmetric interaction interaction_symmetric
        (neighbors origin) crossingParameter)
  have heq : ev = baseline :=
    DomainEigenbasis.ordered_levels_unique b b0
      (onsitePlusBounded_symmetric potential
        (ringInteraction crossingParameter) hring)
      hev hbaseline
  have hbase_n : baseline n = crossingEnergy := by
    rw [← heq]
    exact hn
  have hbase_next : baseline (n + 1) = crossingEnergy := by
    rw [← heq]
    exact hnext
  have hnotboth :
      μ n ≠ crossingEnergy ∨ μ (n + 1) ≠ crossingEnergy := by
    by_contra h
    push_neg at h
    obtain ⟨c, hc⟩ :=
      crossingPerturbedEnergy_dark_only ε hε
        ⟨bt.basis n, bt.mem_domain n⟩
        (by simpa only [h.1] using bt.eigen n)
    obtain ⟨d, hd⟩ :=
      crossingPerturbedEnergy_dark_only ε hε
        ⟨bt.basis (n + 1), bt.mem_domain (n + 1)⟩
        (by simpa only [h.2] using bt.eigen (n + 1))
    change bt.basis n = c • crossingDark at hc
    change bt.basis (n + 1) = d • crossingDark at hd
    have hnorm_n : ‖bt.basis n‖ = 1 :=
      bt.basis.orthonormal.norm_eq_one n
    have hnorm_next : ‖bt.basis (n + 1)‖ = 1 :=
      bt.basis.orthonormal.norm_eq_one (n + 1)
    rw [hc, norm_smul, Real.norm_eq_abs, crossingDark_norm_one,
      mul_one] at hnorm_n
    rw [hd, norm_smul, Real.norm_eq_abs, crossingDark_norm_one,
      mul_one] at hnorm_next
    have hc0 : c ≠ 0 := by
      intro hz
      rw [hz, abs_zero] at hnorm_n
      norm_num at hnorm_n
    have hd0 : d ≠ 0 := by
      intro hz
      rw [hz, abs_zero] at hnorm_next
      norm_num at hnorm_next
    have hD : inner ℝ crossingDark crossingDark = 1 := by
      rw [real_inner_self_eq_norm_sq, crossingDark_norm_one]
      norm_num
    have horth :
        inner ℝ (bt.basis n) (bt.basis (n + 1)) = 0 :=
      bt.basis.orthonormal.inner_eq_zero (by omega)
    rw [hc, hd, real_inner_smul_left, real_inner_smul_right, hD] at horth
    have hcd : c * d = 0 := by nlinarith only [horth]
    exact (mul_ne_zero hc0 hd0) hcd
  rcases hnotboth with hmove | hmove
  · refine ⟨μ n, ⟨bt.basis n, bt.mem_domain n⟩, hmove, ?_, ?_, ?_⟩
    · simpa only [hbase_n] using hstab n
    · exact bt.basis.orthonormal.ne_zero n
    · exact bt.eigen n
  · refine ⟨μ (n + 1), ⟨bt.basis (n + 1), bt.mem_domain (n + 1)⟩,
      hmove, ?_, ?_, ?_⟩
    · simpa only [hbase_next] using hstab (n + 1)
    · exact bt.basis.orthonormal.ne_zero (n + 1)
    · exact bt.eigen (n + 1)

end
end SpectralGeometry.AmmannBeenker
