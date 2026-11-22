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

/-- For a nonzero selected-edge perturbation with |ε| ≤ 1/1024,
the genuine infinite-operator point spectrum in the closed radius
1/256 about E* consists of exactly two distinct, simple energies:
the fixed dark energy E* and one moving energy. The moving eigenvalue
lies within 2|ε|, and every natural-domain eigenvector at that
energy is a scalar multiple of a fixed normalized eigenvector.

This uses the full ordered eigenbases, not a two-state truncation.
The quantitative bright shift and exterior component are still open. -/
theorem crossing_perturbed_isolated_pair_simple
    (ε : ℝ) (hε : ε ≠ 0) (hsmall : |ε| ≤ 1 / 1024) :
    ∃ (energy : ℝ) (x : infiniteOnsiteDomain potential),
      energy ≠ crossingEnergy ∧
      |energy - crossingEnergy| ≤ 2 * |ε| ∧
      (x : TileHilbert Vertex) ≠ 0 ∧
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x =
        energy • (x : TileHilbert Vertex) ∧
      (∀ (t : ℝ) (y : infiniteOnsiteDomain potential),
        (y : TileHilbert Vertex) ≠ 0 →
        onsitePlusBounded potential
            (ringInteraction crossingParameter + ε • crossingEdge) y =
          t • (y : TileHilbert Vertex) →
        |t - crossingEnergy| ≤ 1 / 256 →
        t = crossingEnergy ∨ t = energy) ∧
      (∀ y : infiniteOnsiteDomain potential,
        onsitePlusBounded potential
            (ringInteraction crossingParameter + ε • crossingEdge) y =
          energy • (y : TileHilbert Vertex) →
        ∃ c : ℝ, (y : TileHilbert Vertex) = c • (x : TileHilbert Vertex)) := by
  obtain ⟨ev, b, hev, n, hn, hnext, hunique⟩ :=
    crossing_exists_ordered_eigenbasis_consecutive_pair
  obtain ⟨baseline, μ, b0, bt, hbaseline, _, hstab⟩ :=
    crossingEdge_exists_ordered_eigenbases_and_stability ε
  have hring :
      ∀ u v : TileHilbert Vertex,
        inner ℝ ((ringInteraction crossingParameter) u) v =
          inner ℝ u ((ringInteraction crossingParameter) v) := by
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
  have hsmallgap :
      (1 / 256 : ℝ) + 2 * |ε| < crossingGapCandidate := by
    dsimp only [crossingGapCandidate]
    linarith only [hsmall]
  have hfar (k : ℕ) (hk : ev k ≠ crossingEnergy) :
      crossingGapCandidate < |ev k - crossingEnergy| := by
    by_contra hnot
    have hnear : |ev k - crossingEnergy| ≤ crossingGapCandidate :=
      le_of_not_gt hnot
    have hz := crossingGapCandidate_off_crossing_eigenvector_zero
      ⟨b.basis k, b.mem_domain k⟩ (ev k) (b.eigen k) hk hnear
    exact (b.basis.orthonormal.ne_zero k) hz
  have houtside (k : ℕ) (hkn : k ≠ n) (hknext : k ≠ n + 1) :
      (1 / 256 : ℝ) < |μ k - crossingEnergy| := by
    have hne : ev k ≠ crossingEnergy := by
      intro h
      rcases hunique k h with hidx | hidx
      · exact hkn hidx
      · exact hknext hidx
    have hg := hfar k hne
    have hs : |μ k - ev k| ≤ 2 * |ε| := by
      simpa only [← heq] using hstab k
    have hs' : |ev k - μ k| ≤ 2 * |ε| := by
      calc
        |ev k - μ k| = |μ k - ev k| := abs_sub_comm _ _
        _ ≤ 2 * |ε| := hs
    have htri : |ev k - crossingEnergy| ≤
        |ev k - μ k| + |μ k - crossingEnergy| :=
      abs_sub_le (ev k) (μ k) crossingEnergy
    by_contra hnot
    have hnear : |μ k - crossingEnergy| ≤ (1 / 256 : ℝ) :=
      le_of_not_gt hnot
    linarith only [hg, hs', htri, hnear, hsmallgap]
  have hslot (k : ℕ)
      (hk : |μ k - crossingEnergy| ≤ (1 / 256 : ℝ)) :
      k = n ∨ k = n + 1 := by
    by_contra hnot
    have hkn : k ≠ n := by
      intro h
      exact hnot (Or.inl h)
    have hknext : k ≠ n + 1 := by
      intro h
      exact hnot (Or.inr h)
    exact (not_lt_of_ge hk) (houtside k hkn hknext)
  have hsym :
      ∀ u v : infiniteOnsiteDomain potential,
        inner ℝ
          (onsitePlusBounded potential
            (ringInteraction crossingParameter + ε • crossingEdge) u)
          (v : TileHilbert Vertex) =
        inner ℝ (u : TileHilbert Vertex)
          (onsitePlusBounded potential
            (ringInteraction crossingParameter + ε • crossingEdge) v) :=
    onsitePlusBounded_symmetric potential
      (ringInteraction crossingParameter + ε • crossingEdge)
      (crossingEdgePulseCorrection_symmetric ε)
  obtain ⟨energy, x0, hmove, hnear, hxne, heigen⟩ :=
    crossing_exists_distinct_perturbed_level_near ε hε
  obtain ⟨j, hj⟩ := bt.eigenvalue_occurs hsym x0 energy hxne heigen
  have hsmallnear : 2 * |ε| ≤ (1 / 256 : ℝ) := by
    linarith only [hsmall]
  have hjpair : j = n ∨ j = n + 1 := by
    apply hslot
    rw [hj]
    exact hnear.trans hsmallnear
  have hdarkne : (domainCrossingDark : TileHilbert Vertex) ≠ 0 := by
    change crossingDark ≠ 0
    intro hz
    have hn0 := crossingDark_norm_one
    rw [hz, norm_zero] at hn0
    norm_num at hn0
  obtain ⟨i, hi⟩ := bt.eigenvalue_occurs hsym
    domainCrossingDark crossingEnergy hdarkne
    (crossingDark_full_eigenvector ε)
  have hipair : i = n ∨ i = n + 1 := by
    apply hslot
    rw [hi, sub_self, abs_zero]
    norm_num
  have hij : i ≠ j := by
    intro he
    apply hmove
    calc
      energy = μ j := hj.symm
      _ = μ i := by rw [← he]
      _ = crossingEnergy := hi
  have hpair :
      (i = n ∧ j = n + 1) ∨ (i = n + 1 ∧ j = n) := by
    omega
  have hslots (k : ℕ)
      (hk : |μ k - crossingEnergy| ≤ (1 / 256 : ℝ)) :
      k = i ∨ k = j := by
    have hwhich := hslot k hk
    omega
  have hmoving_unique (k : ℕ) (hk : μ k = energy) : k = j := by
    have hknear : |μ k - crossingEnergy| ≤ (1 / 256 : ℝ) := by
      rw [hk]
      exact hnear.trans hsmallnear
    rcases hslots k hknear with hki | hkj
    · have hbad : energy = crossingEnergy := by
        calc
          energy = μ k := hk.symm
          _ = μ i := congrArg μ hki
          _ = crossingEnergy := hi
      exact (hmove hbad).elim
    · exact hkj
  refine ⟨μ j, ⟨bt.basis j, bt.mem_domain j⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hj] using hmove
  · simpa only [hj] using hnear
  · exact bt.basis.orthonormal.ne_zero j
  · exact bt.eigen j
  · intro t y hyne hye hynear
    obtain ⟨k, hk⟩ := bt.eigenvalue_occurs hsym y t hyne hye
    rcases hslots k (by rw [hk]; exact hynear) with hki | hkj
    · left
      calc
        t = μ k := hk.symm
        _ = μ i := congrArg μ hki
        _ = crossingEnergy := hi
    · right
      calc
        t = μ k := hk.symm
        _ = μ j := congrArg μ hkj
  · intro y hye
    refine ⟨inner ℝ (bt.basis j) (y : TileHilbert Vertex), ?_⟩
    exact bt.eigenvector_eq_smul_of_unique_level hsym
      (μ j) j rfl (by
        intro k hk
        exact hmoving_unique k (by simpa only [hj] using hk))
      y (by simpa only [hj] using hye)

/-!
## L3: the actual moving eigenspace has a nonzero bright amplitude

For the unique real moving level established by L2d, symmetry makes
every corresponding eigenvector perpendicular to the protected dark
state. The exact two-mode projector is therefore the bright line,
so the certified gap-to-residual estimate controls the full exterior
amplitude. A sufficiently small edge change makes zero bright
amplitude impossible for a nonzero moving eigenvector.
-/

/-- At every non-crossing eigenvalue, an eigenvector of the
single-edge perturbed infinite Hamiltonian is orthogonal to the
protected normalized dark state. No smallness hypothesis is needed. -/
theorem crossing_moving_eigenvector_dark_orthogonal
    (ε energy : ℝ) (x : infiniteOnsiteDomain potential)
    (heigen :
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x =
        energy • (x : TileHilbert Vertex))
    (hne : energy ≠ crossingEnergy) :
    inner ℝ crossingDark (x : TileHilbert Vertex) = 0 := by
  have h := crossingDark_pulse_amplitude ε x
  rw [heigen, real_inner_smul_right] at h
  have hz :
      (energy - crossingEnergy) *
          inner ℝ crossingDark (x : TileHilbert Vertex) = 0 := by
    nlinarith only [h]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

/-- A vector orthogonal to dark has compact-plane projection
equal to its exact bright amplitude times the normalized bright
state, even if it has an infinite-support exterior component. -/
theorem crossingQubitPart_eq_bright_smul_of_dark_orthogonal
    (ψ : TileHilbert Vertex)
    (horth : inner ℝ crossingDark ψ = 0) :
    crossingQubitPart ψ =
      (inner ℝ crossingBright ψ) • crossingBright := by
  have hd :
      inner ℝ crossingDark ψ =
        2 * (crossingCoeffA ψ + crossingCoeffB ψ) := by
    simp only [crossingDark, real_inner_smul_left, inner_add_left,
      crossingCoeffA, crossingCoeffB]
    ring
  have hb :
      inner ℝ crossingBright ψ =
        2 * (crossingCoeffA ψ - crossingCoeffB ψ) := by
    simp only [crossingBright, real_inner_smul_left, inner_sub_left,
      crossingCoeffA, crossingCoeffB]
    ring
  have hsum : crossingCoeffB ψ = -crossingCoeffA ψ := by
    linarith only [hd, horth]
  have hcoef :
      inner ℝ crossingBright ψ = 4 * crossingCoeffA ψ := by
    rw [hb, hsum]
    ring
  change
    crossingCoeffA ψ • compactA + crossingCoeffB ψ • compactB =
      (inner ℝ crossingBright ψ) •
        ((1 / 4 : ℝ) • (compactA - compactB))
  rw [hsum, hcoef]
  module

/-- A nearby nonzero moving eigenvector must have a nonzero bright
amplitude: otherwise the vector would be entirely exterior,
contradicting the certified first-order leakage bound. -/
theorem crossing_moving_eigenvector_bright_nonzero
    (ε energy : ℝ) (x : infiniteOnsiteDomain potential)
    (heigen :
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x =
        energy • (x : TileHilbert Vertex))
    (hne : energy ≠ crossingEnergy)
    (hnear : |energy - crossingEnergy| ≤ 2 * |ε|)
    (hsmall : |ε| ≤ 1 / 1024)
    (hxne : (x : TileHilbert Vertex) ≠ 0) :
    inner ℝ crossingBright (x : TileHilbert Vertex) ≠ 0 := by
  intro hz
  have horth :=
    crossing_moving_eigenvector_dark_orthogonal ε energy x heigen hne
  have hp : crossingQubitPart (x : TileHilbert Vertex) = 0 := by
    rw [crossingQubitPart_eq_bright_smul_of_dark_orthogonal
      (x : TileHilbert Vertex) horth, hz, zero_smul]
  have hq : crossingLeakage (x : TileHilbert Vertex) =
      (x : TileHilbert Vertex) := by
    simp only [crossingLeakage, hp, sub_zero]
  have hle :=
    crossingEdge_nearby_eigenvector_leakage_le_full
      ε energy x heigen hnear
  rw [hq] at hle
  have hnorm : 0 < ‖(x : TileHilbert Vertex)‖ :=
    norm_pos_iff.mpr hxne
  have hhalf : 512 * |ε| ≤ (1 / 2 : ℝ) := by
    linarith only [hsmall]
  have hmul :=
    mul_le_mul_of_nonneg_right hhalf (le_of_lt hnorm)
  nlinarith only [hle, hmul, hnorm]

/-- L3 source statement: the genuine moving eigenspace has bright
amplitude, is perpendicular to the dark line, and is controlled
quantitatively outside the unperturbed crossing plane. This initial
norm-relative estimate has coefficient 512; a sharper bound in terms
of the bright coefficient and exact external edge-force norm is
a separate next step. -/
theorem crossing_exists_moving_eigenvector_bright_and_leakage
    (ε : ℝ) (hε : ε ≠ 0) (hsmall : |ε| ≤ 1 / 1024) :
    ∃ (energy : ℝ) (x : infiniteOnsiteDomain potential),
      energy ≠ crossingEnergy ∧
      |energy - crossingEnergy| ≤ 2 * |ε| ∧
      (x : TileHilbert Vertex) ≠ 0 ∧
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x =
        energy • (x : TileHilbert Vertex) ∧
      inner ℝ crossingDark (x : TileHilbert Vertex) = 0 ∧
      inner ℝ crossingBright (x : TileHilbert Vertex) ≠ 0 ∧
      crossingQubitPart (x : TileHilbert Vertex) =
        (inner ℝ crossingBright (x : TileHilbert Vertex)) • crossingBright ∧
      ‖crossingLeakage (x : TileHilbert Vertex)‖ ≤
        512 * |ε| * ‖(x : TileHilbert Vertex)‖ := by
  obtain ⟨energy, x, hmove, hnear, hxne, heigen, _, _⟩ :=
    crossing_perturbed_isolated_pair_simple ε hε hsmall
  have horth :=
    crossing_moving_eigenvector_dark_orthogonal ε energy x heigen hmove
  have hbright :=
    crossing_moving_eigenvector_bright_nonzero
      ε energy x heigen hmove hnear hsmall hxne
  refine ⟨energy, x, hmove, hnear, hxne, heigen,
    horth, hbright, ?_, ?_⟩
  · exact crossingQubitPart_eq_bright_smul_of_dark_orthogonal
      (x : TileHilbert Vertex) horth
  · exact crossingEdge_nearby_eigenvector_leakage_le_full
      ε energy x heigen hnear

/-!
## L3: sharpen the full-exterior estimate using the actual edge force

The previous bound is norm-relative. Here the full exterior residual
is projected before taking its norm. The original residual is already
perpendicular to the exact crossing plane by symmetry; its perturbed
equation therefore involves only the exterior vector and the
projected edge force. This retains the precise external-edge norm
instead of replacing it prematurely by the total edge norm.
-/

/-- The exact crossing-plane orthogonal complement projection is
nonexpansive on the infinite real Hilbert space. -/
theorem crossingLeakage_norm_le (ψ : TileHilbert Vertex) :
    ‖crossingLeakage ψ‖ ≤ ‖ψ‖ := by
  have h := crossingQubitPart_leakage_norm_sq ψ
  have hsq : ‖crossingLeakage ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
    nlinarith only [h, sq_nonneg ‖crossingQubitPart ψ‖]
  nlinarith only [hsq, norm_nonneg ψ, norm_nonneg (crossingLeakage ψ)]

/-- The exterior projection respects subtraction as well as addition
and scalar multiplication. -/
theorem crossingLeakage_sub (ψ φ : TileHilbert Vertex) :
    crossingLeakage (ψ - φ) =
      crossingLeakage ψ - crossingLeakage φ := by
  have hneg : crossingLeakage (-φ) = -crossingLeakage φ := by
    calc
      crossingLeakage (-φ) =
          crossingLeakage ((-1 : ℝ) • φ) := by rw [neg_one_smul]
      _ = (-1 : ℝ) • crossingLeakage φ := crossingLeakage_smul (-1) φ
      _ = -crossingLeakage φ := by rw [neg_one_smul]
  calc
    crossingLeakage (ψ - φ) =
        crossingLeakage (ψ + -φ) := by rw [sub_eq_add_neg]
    _ = crossingLeakage ψ + crossingLeakage (-φ) :=
      crossingLeakage_add ψ (-φ)
    _ = crossingLeakage ψ - crossingLeakage φ := by
      rw [hneg, sub_eq_add_neg]

/-- The entire original Hamiltonian residual is orthogonal to the
two-dimensional crossing eigenspace, by exact symmetry. -/
theorem crossingLeakage_crossingResidual
    (x : infiniteOnsiteDomain potential) :
    crossingLeakage (crossingResidual x) = crossingResidual x := by
  have ha := crossingResidual_symmetric x domainCompactA
  rw [crossingResidual_compactA, inner_zero_right] at ha
  have hb := crossingResidual_symmetric x domainCompactB
  rw [crossingResidual_compactB, inner_zero_right] at hb
  have ha' : inner ℝ compactA (crossingResidual x) = 0 := by
    calc
      inner ℝ compactA (crossingResidual x) =
          inner ℝ (crossingResidual x) compactA := real_inner_comm _ _
      _ = 0 := ha
  have hb' : inner ℝ compactB (crossingResidual x) = 0 := by
    calc
      inner ℝ compactB (crossingResidual x) =
          inner ℝ (crossingResidual x) compactB := real_inner_comm _ _
      _ = 0 := hb
  have hp : crossingQubitPart (crossingResidual x) = 0 := by
    simp only [crossingQubitPart, crossingCoeffA, crossingCoeffB,
      ha', hb', zero_div, zero_smul, add_zero]
  simp only [crossingLeakage, hp, sub_zero]

/-- Full perturbed eigen-equation, projected to the true exterior
of the unperturbed double eigenspace. -/
theorem crossingResidual_projected_moving_eigenvector
    (ε energy : ℝ) (x : infiniteOnsiteDomain potential)
    (heigen :
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x =
        energy • (x : TileHilbert Vertex)) :
    crossingResidual x =
      (energy - crossingEnergy) •
        crossingLeakage (x : TileHilbert Vertex) -
      ε • crossingLeakage (crossingEdge (x : TileHilbert Vertex)) := by
  have h :=
    crossingEdge_perturbed_eigenvector_residual ε energy x heigen
  change crossingResidual x =
    (energy - crossingEnergy) • (x : TileHilbert Vertex) -
      ε • crossingEdge (x : TileHilbert Vertex) at h
  have hp := congrArg crossingLeakage h
  rw [crossingLeakage_crossingResidual,
    crossingLeakage_sub, crossingLeakage_smul, crossingLeakage_smul] at hp
  exact hp

/-- On a dark-orthogonal input, the exterior response of the
selected edge splits into an exact bright forcing vector and
the remaining exterior feedback. -/
theorem crossingLeakage_edge_bright_split
    (ψ : TileHilbert Vertex)
    (horth : inner ℝ crossingDark ψ = 0) :
    crossingLeakage (crossingEdge ψ) =
      (inner ℝ crossingBright ψ) •
        crossingLeakage (crossingEdge crossingBright) +
      crossingLeakage (crossingEdge (crossingLeakage ψ)) := by
  have hp :=
    crossingQubitPart_eq_bright_smul_of_dark_orthogonal ψ horth
  have he := congrArg crossingEdge (crossingQubitPart_add_leakage ψ)
  rw [map_add, hp, map_smul] at he
  have hes : crossingEdge ψ =
      (inner ℝ crossingBright ψ) • crossingEdge crossingBright +
        crossingEdge (crossingLeakage ψ) := he.symm
  rw [hes, crossingLeakage_add, crossingLeakage_smul]

/-- The precise L3 external-eigenvector estimate.
For the genuine infinite Hamiltonian, the exterior component q
of any non-crossing eigenvector near E* is bounded by the absolute
bright amplitude c times the ACTUAL external edge-force norm.

For 0 < |ε| ≤ 1/1024, the closed baseline gap g=1/128 gives
g - |energy-E*| - 2|ε| ≥ 1/256.
The theorem does not assume any unproved projected resolvent. -/
theorem crossing_moving_eigenvector_sharp_leakage
    (ε energy : ℝ) (x : infiniteOnsiteDomain potential)
    (heigen :
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x =
        energy • (x : TileHilbert Vertex))
    (hne : energy ≠ crossingEnergy)
    (hnear : |energy - crossingEnergy| ≤ 2 * |ε|)
    (hsmall : |ε| ≤ 1 / 1024) :
    ‖crossingLeakage (x : TileHilbert Vertex)‖ ≤
      256 * |ε| *
        |inner ℝ crossingBright (x : TileHilbert Vertex)| *
        ‖crossingLeakage (crossingEdge crossingBright)‖ := by
  let q : TileHilbert Vertex :=
    crossingLeakage (x : TileHilbert Vertex)
  let c : ℝ :=
    inner ℝ crossingBright (x : TileHilbert Vertex)
  let v : TileHilbert Vertex :=
    crossingLeakage (crossingEdge crossingBright)
  have horth :=
    crossing_moving_eigenvector_dark_orthogonal ε energy x heigen hne
  have hres :
      crossingResidual x =
        (energy - crossingEnergy) • q -
          ε • (c • v + crossingLeakage (crossingEdge q)) := by
    rw [crossingResidual_projected_moving_eigenvector ε energy x heigen,
      crossingLeakage_edge_bright_split
        (x : TileHilbert Vertex) horth]
  have hWq :
      ‖crossingLeakage (crossingEdge q)‖ ≤ 2 * ‖q‖ := by
    calc
      ‖crossingLeakage (crossingEdge q)‖ ≤
          ‖crossingEdge q‖ := crossingLeakage_norm_le _
      _ ≤ 2 * ‖q‖ := crossingEdge_apply_norm_le_two q
  have hforce :
      ‖c • v + crossingLeakage (crossingEdge q)‖ ≤
        |c| * ‖v‖ + 2 * ‖q‖ := by
    calc
      ‖c • v + crossingLeakage (crossingEdge q)‖ ≤
          ‖c • v‖ + ‖crossingLeakage (crossingEdge q)‖ :=
        norm_add_le _ _
      _ = |c| * ‖v‖ + ‖crossingLeakage (crossingEdge q)‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ |c| * ‖v‖ + 2 * ‖q‖ := add_le_add_right hWq _
  have hresnorm :
      ‖crossingResidual x‖ ≤
        |energy - crossingEnergy| * ‖q‖ +
          |ε| * (|c| * ‖v‖ + 2 * ‖q‖) := by
    calc
      ‖crossingResidual x‖ =
          ‖(energy - crossingEnergy) • q -
            ε • (c • v + crossingLeakage (crossingEdge q))‖ :=
        congrArg norm hres
      _ ≤ ‖(energy - crossingEnergy) • q‖ +
          ‖ε • (c • v + crossingLeakage (crossingEdge q))‖ :=
        norm_sub_le _ _
      _ = |energy - crossingEnergy| * ‖q‖ +
          |ε| * ‖c • v + crossingLeakage (crossingEdge q)‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ |energy - crossingEnergy| * ‖q‖ +
          |ε| * (|c| * ‖v‖ + 2 * ‖q‖) :=
        add_le_add_right
          (mul_le_mul_of_nonneg_left hforce (abs_nonneg ε)) _
  have hgap :
      crossingGapCandidate * ‖q‖ ≤ ‖crossingResidual x‖ :=
    crossingReducedGapResidualEstimate_full x
  have hmargin :
      (1 / 256 : ℝ) ≤
        crossingGapCandidate -
          |energy - crossingEnergy| - 2 * |ε| := by
    dsimp only [crossingGapCandidate]
    linarith only [hnear, hsmall]
  have hsqueezed :
      (crossingGapCandidate - |energy - crossingEnergy| - 2 * |ε|) *
          ‖q‖ ≤ |ε| * |c| * ‖v‖ := by
    nlinarith only [hgap, hresnorm]
  have hscaled :=
    mul_le_mul_of_nonneg_right hmargin (norm_nonneg q)
  have hquarter : (1 / 256 : ℝ) * ‖q‖ ≤
      |ε| * |c| * ‖v‖ := by
    nlinarith only [hscaled, hsqueezed]
  change ‖q‖ ≤ 256 * |ε| * |c| * ‖v‖
  nlinarith only [hquarter]

/-- A genuine simple moving eigenvector with nonzero bright component,
zero dark component and the sharp L3 external estimate. -/
theorem crossing_exists_moving_bright_sharp_leakage
    (ε : ℝ) (hε : ε ≠ 0) (hsmall : |ε| ≤ 1 / 1024) :
    ∃ (energy : ℝ) (x : infiniteOnsiteDomain potential),
      energy ≠ crossingEnergy ∧
      |energy - crossingEnergy| ≤ 2 * |ε| ∧
      (x : TileHilbert Vertex) ≠ 0 ∧
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x =
        energy • (x : TileHilbert Vertex) ∧
      inner ℝ crossingDark (x : TileHilbert Vertex) = 0 ∧
      inner ℝ crossingBright (x : TileHilbert Vertex) ≠ 0 ∧
      ‖crossingLeakage (x : TileHilbert Vertex)‖ ≤
        256 * |ε| *
          |inner ℝ crossingBright (x : TileHilbert Vertex)| *
          ‖crossingLeakage (crossingEdge crossingBright)‖ := by
  obtain ⟨energy, x, hmove, hnear, hxne, heigen, _, _⟩ :=
    crossing_perturbed_isolated_pair_simple ε hε hsmall
  refine ⟨energy, x, hmove, hnear, hxne, heigen, ?_, ?_, ?_⟩
  · exact crossing_moving_eigenvector_dark_orthogonal
      ε energy x heigen hmove
  · exact crossing_moving_eigenvector_bright_nonzero
      ε energy x heigen hmove hnear hsmall hxne
  · exact crossing_moving_eigenvector_sharp_leakage
      ε energy x heigen hmove hnear hsmall

/-!
## L4: true quadratic shift from the full bright eigenvector

The previously verified L3 bound controls the actual external part
of the unique moving eigenvector. Pairing the *exact* infinite-domain
eigenvector equation with bright and retaining the exact external
force v = Q W F yields the sharp 112 ε² energy bound, rather than
a mere Rayleigh-quotient estimate on the unperturbed bright mode.
-/

/-- The bright-to-exterior edge feedback is exactly the pairing
of the full projected edge force with the full exterior state.
The proof uses real symmetry and true orthogonality to the original
two-dimensional crossing eigenspace. -/
theorem crossingBright_edge_leakage_inner
    (ψ : TileHilbert Vertex) :
    inner ℝ crossingBright (crossingEdge (crossingLeakage ψ)) =
      inner ℝ (crossingLeakage (crossingEdge crossingBright))
        (crossingLeakage ψ) := by
  have hp :
      inner ℝ (crossingQubitPart (crossingEdge crossingBright))
        (crossingLeakage ψ) = 0 := by
    simp only [crossingQubitPart, inner_add_left, real_inner_smul_left,
      crossingLeakage_inner_compactA, crossingLeakage_inner_compactB]
    ring
  have hsplit := congrArg
    (fun z : TileHilbert Vertex => inner ℝ z (crossingLeakage ψ))
    (crossingQubitPart_add_leakage (crossingEdge crossingBright))
  rw [inner_add_left, hp, zero_add] at hsplit
  calc
    inner ℝ crossingBright (crossingEdge (crossingLeakage ψ)) =
        inner ℝ (crossingEdge crossingBright) (crossingLeakage ψ) :=
      (crossingEdge_symmetric_full crossingBright (crossingLeakage ψ)).symm
    _ = inner ℝ (crossingLeakage (crossingEdge crossingBright))
          (crossingLeakage ψ) := hsplit.symm

/-- Real Cauchy–Schwarz in absolute-value form without a unit-norm
assumption; used for the exact external coupling, not the total edge
operator norm. -/
theorem crossing_abs_inner_le_norm_mul
    (u v : TileHilbert Vertex) :
    |inner ℝ u v| ≤ ‖u‖ * ‖v‖ := by
  have hu : inner ℝ u v ≤ ‖u‖ * ‖v‖ :=
    real_inner_le_norm u v
  have hl : -(inner ℝ u v) ≤ ‖u‖ * ‖v‖ := by
    have h := real_inner_le_norm u (-v)
    simpa only [inner_neg_right, norm_neg] using h
  exact abs_le.mpr ⟨by linarith only [hl], hu⟩

/-- Sharp L4 bound on a *genuine* moving eigenvalue.
A nonzero bright coefficient is supplied, rather than dividing
through a possibly zero amplitude. All spectral, residual and
external-force estimates were previously kernel-verified. -/
theorem crossing_moving_energy_quadratic_bound
    (ε energy : ℝ) (x : infiniteOnsiteDomain potential)
    (heigen :
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x =
        energy • (x : TileHilbert Vertex))
    (hne : energy ≠ crossingEnergy)
    (hnear : |energy - crossingEnergy| ≤ 2 * |ε|)
    (hsmall : |ε| ≤ 1 / 1024)
    (hbright : inner ℝ crossingBright (x : TileHilbert Vertex) ≠ 0) :
    |energy - (crossingEnergy + ε / 4)| ≤ 112 * ε ^ 2 := by
  let c : ℝ := inner ℝ crossingBright (x : TileHilbert Vertex)
  let q : TileHilbert Vertex :=
    crossingLeakage (x : TileHilbert Vertex)
  let v : TileHilbert Vertex :=
    crossingLeakage (crossingEdge crossingBright)
  have hidentity :
      (energy - (crossingEnergy + ε / 4)) * c =
        ε * inner ℝ v q := by
    have hp := crossingBright_pulse_amplitude ε x
    rw [heigen, real_inner_smul_right,
      crossingBright_edge_leakage_inner] at hp
    change energy * c = (crossingEnergy + ε / 4) * c +
      ε * inner ℝ v q at hp
    nlinarith only [hp]
  have habs := congrArg abs hidentity
  rw [abs_mul, abs_mul] at habs
  have hcoupling :
      |energy - (crossingEnergy + ε / 4)| * |c| ≤
        (|ε| * ‖v‖) * ‖q‖ := by
    calc
      |energy - (crossingEnergy + ε / 4)| * |c| =
          |ε| * |inner ℝ v q| := habs
      _ ≤ |ε| * (‖v‖ * ‖q‖) :=
        mul_le_mul_of_nonneg_left
          (crossing_abs_inner_le_norm_mul v q) (abs_nonneg ε)
      _ = (|ε| * ‖v‖) * ‖q‖ := by ring
  have hsharp :=
    crossing_moving_eigenvector_sharp_leakage
      ε energy x heigen hne hnear hsmall
  change ‖q‖ ≤ 256 * |ε| * |c| * ‖v‖ at hsharp
  have hscaled :
      (|ε| * ‖v‖) * ‖q‖ ≤
        (|ε| * ‖v‖) * (256 * |ε| * |c| * ‖v‖) :=
    mul_le_mul_of_nonneg_left hsharp
      (mul_nonneg (abs_nonneg ε) (norm_nonneg v))
  have hv : ‖v‖ ^ 2 = 7 / 16 := crossingBright_external_edge_norm_sq
  have htotal :
      |energy - (crossingEnergy + ε / 4)| * |c| ≤
        112 * ε ^ 2 * |c| := by
    calc
      |energy - (crossingEnergy + ε / 4)| * |c| ≤
          (|ε| * ‖v‖) * ‖q‖ := hcoupling
      _ ≤ (|ε| * ‖v‖) * (256 * |ε| * |c| * ‖v‖) := hscaled
      _ = 256 * |ε| ^ 2 * |c| * ‖v‖ ^ 2 := by ring
      _ = 112 * ε ^ 2 * |c| := by
        rw [hv, sq_abs]
        ring
  exact (mul_le_mul_iff_of_pos_right (abs_pos.mpr hbright)).mp htotal

/-- A true moving level, its nonzero natural-domain eigenvector,
and the sharp second-order eigenvalue bound all exist simultaneously.
The level is the unique non-crossing simple level in the L2d window. -/
theorem crossing_exists_moving_level_quadratic_bound
    (ε : ℝ) (hε : ε ≠ 0) (hsmall : |ε| ≤ 1 / 1024) :
    ∃ (energy : ℝ) (x : infiniteOnsiteDomain potential),
      energy ≠ crossingEnergy ∧
      |energy - crossingEnergy| ≤ 2 * |ε| ∧
      (x : TileHilbert Vertex) ≠ 0 ∧
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x =
        energy • (x : TileHilbert Vertex) ∧
      inner ℝ crossingBright (x : TileHilbert Vertex) ≠ 0 ∧
      |energy - (crossingEnergy + ε / 4)| ≤ 112 * ε ^ 2 := by
  obtain ⟨energy, x, hmove, hnear, hxne, heigen, _, hbright, _⟩ :=
    crossing_exists_moving_bright_sharp_leakage ε hε hsmall
  refine ⟨energy, x, hmove, hnear, hxne, heigen, hbright, ?_⟩
  exact crossing_moving_energy_quadratic_bound
    ε energy x heigen hmove hnear hsmall hbright

/-!
## L5: signed spectral shift and one full infinite-operator theorem

The already verified quadratic remainder is smaller than the
first-order shift in the stated epsilon range:
112 ε² ≤ (7/64)|ε| < |ε|/4.
Thus the sign of the genuine moving eigenvalue's displacement
agrees with the sign of epsilon. No monotonicity claim about a
time-dependent propagator is being made.
-/

/-- The verified quadratic remainder forces the *true* moving
energy to shift strictly upward for a positive edge correction,
and strictly downward for a negative correction. This is a
pure numerical consequence of |ε| ≤ 1/1024 and the actual
full-eigenvalue bound; it is not a matrix approximation. -/
theorem crossing_moving_energy_shift_sign
    (ε energy : ℝ) (hsmall : |ε| ≤ 1 / 1024)
    (hquad :
      |energy - (crossingEnergy + ε / 4)| ≤ 112 * ε ^ 2) :
    (0 < ε → crossingEnergy < energy) ∧
    (ε < 0 → energy < crossingEnergy) := by
  have hprod :
      |ε| * |ε| ≤ (1 / 1024 : ℝ) * |ε| :=
    mul_le_mul_of_nonneg_right hsmall (abs_nonneg ε)
  have herr :
      112 * ε ^ 2 ≤ (7 / 64 : ℝ) * |ε| := by
    rw [← sq_abs]
    nlinarith only [hprod]
  have hb := abs_le.mp hquad
  constructor
  · intro hpos
    have habs : |ε| = ε := abs_of_pos hpos
    rw [habs] at herr
    have hstrict : (0 : ℝ) < (9 / 64 : ℝ) * ε :=
      mul_pos (by norm_num) hpos
    linarith only [hb.1, herr, hstrict]
  · intro hneg
    have habs : |ε| = -ε := abs_of_neg hneg
    rw [habs] at herr
    have hstrict : (9 / 64 : ℝ) * ε < (0 : ℝ) :=
      mul_neg_of_pos_of_neg (by norm_num) hneg
    linarith only [hb.2, herr, hstrict]

/-- L5: a self-contained package for the *real natural-domain
point spectrum* of the genuine infinite Ammann–Beenker Hamiltonian.

For each nonzero |ε| ≤ 1/1024, the dark line remains a simple,
fixed eigenspace; there is exactly one other, simple eigenvalue
in the closed 1/256 window; its sign follows epsilon, its error
about E*+ε/4 is at most 112 ε², and each moving eigenvector
is bright with controlled full exterior component.

Every claim uses the original infinite domain, not a two-level
restriction. Complex spectrum and quantum propagators are not
claimed by this theorem. -/
theorem crossing_final_signed_bright_spectral_splitting
    (ε : ℝ) (hε : ε ≠ 0) (hsmall : |ε| ≤ 1 / 1024) :
    ∃ (energy : ℝ) (x : infiniteOnsiteDomain potential),
      energy ≠ crossingEnergy ∧
      |energy - crossingEnergy| ≤ 2 * |ε| ∧
      (x : TileHilbert Vertex) ≠ 0 ∧
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x =
        energy • (x : TileHilbert Vertex) ∧
      (0 < ε → crossingEnergy < energy) ∧
      (ε < 0 → energy < crossingEnergy) ∧
      |energy - (crossingEnergy + ε / 4)| ≤ 112 * ε ^ 2 ∧
      inner ℝ crossingDark (x : TileHilbert Vertex) = 0 ∧
      inner ℝ crossingBright (x : TileHilbert Vertex) ≠ 0 ∧
      crossingQubitPart (x : TileHilbert Vertex) =
        (inner ℝ crossingBright (x : TileHilbert Vertex)) • crossingBright ∧
      ‖crossingLeakage (x : TileHilbert Vertex)‖ ≤
        256 * |ε| *
          |inner ℝ crossingBright (x : TileHilbert Vertex)| *
          ‖crossingLeakage (crossingEdge crossingBright)‖ ∧
      (∀ (t : ℝ) (y : infiniteOnsiteDomain potential),
        (y : TileHilbert Vertex) ≠ 0 →
        onsitePlusBounded potential
            (ringInteraction crossingParameter + ε • crossingEdge) y =
          t • (y : TileHilbert Vertex) →
        |t - crossingEnergy| ≤ 1 / 256 →
        t = crossingEnergy ∨ t = energy) ∧
      (∀ y : infiniteOnsiteDomain potential,
        onsitePlusBounded potential
            (ringInteraction crossingParameter + ε • crossingEdge) y =
          energy • (y : TileHilbert Vertex) →
        ∃ c : ℝ, (y : TileHilbert Vertex) = c • (x : TileHilbert Vertex)) ∧
      (∀ y : infiniteOnsiteDomain potential,
        onsitePlusBounded potential
            (ringInteraction crossingParameter + ε • crossingEdge) y =
          crossingEnergy • (y : TileHilbert Vertex) →
        ∃ c : ℝ, (y : TileHilbert Vertex) = c • crossingDark) := by
  obtain ⟨energy, x, hmove, hnear, hxne, heigen, hunique, hsimple⟩ :=
    crossing_perturbed_isolated_pair_simple ε hε hsmall
  have hbright :=
    crossing_moving_eigenvector_bright_nonzero
      ε energy x heigen hmove hnear hsmall hxne
  have hquad :=
    crossing_moving_energy_quadratic_bound
      ε energy x heigen hmove hnear hsmall hbright
  have hsign := crossing_moving_energy_shift_sign ε energy hsmall hquad
  have horth :=
    crossing_moving_eigenvector_dark_orthogonal
      ε energy x heigen hmove
  have hproj :=
    crossingQubitPart_eq_bright_smul_of_dark_orthogonal
      (x : TileHilbert Vertex) horth
  have hsharp :=
    crossing_moving_eigenvector_sharp_leakage
      ε energy x heigen hmove hnear hsmall
  refine ⟨energy, x, hmove, hnear, hxne, heigen, hsign.1, hsign.2,
    hquad, horth, hbright, hproj, hsharp, hunique, hsimple, ?_⟩
  intro y hyeigen
  exact crossingPerturbedEnergy_dark_only ε hε y hyeigen

end
end SpectralGeometry.AmmannBeenker
