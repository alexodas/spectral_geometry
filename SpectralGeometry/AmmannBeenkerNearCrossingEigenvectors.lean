module

public import SpectralGeometry.AmmannBeenkerQubitLeakage
public import SpectralGeometry.AmmannBeenkerCrossingGapOrthogonality
public import SpectralGeometry.DomainEigenbasisGapResidual

public section

/-!
# A quantitative bridge from the crossing gap to nearby perturbed modes

The crossing has an exactly two-dimensional eigenspace and a rigorously
isolated real spectrum, with gap radius g = 1/128. The original
connecting-edge operator also has exactly computed norm 2.

This file isolates the missing *reduced-gap residual estimate* needed
to translate that spectral isolation into an explicit eigenvector
stability inequality. In a complete self-adjoint spectral calculus,
a suitable residual estimate on the orthogonal complement follows
from the gap. That inference has NOT yet been formalized here.

Assuming that residual estimate, every eigenvector of a small
single-edge perturbation whose energy stays near the crossing has
an explicit bound on its total overlap with *all* external modes.
This bound is valid in the actual infinite graph's real Hilbert
space and on the original natural domain.

This is a statement about individual perturbed eigenvectors, NOT
yet a norm estimate for a two-dimensional spectral projector and
NOT a pulse-propagator or controllability result.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- Restoring the baseline Hamiltonian subtracts exactly the applied
bounded edge contribution. This is an identity on the *same* natural
domain for every state, not only for eigenvectors. -/
theorem crossingEdge_perturbation_identity (ε : ℝ)
    (x : infiniteOnsiteDomain potential) :
    onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge) x =
      onsitePlusBounded potential (ringInteraction crossingParameter) x +
        ε • crossingEdge (x : TileHilbert Vertex) := by
  simp only [onsitePlusBounded_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  abel

/-- The original crossing-energy residual of a perturbed
eigenvector is exactly the energy shift minus the edge force. -/
theorem crossingEdge_perturbed_eigenvector_residual
    (ε energy : ℝ) (x : infiniteOnsiteDomain potential)
    (heigen :
      onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge) x =
          energy • (x : TileHilbert Vertex)) :
    onsitePlusBounded potential (ringInteraction crossingParameter) x -
        crossingEnergy • (x : TileHilbert Vertex) =
      (energy - crossingEnergy) • (x : TileHilbert Vertex) -
        ε • crossingEdge (x : TileHilbert Vertex) := by
  rw [crossingEdge_perturbation_identity] at heigen
  have he :
      onsitePlusBounded potential (ringInteraction crossingParameter) x =
        energy • (x : TileHilbert Vertex) -
          ε • crossingEdge (x : TileHilbert Vertex) :=
    eq_sub_of_add_eq heigen
  rw [he, sub_smul]
  abel

/-- The real infinite-graph edge perturbation has uniform force
bound 2‖x‖, with *no* finite-volume approximation. -/
theorem crossingEdge_apply_norm_le_two (x : TileHilbert Vertex) :
    ‖crossingEdge x‖ ≤ 2 * ‖x‖ := by
  calc
    ‖crossingEdge x‖ ≤ ‖crossingEdge‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = 2 * ‖x‖ := by rw [crossingEdge_opNorm]

/-- Exact spectral-gap-to-residual estimate *required* for the next
step. This is a proposition, not asserted to hold by definition.
The current gap theorem isolates the real spectrum but does not
yet identify this quantitative inequality in Lean. -/
@[expose] def CrossingReducedGapResidualEstimate : Prop :=
  ∀ x : infiniteOnsiteDomain potential,
    crossingGapCandidate *
        ‖crossingLeakage (x : TileHilbert Vertex)‖ ≤
      ‖onsitePlusBounded potential (ringInteraction crossingParameter) x -
        crossingEnergy • (x : TileHilbert Vertex)‖

/-- The *already certified* exclusion of other crossing eigenvalues,
together with a complete symmetric real domain eigenbasis of the
original operator, implies the reduced-gap residual estimate
for the actual original two-mode projector.

This theorem does NOT assume the desired residual inequality. It
derives it from the graph's proved 1/128 eigenvalue exclusion and
exact representation of every crossing eigenvector. Constructing
the corresponding complete basis/symmetry input for this concrete
operator is the remaining instantiation obligation. -/
theorem crossingReducedGapResidualEstimate_of_domainEigenbasis
    {ι : Type*} {ev : ι → ℝ}
    (b : DomainEigenbasis
      (infiniteOnsiteDomain potential)
      (onsitePlusBounded potential (ringInteraction crossingParameter)) ev)
    (hsymm : ∀ x y : infiniteOnsiteDomain potential,
      inner ℝ
          (onsitePlusBounded potential (ringInteraction crossingParameter) x)
          (y : TileHilbert Vertex) =
        inner ℝ (x : TileHilbert Vertex)
          (onsitePlusBounded potential (ringInteraction crossingParameter) y)) :
    CrossingReducedGapResidualEstimate := by
  have hseparated (i : ι) (hne : ev i ≠ crossingEnergy) :
      crossingGapCandidate ≤ |ev i - crossingEnergy| := by
    by_contra hn
    have hnear :
        |ev i - crossingEnergy| ≤ crossingGapCandidate :=
      le_of_lt (lt_of_not_ge hn)
    apply (crossingGapCandidate_no_other_full_eigenvector
      (ev i) hne hnear)
    exact ⟨⟨b.basis i, b.mem_domain i⟩,
      b.basis.orthonormal.ne_zero i, b.eigen i⟩
  intro x
  let pdom : infiniteOnsiteDomain potential :=
    crossingCoeffA (x : TileHilbert Vertex) • domainCompactA +
      crossingCoeffB (x : TileHilbert Vertex) • domainCompactB
  let qdom : infiniteOnsiteDomain potential := x - pdom
  have hqcoe :
      (qdom : TileHilbert Vertex) =
        crossingLeakage (x : TileHilbert Vertex) := by
    change
      (x : TileHilbert Vertex) -
        (crossingCoeffA (x : TileHilbert Vertex) • compactA +
          crossingCoeffB (x : TileHilbert Vertex) • compactB) =
        crossingLeakage (x : TileHilbert Vertex)
    rfl
  have hp :
      onsitePlusBounded potential (ringInteraction crossingParameter) pdom =
        crossingEnergy • (pdom : TileHilbert Vertex) := by
    change
      onsitePlusBounded potential (ringInteraction crossingParameter)
        (crossingCoeffA (x : TileHilbert Vertex) • domainCompactA +
          crossingCoeffB (x : TileHilbert Vertex) • domainCompactB) =
      crossingEnergy • crossingQubitPart (x : TileHilbert Vertex)
    exact crossingQubitPart_restored_eigenvector (x : TileHilbert Vertex)
  have hres :
      onsitePlusBounded potential (ringInteraction crossingParameter) qdom -
          crossingEnergy • (qdom : TileHilbert Vertex) =
        onsitePlusBounded potential (ringInteraction crossingParameter) x -
          crossingEnergy • (x : TileHilbert Vertex) := by
    have he :
        onsitePlusBounded potential (ringInteraction crossingParameter) qdom =
          onsitePlusBounded potential (ringInteraction crossingParameter) x -
            crossingEnergy • (pdom : TileHilbert Vertex) := by
      change onsitePlusBounded potential (ringInteraction crossingParameter)
          (x - pdom) = _
      rw [map_sub, hp]
    rw [he]
    change
      (onsitePlusBounded potential (ringInteraction crossingParameter) x -
        crossingEnergy • (pdom : TileHilbert Vertex)) -
          crossingEnergy •
            ((x : TileHilbert Vertex) - (pdom : TileHilbert Vertex)) =
      onsitePlusBounded potential (ringInteraction crossingParameter) x -
        crossingEnergy • (x : TileHilbert Vertex)
    rw [smul_sub]
    abel
  have hsupport (i : ι) (hi : ev i = crossingEnergy) :
      inner ℝ (b.basis i) (qdom : TileHilbert Vertex) = 0 := by
    have he :
        onsitePlusBounded potential (ringInteraction crossingParameter)
            ⟨b.basis i, b.mem_domain i⟩ =
          crossingEnergy • b.basis i := by
      simpa only [hi] using b.eigen i
    have hrepr := crossing_eigenvector_representation
      ⟨b.basis i, b.mem_domain i⟩ he
    change
      b.basis i =
        (b.basis i) (centralVertex 1) • compactA +
          (b.basis i) (centralVertex 9) • compactB at hrepr
    rw [hqcoe, hrepr]
    simp only [inner_add_left, real_inner_smul_left,
      crossingLeakage_inner_compactA, crossingLeakage_inner_compactB]
    ring
  have hq := DomainEigenbasis.norm_le_residual_of_gap
      b hsymm crossingEnergy crossingGapCandidate
      crossingGapCandidate_pos hseparated qdom hsupport
  rw [hres] at hq
  rw [hqcoe] at hq
  exact hq

/-- Assuming the reduced-gap residual estimate, the external norm
of *every* perturbed full-domain eigenvector is controlled by the
distance of its perturbed energy from E*, and the applied edge weight.
The factor 2 is the *proved exact operator norm* of W. -/
theorem crossingEdge_perturbed_eigenvector_gap_bound
    (hgap : CrossingReducedGapResidualEstimate)
    (ε energy : ℝ) (x : infiniteOnsiteDomain potential)
    (heigen :
      onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge) x =
          energy • (x : TileHilbert Vertex)) :
    crossingGapCandidate *
        ‖crossingLeakage (x : TileHilbert Vertex)‖ ≤
      |energy - crossingEnergy| * ‖(x : TileHilbert Vertex)‖ +
        2 * |ε| * ‖(x : TileHilbert Vertex)‖ := by
  have hres :=
    crossingEdge_perturbed_eigenvector_residual ε energy x heigen
  have hnorm :
      ‖onsitePlusBounded potential (ringInteraction crossingParameter) x -
        crossingEnergy • (x : TileHilbert Vertex)‖ ≤
      |energy - crossingEnergy| * ‖(x : TileHilbert Vertex)‖ +
        |ε| * ‖crossingEdge (x : TileHilbert Vertex)‖ := by
    rw [hres]
    calc
      ‖(energy - crossingEnergy) • (x : TileHilbert Vertex) -
          ε • crossingEdge (x : TileHilbert Vertex)‖ ≤
        ‖(energy - crossingEnergy) • (x : TileHilbert Vertex)‖ +
          ‖ε • crossingEdge (x : TileHilbert Vertex)‖ :=
        norm_sub_le _ _
      _ = |energy - crossingEnergy| * ‖(x : TileHilbert Vertex)‖ +
          |ε| * ‖crossingEdge (x : TileHilbert Vertex)‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
  calc
    crossingGapCandidate *
        ‖crossingLeakage (x : TileHilbert Vertex)‖ ≤
      ‖onsitePlusBounded potential (ringInteraction crossingParameter) x -
        crossingEnergy • (x : TileHilbert Vertex)‖ := hgap x
    _ ≤ |energy - crossingEnergy| * ‖(x : TileHilbert Vertex)‖ +
        |ε| * ‖crossingEdge (x : TileHilbert Vertex)‖ := hnorm
    _ ≤ |energy - crossingEnergy| * ‖(x : TileHilbert Vertex)‖ +
        |ε| * (2 * ‖(x : TileHilbert Vertex)‖) :=
      add_le_add_right
        (mul_le_mul_of_nonneg_left
          (crossingEdge_apply_norm_le_two (x : TileHilbert Vertex))
          (abs_nonneg ε)) _
    _ = |energy - crossingEnergy| * ‖(x : TileHilbert Vertex)‖ +
        2 * |ε| * ‖(x : TileHilbert Vertex)‖ := by ring

/-- If the perturbed eigenvalue is within the usual bounded-correction
shift window |energy-E*| ≤ 2|ε|, the 1/128 gap gives an explicit
first-order bound on off-plane amplitude: at most 512|ε|‖x‖.

This is a genuinely infinite-graph result, but it is CONDITIONAL:
the exact reduced-residual spectral consequence and eigenvalue-window
hypothesis must be supplied before applying it. -/
theorem crossingEdge_nearby_eigenvector_leakage_le
    (hgap : CrossingReducedGapResidualEstimate)
    (ε energy : ℝ) (x : infiniteOnsiteDomain potential)
    (heigen :
      onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge) x =
          energy • (x : TileHilbert Vertex))
    (hnear : |energy - crossingEnergy| ≤ 2 * |ε|) :
    ‖crossingLeakage (x : TileHilbert Vertex)‖ ≤
      512 * |ε| * ‖(x : TileHilbert Vertex)‖ := by
  have h :=
    crossingEdge_perturbed_eigenvector_gap_bound hgap ε energy x heigen
  have hnear_mul :=
    mul_le_mul_of_nonneg_right hnear (norm_nonneg (x : TileHilbert Vertex))
  have hb :
      crossingGapCandidate *
          ‖crossingLeakage (x : TileHilbert Vertex)‖ ≤
        4 * |ε| * ‖(x : TileHilbert Vertex)‖ := by
    nlinarith
  change (1 / 128 : ℝ) *
      ‖crossingLeakage (x : TileHilbert Vertex)‖ ≤
    4 * |ε| * ‖(x : TileHilbert Vertex)‖ at hb
  nlinarith

/-- The original Ammann–Beenker crossing has the required
reduced-gap residual estimate UNCONDITIONALLY.

The full real eigenbasis is constructed from the proper onsite potential,
the bounded symmetric interaction, and the existing compact-resolvent
theory. The precise 1/128 separation and the complete two-mode
eigenspace have already been proved. -/
theorem crossingReducedGapResidualEstimate_full :
    CrossingReducedGapResidualEstimate := by
  have hsymB :
      ∀ x y : TileHilbert Vertex,
        inner ℝ ((ringInteraction crossingParameter) x) y =
          inner ℝ x ((ringInteraction crossingParameter) y) := by
    simpa only [ringInteraction] using
      (finiteSectorCorrection_symmetric interaction interaction_symmetric
        (neighbors origin) crossingParameter)
  obtain ⟨ev, _hev, ⟨b⟩⟩ :=
    onsitePlusBounded_exists_orderedEigenbasis
      potential 1 potential_lower potential_proper
      (ringInteraction crossingParameter) hsymB
  have hsymm :
      ∀ x y : infiniteOnsiteDomain potential,
        inner ℝ
            (onsitePlusBounded potential (ringInteraction crossingParameter) x)
            (y : TileHilbert Vertex) =
          inner ℝ (x : TileHilbert Vertex)
            (onsitePlusBounded potential (ringInteraction crossingParameter) y) :=
    onsitePlusBounded_symmetric potential
      (ringInteraction crossingParameter) hsymB
  exact crossingReducedGapResidualEstimate_of_domainEigenbasis b hsymm

/-- The certified gap and the exact single-edge operator norm
give an UNCONDITIONAL residual-to-leakage bound for every perturbed
eigenvector, including all the infinite-graph external modes. -/
theorem crossingEdge_perturbed_eigenvector_gap_bound_full
    (ε energy : ℝ) (x : infiniteOnsiteDomain potential)
    (heigen :
      onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge) x =
          energy • (x : TileHilbert Vertex)) :
    crossingGapCandidate *
        ‖crossingLeakage (x : TileHilbert Vertex)‖ ≤
      |energy - crossingEnergy| * ‖(x : TileHilbert Vertex)‖ +
        2 * |ε| * ‖(x : TileHilbert Vertex)‖ :=
  crossingEdge_perturbed_eigenvector_gap_bound
    crossingReducedGapResidualEstimate_full ε energy x heigen

/-- Whenever a genuine perturbed eigenvector lies in the expected
energy-shift window, its total external amplitude is at most
512|ε| times its norm. The gap and residual hypotheses are now
**proved** for the full graph; only the stated eigenvalue-window
condition is needed to identify a near-crossing eigenvector. -/
theorem crossingEdge_nearby_eigenvector_leakage_le_full
    (ε energy : ℝ) (x : infiniteOnsiteDomain potential)
    (heigen :
      onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge) x =
          energy • (x : TileHilbert Vertex))
    (hnear : |energy - crossingEnergy| ≤ 2 * |ε|) :
    ‖crossingLeakage (x : TileHilbert Vertex)‖ ≤
      512 * |ε| * ‖(x : TileHilbert Vertex)‖ :=
  crossingEdge_nearby_eigenvector_leakage_le
    crossingReducedGapResidualEstimate_full ε energy x heigen hnear


/-- A nonzero change of the chosen edge cannot leave a crossing-energy
eigenvector coupled to that edge.  This is a full-domain consequence of
the rank-one perturbation, symmetry of the original Hamiltonian, and
the explicit nonzero pairing with compactA. -/
theorem crossingEdge_zero_of_perturbed_crossing_eigen
    (ε : ℝ) (hε : ε ≠ 0)
    (x : infiniteOnsiteDomain potential)
    (heigen :
      onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge) x =
          crossingEnergy • (x : TileHilbert Vertex)) :
    crossingEdge (x : TileHilbert Vertex) = 0 := by
  have hres :
      crossingResidual x =
        -(ε • crossingEdge (x : TileHilbert Vertex)) := by
    have h := crossingEdge_perturbed_eigenvector_residual
      ε crossingEnergy x heigen
    change crossingResidual x =
      (crossingEnergy - crossingEnergy) • (x : TileHilbert Vertex) -
        ε • crossingEdge (x : TileHilbert Vertex) at h
    simpa only [sub_self, zero_smul, zero_sub] using h
  have horth : inner ℝ (crossingResidual x) compactA = 0 := by
    have hs := crossingResidual_symmetric x domainCompactA
    rw [crossingResidual_compactA, inner_zero_right] at hs
    exact hs
  have hpair :
      ε * inner ℝ (crossingEdge (x : TileHilbert Vertex)) compactA = 0 := by
    rw [hres, inner_neg_left, real_inner_smul_left] at horth
    linarith only [horth]
  have hinner :
      inner ℝ compactA (crossingEdge (x : TileHilbert Vertex)) = 0 := by
    calc
      inner ℝ compactA (crossingEdge (x : TileHilbert Vertex)) =
          inner ℝ (crossingEdge (x : TileHilbert Vertex)) compactA :=
        real_inner_comm _ _
      _ = 0 := (mul_eq_zero.mp hpair).resolve_left hε
  have hcoeff :
      (x : TileHilbert Vertex) compactSiteA -
        (x : TileHilbert Vertex) compactSiteB = 0 := by
    rw [crossingEdge_inner] at hinner
    simpa only [compactA_siteA, compactA_siteB,
      sub_zero, mul_one] using hinner
  rw [crossingEdge_apply, hcoeff, zero_smul]

/-- For every nonzero edge strength the original crossing energy has
exactly the dark direction as its entire eigenspace.  This does not
yet construct or locate the displaced bright eigenvalue. -/
theorem crossingPerturbedEnergy_dark_only
    (ε : ℝ) (hε : ε ≠ 0)
    (x : infiniteOnsiteDomain potential)
    (heigen :
      onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge) x =
          crossingEnergy • (x : TileHilbert Vertex)) :
    ∃ c : ℝ, (x : TileHilbert Vertex) = c • crossingDark := by
  have hW :
      crossingEdge (x : TileHilbert Vertex) = 0 :=
    crossingEdge_zero_of_perturbed_crossing_eigen ε hε x heigen
  have hbase :
      onsitePlusBounded potential (ringInteraction crossingParameter) x =
        crossingEnergy • (x : TileHilbert Vertex) := by
    have h := crossingEdge_perturbation_identity ε x
    rw [hW, smul_zero, add_zero] at h
    exact h.symm.trans heigen
  let r : ℝ := x.1 (centralVertex 1)
  let s : ℝ := x.1 (centralVertex 9)
  have hrep :
      (x : TileHilbert Vertex) = r • compactA + s • compactB :=
    crossing_eigenvector_representation x hbase
  have hforce : crossingEdge compactA ≠ 0 := by
    intro hzero
    have hn := crossingEdge_compactA_norm_sq
    rw [hzero, norm_zero] at hn
    norm_num at hn
  have hrs : (r - s) • crossingEdge compactA = 0 := by
    have h := congrArg crossingEdge hrep
    rw [hW, crossingEdge_two_mode_action] at h
    exact h.symm
  have heq : r = s := by
    have hz : r - s = 0 := (smul_eq_zero.mp hrs).resolve_right hforce
    exact sub_eq_zero.mp hz
  refine ⟨4 * r, ?_⟩
  calc
    (x : TileHilbert Vertex) =
        r • compactA + s • compactB := hrep
    _ = r • (compactA + compactB) := by rw [← heq, smul_add]
    _ = (4 * r) • crossingDark := by
      rw [crossingDark, smul_smul,
        show (4 * r) * (1 / 4 : ℝ) = r by ring]

end
end SpectralGeometry.AmmannBeenker
