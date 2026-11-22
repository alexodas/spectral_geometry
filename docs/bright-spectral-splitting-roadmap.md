# Bright spectral splitting — Lean proof roadmap

**Research branch:** `research/bright-spectral-splitting-20261122`
**Scope:** the actual infinite confined Ammann–Beenker graph, the natural onsite domain, the real self-adjoint Hamiltonian and the single selected edge.
**Status:** L1–L2d are fully Lean/Comparator verified (Actions #319–#324), and the initial L3 bright-amplitude and exterior-norm bound passed both jobs in Action #326. The sharp L3 full-operator bound `‖Qx‖≤256|ε||c|‖QWF‖` also passed the full Lean and independent Comparator jobs in Action #328 (commit `0590eb7`), with `‖QWF‖²=7/16`. The open objectives are the sign and `112ε²` eigenvalue remainder and final consolidation (L4–L5). No change to existing Palomar packaging is required.

## 1. Established starting point

Let `H₀ = onsitePlusBounded potential (ringInteraction crossingParameter)`,
`Hε = H₀ + ε W`, `E_* = crossingEnergy`, `W = crossingEdge`.
The complete unperturbed eigenspace at `E_*` is the plane spanned by the
compact normalized dark `D = (a+b)/4` and bright `F = (a-b)/4`.
Its dimension is **exactly two**, and the full real spectrum has no
other point within the **closed radius g = 1/128**. The edge operator
is symmetric, positive, rank one, and has exact norm **2**.
The equation `Hε D = E_* D` holds for all real ε.

Already formalized: `crossingEigenspace_finrank`,
`crossing_eigenvector_representation`,
`crossingGapCandidate_realSpectrum_isolated`,
`crossingEdge_opNorm`,
`crossingReducedGapResidualEstimate_full`,
`crossingBright_pulse_amplitude`,
`crossingEdge_two_mode_leakage_norm_sq`,
`onsitePlusBounded_exists_orderedEigenbasis`, and
`onsitePlusBounded_ordered_perturbation_bound`.
The last theorem supplies `|μ_n − λ_n| ≤ ‖εW‖ = 2|ε|` for the
ordered eigenvalues of H₀ and Hε.

The two-mode leakage identity gives `‖QWF‖² = 7/16`, where Q is
the orthogonal projection onto the complement of span(D,F).
`AmmannBeenkerBrightSpectralSplitting.lean` includes the verified
specialization, alongside the ordered-eigenbasis stability result.

## 2. Intended main theorem — NOT YET PROVED

For `0 < |ε| ≤ 1/1024`, **L2d already proves existence and
uniqueness of one simple** real eigenvalue `E_b(ε) ≠ E_*`
inside the `1/256` point-spectrum window, with a nonzero
natural-domain eigenvector and the certified bound

`|E_b(ε) − E_*| ≤ 2|ε|`.

The original dark eigenspace is exactly one-dimensional.
The **remaining main target**, still not proved, is the quantitative
second-order formula

`|E_b(ε) − E_* − ε/4| ≤ 112 ε²`

and the sign of the moving shift. The moving eigenvector's
external component and nonzero bright amplitude have already
been quantitatively bounded in L3, with constant `256` and the
exact edge-force norm `‖QWF‖²=7/16`. Only the `112` remainder
constant and the shift sign remain proposed targets.
This concerns the actual infinite graph,
not a two-state approximation or time-dependent control protocol.

## 3. Proof milestones, ordered by dependency

**L1 — Exactly one dark direction remains at the original energy.**
For every ε≠0 and every domain vector x, prove
`Hε x = E_* x → ∃ c, x = c • D`.
Pair the original residual `(H₀−E_*)x = −εWx` with the compact
eigenvector a. The original residual pairing is zero by symmetry.
Because W has rank one and its overlap with a is nonzero,
`Wx = 0`. Hence x belongs to the original crossing eigenspace.
The exact representation by a,b and the one-edge formula
force equal coefficients. Two Lean source declarations are added
in `AmmannBeenkerNearCrossingEigenvectors.lean`: the edge-zero lemma
and the dark-only conclusion. **L1 verified** by both PR #88 workflows on commit `464bee37d3477a20f24c3ac48ac116e748fdfd01`.

**L2 — Genuine isolated pair of simple point-spectrum energies (verified).**
Construct complete monotone eigenbases of H₀ and Hε from the
existing generic Lean theorem. Show that the multiplicity-two
crossing occupies *exactly two consecutive positions* in the
baseline spectrum. Norm stability then places both corresponding
perturbed slots within 2|ε| of E*. When 4|ε|<g, all other slots
stay away. L1 ensures that only one of the two slots can equal E*,
so the other corresponds to a new simple bright-derived level.
The new module packages existence of both complete ordered eigenbases
and the explicit 2|ε| indexwise stability bound; both are **Lean verified** on commit `bcc0d2971f5c310743c012935ce3547db021b141` (Action #313).
The exact-double count passed Action #316, and the generic
consecutive-index theorem plus its concrete crossing corollary passed
both the full Lean build and independent Comparator in Action #319
(commit `1f0935439bca41f49d04124cd63ab83d28ae3cf9`).
**L2c is now verified:** `crossing_exists_distinct_perturbed_level_near`
uses `DomainEigenbasis.ordered_levels_unique` to identify the
counting and stability sequences, then dark-only rigidity and
orthonormality to exhibit a *genuine nonzero* perturbed natural-domain
eigenvector at some `E_b ≠ E_*`, with `|E_b − E_*| ≤ 2|ε|`.
It holds for **every ε ≠ 0**, without a smallness assumption.
Both Lean and the independent Comparator passed
[Action #320](https://github.com/alexodas/spectral_geometry/actions/runs/45050640931)
on commit `53075f3fd8af3aef9287b30a8ae0e17f4f3dd5e2`.
L2c by itself is an existence theorem only. **L2d now proves the
remaining small-window conclusions:** for `0 < |ε| ≤ 1/1024`,
`crossing_perturbed_isolated_pair_simple` shows that every
genuine nonzero natural-domain eigenvector of Hε with
`|energy−E_*| ≤ 1/256` has energy `E_*` or the single
distinct energy `E_b`. Each corresponding real eigenspace
is exactly one-dimensional (L1 proves dark simplicity and
L2d proves moving simplicity). The new
`DomainEigenbasis.eigenvalue_occurs` and
`DomainEigenbasis.eigenvector_eq_smul_of_unique_level`
lemmas make completeness and geometric simplicity explicit.
The complete Lean build and independent Comparator passed
[Action #324](https://github.com/alexodas/spectral_geometry/actions/runs/45054460160)
on commit `180f1d8aaf867967805d7f59891249961e8cda22`.
The theorem establishes **point-spectrum** coverage, not a
new standalone assertion about the complex spectrum.

**L3 — External leakage of an actual moving eigenvector (verified).**
Let `x = c F + q`, with x orthogonal to the dark D and q=Qx.
Use the already proved reduced-gap estimate, the fact that the
unperturbed residual is zero on the F direction, and
`W(F)=⟨F,WF⟩F + v`, where `v=QWF`.
For `δ = E_b−E_*` and the L2 interval `|δ|≤2|ε|`, obtain

`(g−|δ|−2|ε|) ‖q‖ ≤ |ε| |c| ‖v‖`.

With `|ε|≤1/1024`, the left coefficient is at least `1/256`,
so `‖q‖ ≤ 256|ε| |c| ‖v‖`. The new theorems
`crossing_moving_eigenvector_sharp_leakage`,
`crossing_moving_eigenvector_bright_nonzero` and
`crossing_exists_moving_bright_sharp_leakage` certify the entire
statement, including `c≠0` and dark orthogonality, in the actual
infinite natural domain. Lean and the independent Comparator passed
Action #328 (commit `0590eb7`); the norm-relative preliminary
bound `‖Qx‖ ≤ 512|ε|‖x‖` passed Action #326.

**L4 — Quadratic spectral error, not merely a Rayleigh quotient (source candidate, CI pending).**
The existing exact bright pairing yields
`(δ−ε/4)c = ε⟨v,q⟩`. Apply Cauchy–Schwarz and L3 to get

`|δ−ε/4| ≤ 256 ε² ‖v‖² = 112 ε²`.

The formula must be attached to the *actual eigenvalue*
constructed in L2; an energy expectation alone is insufficient.

The full L4 candidate is now in
`AmmannBeenkerBrightSpectralSplitting.lean`:
`crossingBright_edge_leakage_inner` identifies the exact
external feedback `⟨QWF,Qx⟩`,
`crossing_abs_inner_le_norm_mul` supplies Cauchy–Schwarz, and
`crossing_moving_energy_quadratic_bound` obtains the proposed
`112ε²` from the already verified L3 norm and
`‖QWF‖²=7/16`. Its existential corollary
`crossing_exists_moving_level_quadratic_bound` attaches this
bound to the *actual unique simple* moving point-spectrum energy.
**This new source candidate is not yet Lean/Comparator verified.**

**L5 — Combine into the final infinite-graph theorem.**
Uniqueness and simplicity in the isolated point-spectrum window
are already L2d conclusions. Establish the sign of the moving
shift, the sharp energy remainder, the full quantitative
eigenvector estimate and all required domain/parameter details.
After full Lean verification, independently assess mathematical
interest before changing any formalization/comparison package.

## 4. Efficient Lean development sequence

1. **L1 green**: the dark-only source declarations are Lean verified.
2. **L2a green**: the ordered-eigenbasis stability and external-edge
   specializations passed Action #313.
3. **L2b fully green**: Action #316 certified exact-double
   multiplicity; Action #319 certified consecutive spectral slots
   with both Lean and the independent Comparator.
4. **L2c fully green**: Action #320 certified the existence of a
   true distinct perturbed natural-domain eigenpair for every
   `ε ≠ 0`, with `|E_b − E_*| ≤ 2|ε|`. The independent
   Comparator also passed.
5. **L2d fully green**: Action #324 certifies
   `crossing_perturbed_isolated_pair_simple` on the actual infinite
   operator for `0 < |ε| ≤ 1/1024`, showing the closed radius
   `1/256` contains precisely two distinct simple
   natural-domain point-spectrum energies, and the moving one is
   within `2|ε|`. A generic complete DomainEigenbasis interface
   establishes eigenvalue coverage and simplicity for unique slots.
   Both the complete Lean and independent Comparator jobs passed.
6. **L3a fully green**: Action #326 (commit `4951e87`)
   verified `crossing_moving_eigenvector_dark_orthogonal`,
   `crossingQubitPart_eq_bright_smul_of_dark_orthogonal`,
   `crossing_moving_eigenvector_bright_nonzero`, and
   `crossing_exists_moving_eigenvector_bright_and_leakage`.
   Thus the genuine moving eigenvector is orthogonal to the
   dark direction, has nonzero bright amplitude, and satisfies
   `‖Qx‖ ≤ 512|ε|‖x‖` for `0<|ε|≤1/1024`.
7. **L3b fully green**: Action #328 verified the exact
   full-operator projected residual, nonexpansiveness of `Q`,
   edge-force decomposition, and the sharp inequality
   `‖Qx‖ ≤ 256|ε||c|‖QWF‖`, with `c=⟨F,x⟩≠0`
   and `‖QWF‖²=7/16`. The full Lean build and independent
   Comparator passed at commit `0590eb7`.
8. **L4–L5 remaining**: perform the quantitative exterior-to-energy
   argument, the `112ε²` spectral remainder and sign, then
   consolidate the final estimates. Dynamic control remains a
   separate downstream research topic.

**Unchanged:** `Challenge.lean`, `Solution.lean`,
`comparator.json`, `palomar/dark-bright/comparator.json`,
`formalization.yaml` and the first registered theorem.
