# Bright spectral splitting — Lean proof roadmap

**Research branch:** `research/bright-spectral-splitting-20261122`
**Scope:** the actual infinite confined Ammann–Beenker graph, the natural onsite domain, the real self-adjoint Hamiltonian and the single selected edge.
**Status:** this is a proof plan. A source lemma is not verified until its GitHub Actions Lean proof check succeeds. No change to existing Palomar files is needed in this phase.

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

For `0 < |ε| ≤ 1/1024`, establish existence of a *unique simple*
bright-derived real eigenvalue `E_b(ε) ≠ E_*`, with a nonzero
natural-domain eigenvector and quantitative bounds

`|E_b(ε) − E_*| ≤ 2|ε|`

`|E_b(ε) − E_* − ε/4| ≤ 112 ε²`.

The dark energy remains fixed and becomes simple, and the moving
eigenvector must be quantitatively close to the original two-mode
plane. The constants are proposed proof targets, not established
results. This is a statement about the infinite graph, not a two-state
approximation or a time-dependent control protocol.

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

**L2 — Moving-level existence using ordered eigenvalues (in progress).**
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
The next L2c source candidate uses `DomainEigenbasis.ordered_levels_unique`
to identify the sequences used for counting and stability, then
uses L1 and orthonormality to exhibit a *genuine nonzero* perturbed
eigenvector with a distinct energy inside the `2|ε|` window.
This new L2c declaration remains unverified until its own CI passes.
Simplicity of the moving level and exhaustion of the small spectral
window remain to be proved separately.

**L3 — External leakage of an actual moving eigenvector.**
Let `x = c F + q`, with x orthogonal to the dark D and q=Qx.
Use the already proved reduced-gap estimate, the fact that the
unperturbed residual is zero on the F direction, and
`W(F)=⟨F,WF⟩F + v`, where `v=QWF`.
For `δ = E_b−E_*` and the L2 interval `|δ|≤2|ε|`, obtain

`(g−|δ|−2|ε|) ‖q‖ ≤ |ε| |c| ‖v‖`.

With `|ε|≤1/1024`, the left coefficient is at least `1/256`,
so `‖q‖ ≤ 256|ε| |c| ‖v‖`. Prove c≠0 for x≠0.

**L4 — Quadratic spectral error, not merely a Rayleigh quotient.**
The existing exact bright pairing yields
`(δ−ε/4)c = ε⟨v,q⟩`. Apply Cauchy–Schwarz and L3 to get

`|δ−ε/4| ≤ 256 ε² ‖v‖² = 112 ε²`.

The formula must be attached to the *actual eigenvalue*
constructed in L2; an energy expectation alone is insufficient.

**L5 — Combine into the final infinite-graph theorem.**
Establish the sign of the moving shift, uniqueness and
simplicity in the isolated window, the exact domain and
parameter hypotheses, and the quantitative eigenvector estimate.
After full Lean verification, independently assess mathematical
interest before changing any formalization/comparison package.

## 4. Efficient Lean development sequence

1. **L1 green**: the dark-only source declarations are Lean verified.
2. **L2a green**: the ordered-eigenbasis stability and external-edge
   specializations passed Action #313.
3. **L2b fully green**: Action #316 certified exact-double
   multiplicity, and Action #319 certified consecutive spectral slots
   with both Lean and the independent Comparator.
4. **L2c source candidate**: a true distinct perturbed level and
   eigenvector, with the `2|ε|` bound, are being submitted for CI.
   Do not call L2c verified before its own run is green.
5. After L2c verification, prove window uniqueness/simplicity and
   perform the L3–L4 algebra and domain checks; save the more
   speculative dynamical-control questions for later.

**Unchanged:** `Challenge.lean`, `Solution.lean`,
`comparator.json`, `palomar/dark-bright/comparator.json`,
`formalization.yaml` and the first registered theorem.
