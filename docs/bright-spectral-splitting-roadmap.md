# Dark–bright spectral splitting and control — Lean research roadmap

**Relationship to the original program.** This is the **specialized
localized-modes/control roadmap** (Track B). The repo's original
spectral-geometry and analytic-zero program (Track A) remains active,
with its verified canonical-product results and open relative
determinant, cofactor, finite-patch and zero-statistics objectives
in the [main README §6](../README.md#6-roadmap-proof-status-and-next-steps).
L7's priority is **operational**, not a withdrawal of those goals.
The original single-edge proposal is retained below as L6 and in
the [historical L6 note](edge-control-reachability.md).

**Active research branch:** `research/l7-exact-leakage-free-control` (branched from the verified `main` commit `7b68540619ab45e5233b2d5ec8273829b3fbba77`).
**Historical L1–L5 branch:** `research/bright-spectral-splitting-20261122`.
**Scope:** the actual infinite confined Ammann–Beenker cut-and-project vertex graph and natural-domain Hamiltonian; control statements will require a separate complex quantum-dynamics formalization.

**Current priority: L7c, complex evolution and exact zero-leakage preparation.** L7a is complete: the coordinated eight-edge correction and first-ring detuning preserve the original natural-domain plane exactly. L7b is complete at the algebraic level: the exact dark/bright effective matrix, Pauli commutators, full real su(2) generation and constructive Z–X–Z state reachability from dark are Lean-verified ([README §§4.100–4.101](../README.md#4101-full-lie-generation-and-constructive-two-state-rotations)). Independent signed real control coefficients are explicit. The remaining task is to identify those rotations with the complex full-graph evolution and prove exact zero leakage at every time. L6 remains preserved.

**Established foundation:** **L1–L5 are Lean/Comparator verified** for the full infinite graph. The single-edge perturbation has a fixed simple dark level, one unique simple moving real point-spectrum level in the closed radius-`1/256` window for `0<|ε|≤1/1024`, `‖Qx‖≤256|ε||c|‖QWF‖` with `‖QWF‖²=7/16`, and `|E_b-(E_*+ε/4)|≤112ε²` with a strict signed shift. The consolidated L5 theorem now also explicitly states and proves the **nonzero fixed dark eigenvector and its full-domain eigenvalue equation** (Palomar feedback fix in PR #89; full Lean and independent Comparator passed [Action #340](https://github.com/alexodas/spectral_geometry/actions/runs/45142702987)). This is **not** a proof of general quantum dynamics, L6 reachability or time-dependent L7 zero-leakage controllability.

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

## 2. Quantitative real point-spectrum splitting: L1–L5 verified

For `0 < |ε| ≤ 1/1024`, **L2d already proves existence and
uniqueness of one simple** real eigenvalue `E_b(ε) ≠ E_*`
inside the `1/256` point-spectrum window, with a nonzero
natural-domain eigenvector and the certified bound

`|E_b(ε) − E_*| ≤ 2|ε|`.

The original dark eigenspace is exactly one-dimensional.
The **second-order formula is now verified in L4**:

`|E_b(ε) − E_* − ε/4| ≤ 112 ε²`.

The moving eigenvector's exterior component and nonzero
bright amplitude were previously bounded in L3, with constant
`256` and exact edge-force norm `‖QWF‖²=7/16`.
The final L5 theorems now additionally prove that
`ε>0 → E_b>E_*` and `ε<0 → E_b<E_*`, and consolidate
fixed dark simplicity, moving-level uniqueness and simplicity,
genuine natural-domain eigenpairs, bright amplitude,
sharp exterior leakage and the `112ε²` energy remainder
under the same hypotheses. This concerns the actual infinite
graph's real point spectrum, not a two-state approximation,
independent complex-spectrum theorem or time-dependent
control protocol.

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

**L4 — Quadratic spectral error for the actual moving eigenvalue (verified).**
The existing exact bright pairing yields
`(δ−ε/4)c = ε⟨v,q⟩`. Apply Cauchy–Schwarz and L3 to get

`|δ−ε/4| ≤ 256 ε² ‖v‖² = 112 ε²`.

The formula must be attached to the *actual eigenvalue*
constructed in L2; an energy expectation alone is insufficient.

The full verified L4 result is in
`AmmannBeenkerBrightSpectralSplitting.lean`:
`crossingBright_edge_leakage_inner` identifies the exact
external feedback `⟨QWF,Qx⟩`,
`crossing_abs_inner_le_norm_mul` applies Cauchy–Schwarz, and
`crossing_moving_energy_quadratic_bound` proves the explicit
`112ε²` using the verified L3 estimate and
`‖QWF‖²=7/16`. Its existential corollary
`crossing_exists_moving_level_quadratic_bound` attaches this
bound to the true unique simple moving point-spectrum energy.
Both the complete Lean build and independent Comparator passed
[Action #331](https://github.com/alexodas/spectral_geometry/actions/runs/45059362269)
at commit `e03f7cfc88b933fe9c2a635d33016927e6d64709`.

**L5 — Strict signed shift and final full-domain theorem (verified).**
Theorem `crossing_moving_energy_shift_sign` derives a strict
upward shift for positive ε and downward shift for negative ε:
`112ε² ≤ (7/64)|ε| < |ε|/4` under the already verified
parameter bounds. The theorem
`crossing_final_signed_bright_spectral_splitting`
packages a genuine nonzero eigenvector at the one moving
energy, the `2|ε|` and `112ε²` energy bounds, the
strict shift sign, exact dark orthogonality and nonzero bright
amplitude, the projected equality `x=cF+Qx`, the sharp
full-exterior leakage bound, exhaustive two-level real point
spectrum in the closed `1/256` window, and simple dark
and moving eigenspaces. The exact common hypotheses are
`ε≠0`, `|ε|≤1/1024` and the original infinite
natural domain. Both full Lean and independent Comparator
passed [Action #333](https://github.com/alexodas/spectral_geometry/actions/runs/45060461341)
on source commit `fbd2503d33280d7d0c2fe5306ea2739806628b20`.
Independent research-interest assessment and the distinct
complex-dynamics or spectral-product programs remain open;
none is claimed in this theorem. No comparison package changed.

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
8. **L4 fully green**: the exact external feedback identity,
   real Cauchy–Schwarz argument and quantitative `112ε²`
   spectral-level estimate passed complete Lean and Comparator
   CI in Action #331.
9. **L5 fully green**: Action #333 certifies
   `crossing_moving_energy_shift_sign` and
   `crossing_final_signed_bright_spectral_splitting`,
   combining sign, complete isolated real point-spectrum
   count, simplicity, sharp energy law and full-exterior
   eigenvector control on the original natural domain.
   Both full Lean and the independent Comparator passed.
10. **New priority: L7a (open)**: construct and verify the eight-edge
    operator preserving the original dark–bright plane exactly.
    L7b–L7c, physical reachability and complex propagation remain open.
    **Original L6** (single-edge controlled small leakage), independent
    novelty assessment and analytic-product research are retained
    for future work; none follows automatically from L5.

## 5. L5 Palomar candidate, editorial feedback and correction

The newly selected scientific result is the single consolidated
`crossing_final_signed_bright_spectral_splitting` theorem (§4.97),
not the earlier generator-response conclusion (§4.92).
The active Mathlib-only `Challenge.lean` and
`Solution.lean` now state and prove that exact selected
theorem, with the six necessary concrete-model witnesses.

The active Comparator is kept **per theorem** at
[`palomar/signed-bright-splitting/comparator.json`](../palomar/signed-bright-splitting/comparator.json).
The previous **unsubmitted** generator-response candidate
is archived under [`palomar/dark-bright/`](../palomar/dark-bright/)
with its original Comparator and snapshots of its Challenge and
Solution. The redundant root `comparator.json` was deleted;
the static checks, comparator runner, diagnosis script and
CI workflow now use the dedicated active configuration.

The project description in [`formalization.yaml`](../formalization.yaml)
states the theorem in plain English: one simple energy remains
fixed while exactly one other simple energy moves in the direction
of a small one-edge change, with explicit bounds for its value
and its wave pattern. It does not contain workflow,
pull-request or commit details.

The original candidate package passed the complete Lean build,
static checks and independent Comparator in
[Action #335](https://github.com/alexodas/spectral_geometry/actions/runs/45063053611).
The external L5 submission pinned to commit
`4c2633d6c8ee6e32b163bc4d27483a31f7c50aae` passed
mechanical verification and Challenge renderability, but the
**automated editorial review requested a correction**: the selected
theorem had proved the uniqueness of the fixed dark eigendirection,
without explicitly asserting the existence of its nonzero eigenvector.
The moving bright eigenvector had already been explicitly proved nonzero.

[PR #89](https://github.com/alexodas/spectral_geometry/pull/89)
strengthened the selected L5 theorem and the Mathlib-only Challenge with
both `crossingDark ≠ 0` and the exact full-domain equation
`Hε domainCrossingDark = E_* • crossingDark`, using existing source
lemmas. The full Lean build, static package checks and independent
Comparator all passed
[Action #340](https://github.com/alexodas/spectral_geometry/actions/runs/45142702987);
the PR was merged into `main` at
`7b68540619ab45e5233b2d5ec8273829b3fbba77`.
The Comparator selection remains
`palomar/signed-bright-splitting/comparator.json`.
**A new Palomar editorial acceptance or registration has not been
established by these GitHub checks.** Any resubmission must use the
new commit, not the earlier reviewed one.

**Protected historical registration:** the separate first Palomar record
`PALOMAR-2026-11-06-000012` remains unchanged.



## 6. Active next theorem: L7 — exact two-mode control without leakage (OPEN)

**Motivation.** The single selected edge `W` has
`‖Q W F‖² = 7/16 > 0`: it does not preserve the original
two-dimensional dark–bright subspace. Instead of requiring a small
leakage estimate for an arbitrarily long pulse, seek a *different,
coordinated local graph perturbation* that preserves that plane
**exactly**, at any pulse strength.

Let `a = compactA`, `b = compactB`,
`D = (a+b)/4`, `F = (a-b)/4`,
`P` be the orthogonal projection onto `span{D,F}`, and `Q = I-P`.
The two compact modes each have eight alternating signed amplitudes
on distinct, neighboring concentric rings.

**Coordinated control (verified):** pair the eight sites of the
first ring with corresponding adjacent sites of the second ring,
and let `M` be the sum of their eight equal-weight graph-edge
Laplacians (rank-one edge operators). Membership, adjacency, distinctness,
endpoint disjointness and matching signed amplitudes are Lean-verified,
not assumed from a drawing. The verified identities are

```text
M a = a - b
M b = b - a
M D = 0
M F = 2 F
Q M P = 0
```

All five equations are Lean-verified. The bounded symmetric operator is a
*finite sum of genuine local edge changes*, not an artificially imposed
qubit projector. The complete controlled Hamiltonian preserves the original
two-mode plane and maps it into the natural domain at arbitrary real control
strengths.

### L7a — exact invariant-plane algebra (COMPLETE)

- [x] Construct eight genuine distinct adjacent pairs with disjoint endpoints.
- [x] Define the bounded symmetric sum of rank-one edge corrections.
- [x] Verify matching amplitudes and exact full-space action on both modes.
- [x] Deduce the dark and bright identities and `Q M P=0`.
- [x] Establish the natural-domain action and plane invariance of both controls.
- [x] Complete full Lean verification; L7a is not separately selected by Palomar.

**Meaning of zero leakage:** `Q ψ = 0` means *no component orthogonal
to the two compact modes*, not merely no amplitude outside the central
rings. Static invariance is necessary but not yet a full time-dependent
quantum theorem.

### L7b — exact effective controls and reachability algebra (COMPLETE ALGEBRAICALLY)

- [x] Express the full-operator restriction as `(E_*+δ/2+η) I + (δ/2) σ_x - η σ_z`.
- [x] Prove noncommutation and the three complex matrix commutators.
- [x] Prove the real traceless skew-Hermitian matrix space is exactly
      the smallest real commutator-closed subspace containing the controls.
- [x] Construct three rotation angles reaching every normalized complex
      pair from dark, with the middle half-angle in [0, π/2].
- [x] Show the signed real generator coefficients can be set independently:
      `G(-2t,0)=tX`, `G(0,t)=tZ`. This uses ideal independently tunable
      arbitrary real control strengths, not a hardware or edge-positivity constraint.

These are finite-dimensional matrix results, not a proof of the
infinite-system time evolution or arbitrary initial-state propagator.

### L7c — exact complex quantum evolution (CURRENT PRIORITY, OPEN)

- [ ] Construct the complex Hilbert-space model and the relevant
      self-adjoint dynamics/propagators on the full infinite graph
      (including domain conditions and pulse composition).
- [ ] Show every composed pulse starting in `P` remains in `P`
      at **every time**: `‖Q ψ(t)‖ = 0`, rather than merely at
      switch-off or at a final measurement.
- [ ] Prove the resulting sequence reaches an arbitrary normalized
      target in `span{D,F}` up to global phase, under the stated
      control assumptions; distinguish mathematical reachability
      from experimental ability to tune eight edges simultaneously.
- [ ] Optional later question: determine whether fewer than eight
      edges can realize a nontrivial exact phase control. **No
      minimality claim is made yet.**

**L7 completion criterion:** an explicit, physically local finite-edge
control with kernel-checked full-operator invariance **and** a
quantum-dynamical arbitrary-target theorem with exact zero leakage
for every time of the protocol. L7a alone is a useful intermediate
lemma but not this complete controllability result.

## 7. Preserved original direction: L6 — single-edge approximate control (DEFERRED, NOT CANCELLED)

The original program used the one selected graph edge `W` and the
ring parameter `t` to change amplitudes and relative phases while
accepting a quantitative but small `Q`-component. It remains
scientifically distinct from L7: the **single-edge actuator** is
simpler, but `Q W F ≠ 0` excludes exact invariance of the original
two-mode plane for this control.

**Already verified ingredients (not a completed L6):**
`‖QWF‖² = 7/16`; the isolated real point-spectrum pair and L5
eigenvector bounds; exact `t`-detuning action on the compact plane;
the real-space qubit/leakage decomposition; and duration-independent
`512|ε|` leakage estimates **conditional on supplied norm-preserving,
domain-preserving evolutions that intertwine the fixed edge Hamiltonian**.
The actual general complex Schrödinger propagator and arbitrary-target
single-edge protocol are not proved by those conditional statements.

**Future L6 proof goals:**

- [ ] Construct the full complex unitary dynamics and switch-on/off
      sequences for the original one-edge perturbation.
- [ ] Give a precise target-state preparation theorem with controlled
      phases and amplitudes, stated in a norm or fidelity metric and
      with explicit pulse-strength/length dependence.
- [ ] Prove the leakage/error budget for the complete finite pulse
      sequence, including any residual state after restoring the
      unperturbed Hamiltonian.
- [ ] Compare L6 versus L7: number of independently changed edges,
      admissible control strengths, pulse cost and leakage. Neither
      exact controllability for L6 nor an optimality assertion for L7
      is presently established.

**Priority decision:** implement **L7a first** because exact finite-edge
invariance may reduce the dynamical problem to the rigorously closed
two-mode plane. Keep **L6 as the original future path** for a
less demanding, physically more economical single-edge control.
Existing L6 research and
[the edge-control reachability note](edge-control-reachability.md)
are preserved; no earlier research conclusions are withdrawn.
