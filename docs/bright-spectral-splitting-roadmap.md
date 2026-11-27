# Dark–bright spectral splitting and control — Lean research roadmap

**Relationship to the original program.** This is the **specialized
localized-modes/control roadmap** (Track B). The repo's original
spectral-geometry and analytic-zero program (Track A) is temporarily paused,
with its verified canonical-product results and open relative
determinant, cofactor, finite-patch and zero-statistics objectives
in the [main README §6](research-roadmap.md#6-roadmap-proof-status-and-next-steps).
Following the registered L7 and L8a results, exact variable-duration preparation with prescribed energetic protection is Lean-verified (§4.111); all 19 selected propositions passed independent comparison. Registered on 27 November 2026 as [PALOMAR-2026-11-27-000003 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-27-000003&version=1). Palomar mechanical verification and Challenge renderability passed, and the automated editorial review identified no blocking problem. This does not withdraw the earlier goals.
**Current priority:** [L9 — independently controllable spectrally protected
localized qubits](multi-qubit-roadmap.md). L6 and imperfect-control
refinements L8b–L8e remain open but are deferred. L9.1 is now registered ([PALOMAR-2026-11-27-000042 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-27-000042&version=1)): the bounded plateau has an exact double eigenvalue and a full real spectral gap of at least 1/122, with a finite-rank defect relative to the uniform bulk (§4.112). L9.2 recurrence is the next task.
The original single-edge proposal is retained below as L6 and in
the [historical L6 note](edge-control-reachability.md).

**Scope:** the actual infinite confined Ammann–Beenker cut-and-project vertex graph and natural-domain Hamiltonian. The coordinated-control theorems construct exact trajectories in the original localized plane using real and imaginary full-domain vectors; a general complex full-space propagator remains open.

**L7 central objective verified: exact normalized target preparation from dark.** L7a, L7b and L7c.1–4 are Lean-verified. The three unit-duration pulses with strengths (δ,η)=(0,p),(-2t,0),(0,q) reach every normalized complex dark/bright pair from dark up to the explicit phase exp(i(-3E_*+t-p-q)), with continuous full-graph components, natural-domain membership, conserved unit squared complex norm, zero leakage at every time and exact Schrödinger equations on each open interval ([README §4.105](coordinated-quantum-control.md#4105-exact-arbitrary-target-preparation-from-dark-without-leakage)). The general complex full-space propagator and stronger control results remain separate. The independent [third package](../palomar/exact-leakage-free-preparation/) passed full Lean and Comparator verification with the bundled kernels, Palomar mechanical and renderability checks, and automated editorial review with no blocking problem. Registered on 25 November 2026 as [PALOMAR-2026-11-25-000001 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-25-000001&version=1). L6 and Track A are preserved.

**Established foundation:** **L1–L5 are Lean/Comparator verified** for the full infinite graph. The single-edge perturbation has a fixed simple dark level, one unique simple moving real point-spectrum level in the closed radius-`1/256` window for `0<|ε|≤1/1024`, `‖Qx‖≤256|ε||c|‖QWF‖` with `‖QWF‖²=7/16`, and `|E_b-(E_*+ε/4)|≤112ε²` with a strict signed shift. The consolidated L5 theorem now also explicitly states and proves the **nonzero fixed dark eigenvector and its full-domain eigenvalue equation** (full Lean and independent Comparator verification passed after the strengthened statement). This L5 statement is **not** a proof of general quantum dynamics or L6 reachability; the distinct L7 zero-leakage preparation theorem is now proved by the coordinated controls below.

**Registered L8a result — quantitative spectral protection during coordinated control.** L8a.1 is Lean-verified: exact control norms and bounded perturbation decomposition ([README §4.106](coordinated-quantum-control.md#4106-sharp-coordinated-control-norms-and-exact-bounded-perturbation)). L8a.2 is Lean-verified: exact controlled plane levels and natural-domain reducing projections ([README §4.107](coordinated-quantum-control.md#4107-exact-controlled-plane-energies-and-natural-domain-reduction)). L8a.3 is Lean-verified: quantitative exterior exclusion and complete real-spectrum characterization ([README §4.108](coordinated-quantum-control.md#4108-quantitative-exclusion-of-exterior-real-spectral-levels)). L8a.4 is Lean-verified: explicit positive cluster isolation in the complete real spectrum ([README §4.109](coordinated-quantum-control.md#4109-consolidated-quantitative-isolation-of-the-controlled-cluster)). The central L8a objective and centered refinement are complete ([README §4.110](coordinated-quantum-control.md#4110-spectral-protection-during-coordinated-control)); separate independent comparison passed and the result was registered on 26 November 2026 as [PALOMAR-2026-11-26-000015 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000015&version=1). Further refinements remain open. See §8 below and [README §6.9](research-roadmap.md#69-l8a--quantitative-spectral-protection-under-coordinated-controls-open).

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
and the dark-only conclusion. **L1 verified** in Lean.

**L2 — Genuine isolated pair of simple point-spectrum energies (verified).**
Construct complete monotone eigenbases of H₀ and Hε from the
existing generic Lean theorem. Show that the multiplicity-two
crossing occupies *exactly two consecutive positions* in the
baseline spectrum. Norm stability then places both corresponding
perturbed slots within 2|ε| of E*. When 4|ε|<g, all other slots
stay away. L1 ensures that only one of the two slots can equal E*,
so the other corresponds to a new simple bright-derived level.
The new module packages existence of both complete ordered eigenbases
and the explicit 2|ε| indexwise stability bound; both are **Lean verified**. The exact-double count, generic consecutive-index theorem and concrete crossing corollary are Lean-verified.
**L2c is now verified:** `crossing_exists_distinct_perturbed_level_near`
uses `DomainEigenbasis.ordered_levels_unique` to identify the
counting and stability sequences, then dark-only rigidity and
orthonormality to exhibit a *genuine nonzero* perturbed natural-domain
eigenvector at some `E_b ≠ E_*`, with `|E_b − E_*| ≤ 2|ε|`.
It holds for **every ε ≠ 0**, without a smallness assumption.
The substantive Lean proof passed verification.
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
The substantive Lean proof passed verification.
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
infinite natural domain. The sharp result and the preliminary norm-relative bound `‖Qx‖ ≤ 512|ε|‖x‖` are Lean-verified.

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
The substantive Lean proof passed verification.

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
natural domain. The substantive Lean proof passed verification.
Independent research-interest assessment and the distinct
complex-dynamics or spectral-product programs remain open;
none is claimed in this theorem.

## 4. Efficient Lean development sequence

1. **L1 green**: the dark-only source declarations are Lean verified.
2. **L2a green**: the ordered-eigenbasis stability and external-edge
   specializations are Lean-verified.
3. **L2b verified**: exact-double multiplicity and consecutive spectral slots are Lean-verified.
4. **L2c verified**: Lean proves the existence of a
   true distinct perturbed natural-domain eigenpair for every
   `ε ≠ 0`, with `|E_b − E_*| ≤ 2|ε|`. The independent
   Comparator also passed.
5. **L2d verified**: Lean proves
   `crossing_perturbed_isolated_pair_simple` on the actual infinite
   operator for `0 < |ε| ≤ 1/1024`, showing the closed radius
   `1/256` contains precisely two distinct simple
   natural-domain point-spectrum energies, and the moving one is
   within `2|ε|`. A generic complete DomainEigenbasis interface
   establishes eigenvalue coverage and simplicity for unique slots.
   Both the complete Lean and independent Comparator jobs passed.
6. **L3a verified**: Lean proves `crossing_moving_eigenvector_dark_orthogonal`,
   `crossingQubitPart_eq_bright_smul_of_dark_orthogonal`,
   `crossing_moving_eigenvector_bright_nonzero`, and
   `crossing_exists_moving_eigenvector_bright_and_leakage`.
   Thus the genuine moving eigenvector is orthogonal to the
   dark direction, has nonzero bright amplitude, and satisfies
   `‖Qx‖ ≤ 512|ε|‖x‖` for `0<|ε|≤1/1024`.
7. **L3b verified**: Lean proves the exact
   full-operator projected residual, nonexpansiveness of `Q`,
   edge-force decomposition, and the sharp inequality
   `‖Qx‖ ≤ 256|ε||c|‖QWF‖`, with `c=⟨F,x⟩≠0`
   and `‖QWF‖²=7/16`.
8. **L4 fully green**: the exact external feedback identity,
   real Cauchy–Schwarz argument and quantitative `112ε²`
   spectral-level estimate are Lean-verified.
9. **L5 verified**: Lean proves
   `crossing_moving_energy_shift_sign` and
   `crossing_final_signed_bright_spectral_splitting`,
   combining sign, complete isolated real point-spectrum
   count, simplicity, sharp energy law and full-exterior
   eigenvector control on the original natural domain.
   The final L5 package also passed independent comparison.
10. **L7a–L7c.4 (verified)**: construct and verify the eight-edge
    operator preserving the original dark–bright plane exactly, the
    Lie algebra and the continuous three-pulse preparation theorem.
    General complex propagation remains open.
    **Original L6** (single-edge controlled small leakage), independent
    novelty assessment and analytic-product research are retained
    for future work; none follows automatically from L5.

## 5. L5 Palomar candidate, editorial feedback and correction

The registered L5 scientific result is the consolidated
`crossing_final_signed_bright_spectral_splitting` theorem (§4.97),
not the earlier generator-response conclusion (§4.92).
Its Mathlib-only [Challenge](../palomar/signed-bright-splitting/Challenge.lean),
[Solution](../palomar/signed-bright-splitting/Solution.lean),
[Comparator](../palomar/signed-bright-splitting/comparator.json) and
[metadata](../palomar/signed-bright-splitting/formalization.yaml)
are preserved together, with six concrete-model witnesses and one
scientific conclusion. The earlier unsubmitted generator-response
package is archived in [palomar/dark-bright](../palomar/dark-bright/).
Each Comparator remains in its own directory; the active root files
now describe the fifth registered result (§4.111).

The L5 metadata explains the fixed simple energy and the unique
moving simple energy, with explicit energy and wave-pattern bounds.
Automated editorial review of the earlier L5 candidate requested
explicit existence of the nonzero fixed dark eigenvector, in addition
to uniqueness of its eigendirection. The strengthened statement adds
both `crossingDark ≠ 0` and the exact full-domain equation
`Hε domainCrossingDark = E_* • crossingDark`. The corrected substantive
proof and independent candidate passed Lean, static packaging and
Comparator verification.

**Historical verification boundary:** local verification alone did not establish Palomar registration. The corrected L5 result was subsequently registered on 23 November 2026 as [PALOMAR-2026-11-23-000017 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-23-000017&version=1).

**Protected historical registration:** the separate first Palomar record
`PALOMAR-2026-11-06-000012` remains unchanged.



<a id="6-active-next-theorem-l7--exact-two-mode-control-without-leakage-open"></a>

## 6. L7 — exact two-mode preparation without leakage (VERIFIED)

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
- [x] Complete full Lean verification; three locality statements are selected alongside the final L7 preparation theorem in the independently verified registered package.

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

### L7c — exact complex compact-plane preparation (VERIFIED)

- [x] **L7c.1:** Construct exact full natural-domain single-axis trajectories
      in real/imaginary components for arbitrary complex amplitudes.
      Verify the Schrödinger derivative equations, conservation of the
      squared complex norm and zero leakage of both components for every
      real time. Prove the combined real Hamiltonian self-adjoint for
      arbitrary real control strengths.
- [x] **L7c.2:** Identify both single-axis trajectories with the exact
      rotation matrices of L7b, including common scalar phases; certify
      their identity at zero time and compatibility with composition.
- [x] **L7c.3:** Compose the three pulses with matching endpoint states,
      continuous full-space components, piecewise full-domain Schrödinger
      equations, conserved squared complex norm, natural-domain membership
      and zero leakage at every time, including the switches.
- [x] **L7c.4:** Prove arbitrary normalized target preparation from dark
      up to the explicit global phase, with exact zero leakage throughout,
      under independently tunable signed real controls. The bundled
      theorem is coordinatedProtocol_exact_preparation.
- [ ] Construct the general complex Hilbert-space model and unitary
      full-space propagators; distinguish the explicit plane trajectories
      from evolution for arbitrary infinite-space initial data.
- [ ] Optional later question: determine whether fewer than eight edges
      can realize a nontrivial exact phase control. No minimality claim
      is made yet.

**L7 completion criterion:** an explicit, physically local finite-edge
control with kernel-checked full-operator invariance **and** a
quantum-dynamical arbitrary-target theorem with exact zero leakage
for every time of the protocol. This criterion is now met by L7a–L7c.4
for preparation from dark in the real/imaginary representation.
It does not assert a general complex unitary group, preparation from
arbitrary initial states as a separate theorem, or experimental feasibility.

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

**Research decision and outcome:** L7a was prioritized because exact finite-edge
invariance reduces the dynamical problem to the rigorously closed two-mode
plane. L7c.4 now establishes the intended preparation theorem. Keep **L6 as
the original future path** for a potentially more economical single-edge control.
Existing L6 research and
[the edge-control reachability note](edge-control-reachability.md)
are preserved; no earlier research conclusions are withdrawn.

## 8. L8 — robustness of the embedded qubit (OPEN)

### L8a — Quantitative spectral protection under coordinated controls (VERIFIED; refinements open)

**Central static objective and centered refinement verified; further refinements open.** L7 proves that the
two localized modes can be manipulated without any leakage when both
controls are applied exactly as prescribed. That protection is
geometric: the two-mode plane is invariant even for large signed
control strengths. It does not by itself show that the two controlled
energy levels remain separated from the rest of the spectrum.
L8 begins by asking how much energetic protection survives while the
controls are active. This is a prerequisite for investigating the
effect of imperfections, not a proof of robustness against noise.

**Verified starting point.** At zero control strengths, the complete
real bounded-inverse spectrum has no other point in the closed
radius-`g = 1/128` window about `E_*` (README §4.79). The original dark/bright
plane `P` and its orthogonal complement `Q = I - P` reduce the ideal
controlled Hamiltonian by exact invariance and symmetry
(README §§4.99–4.102 and §4.107, which verifies the domain lifts and
commutation identities). The two plane eigenvalues are now characterized
exactly in Lean:

```math
\lambda_\pm(\delta,\eta)
= E_*+\delta/2+\eta\ \pm\sqrt{\delta^2/4+\eta^2}.
```

**L8a.1 — verified sharp control norms and bounded decomposition.**
The new definition and seven theorems in
[AmmannBeenkerCoordinatedInvariantPlane.lean](../SpectralGeometry/AmmannBeenkerCoordinatedInvariantPlane.lean)
prove the following on the complete real square-summable space and, for
Hamiltonian identities, on the unchanged natural domain. The disjoint
matched endpoints give `M²x = 2Mx` for every vector `x`; symmetry then
gives `‖M‖ ≤ 2`, and the existing nonzero bright eigenvector attains it.
The first-ring coordinate projection is a contraction attaining norm one
on the nonzero compact mode A. Thus `‖R‖ = 1` and `‖M‖ = 2` exactly.
The change from the zero-control Hamiltonian is exactly the bounded map
`B = δ R + η M`, with `‖B‖ ≤ ρ = |δ| + 2|η|` for every signed real δ, η.

The declarations are `coordinatedRingControl_sq_apply`,
`coordinatedRingControl_norm_le_two`, `coordinatedRingControl_opNorm`,
`coordinatedOnsiteProjection_opNorm`, `coordinatedControlPerturbation`,
`coordinatedControlCorrection_decomposition`,
`coordinatedControlHamiltonian_decomposition`, and
`coordinatedControlPerturbation_norm_le`. Full Lean verification, static
checks and the existing independent L7 Comparator passed. The new L8a.1
statements are not independently selected in that registered package.
No new module or Palomar package was introduced. See [README §4.106](coordinated-quantum-control.md#4106-sharp-coordinated-control-norms-and-exact-bounded-perturbation).

**L8a.2 — verified controlled plane energies and natural-domain reduction.**
The full natural-domain equation with a nonzero input and zero leakage
holds at energy e if and only if e equals one of the two displayed roots.
The constructive proof uses the traceless A/B matrix with entries
a = δ/2 and b = −η, and z = e − (E_* + δ/2 + η). Its scalar eigenvector
equations have a nonzero solution exactly when z² = a²+b². If b ≠ 0,
the pair (b,z−a) works; if b=0 a coordinate vector works. Compact
coefficient extraction establishes nonvanishing in the full Hilbert
space. The radius vanishes iff both controls vanish. The explicit lifts
of P and Q preserve the natural domain, and both projections commute
with the full controlled Hamiltonian on that domain.

The new definitions and theorems are in
[AmmannBeenkerCoordinatedAxisDynamics.lean](../SpectralGeometry/AmmannBeenkerCoordinatedAxisDynamics.lean):
`coordinatedLevelCenter`, `coordinatedLevelRadius`,
`coordinatedLevelRadius_sq`, `coordinatedLevelRadius_eq_zero_iff`,
`coordinatedCompact_eigen_iff`, `coordinatedPlane_eigenvalue_iff`,
`coordinatedPlaneDomainPart`, `coordinatedComplementDomainPart`,
their two `_coe` theorems, and
`coordinatedHamiltonian_plane_commutes`,
`coordinatedHamiltonian_complement_commutes`,
`coordinatedHamiltonian_complement_invariant`. Full Lean verification
and the existing independent L7 Comparator passed. L8a.2 is not a new
Palomar selection. No global simplicity is asserted by L8a.2 alone; L8a.3 below now
provides quantitative exterior exclusion. See [README §4.107](coordinated-quantum-control.md#4107-exact-controlled-plane-energies-and-natural-domain-reduction).

**L8a.3 — verified quantitative exterior exclusion in the full real spectrum.**
With g = 1/128 and ρ = |δ| + 2|η|, every exterior natural-domain vector
x satisfies (g−ρ−|e−E_*|)‖x‖ ≤ ‖Hx−ex‖, for every real e.
This follows from the baseline reduced-gap estimate, the exact
perturbation decomposition and the triangle inequality. Any eigenvector
with nonzero leakage yields an exterior eigenvector at the same energy
by the reducing projection of L8a.2, hence satisfies g ≤ ρ+|e−E_*|.
Properness and the lower bound of the concrete onsite potential supply
the compact shift for the controlled operator at every real δ, η.
The complete real bounded-inverse spectrum is therefore characterized
by genuine full-domain eigenvectors. In the open window
ρ+|e−E_*|<g, every eigenvector has zero leakage and real-spectrum
membership is equivalent to e being one of the two explicit plane levels.

The seven new theorems in
[AmmannBeenkerCoordinatedAxisDynamics.lean](../SpectralGeometry/AmmannBeenkerCoordinatedAxisDynamics.lean)
are `coordinatedControlPerturbation_apply_norm_le`,
`coordinatedComplement_residual_lower`,
`coordinatedComplement_eigenvalue_distance`,
`coordinatedEigenvector_complement_distance`,
`coordinatedRealSpectrum_iff_full_eigenvector`,
`coordinatedEigenvector_leakage_zero_of_near`, and
`coordinatedRealSpectrum_near_iff`.
Full Lean verification, static checks and the existing independent L7
Comparator passed. These are not independently selected Palomar
statements. See [README §4.108](coordinated-quantum-control.md#4108-quantitative-exclusion-of-exterior-real-spectral-levels).

**L8a.4 — verified consolidated quantitative cluster isolation.** A conservative lower bound on the
separation between the controlled two-mode spectral cluster and
the spectrum on the orthogonal complement is

```math
g_{\rm protected}(\delta,\eta)\ \ge\ g-2\rho
\qquad\text{when }2\rho<g.
```

This is now a Lean-certified sufficient bound: for ρ < 1/256, both
plane levels are genuine real spectral points, the closed radius-ρ
window contains precisely those levels, every eigenvector at either
level has zero leakage, and all other real spectral energies (and
energies of eigenvectors with nonzero leakage) are at distance at least
1/128−2ρ > 0 from either plane level. Zero controls are included.
The shift estimate follows by applying the bounded perturbation to
a nonzero plane eigenvector, since the baseline Hamiltonian acts
there as E_* times the identity.

The new definition and seven theorems in
[AmmannBeenkerCoordinatedAxisDynamics.lean](../SpectralGeometry/AmmannBeenkerCoordinatedAxisDynamics.lean)
are `CoordinatedPlaneLevel`, `coordinatedPlaneLevel_shift_le`,
`coordinatedPlaneLevel_mem_realSpectrum`,
`coordinatedPlaneLevel_complement_residual_lower`,
`coordinatedPlaneLevel_exterior_distance`,
`coordinatedPlaneLevel_otherRealSpectrum_distance`,
`coordinatedPlaneLevel_in_protected_window`, and
`coordinatedCluster_isolation`. Full Lean verification, static checks
and the existing L7 Comparator passed. See [README §4.109](coordinated-quantum-control.md#4109-consolidated-quantitative-isolation-of-the-controlled-cluster).
This is not a new independent Palomar selection. The distance concerns the two-mode cluster versus the
exterior spectrum, not the spacing between its two levels, which
may coincide. The centered refinement below improves this estimate.
Do not infer loss of protection when a sufficient condition fails.

**Verified centered spectral protection.** With the exact midpoint c and
half-spacing s, the centered controls satisfy
‖(R−I/2)x‖=‖x‖/2 and ‖(M−I)x‖=‖x‖. The centered perturbation has
force bound ρ‖x‖/2; the exterior residual is at least
(g−ρ/2−|e−c|)‖x‖. Thus if ρ/2+s<1/128, the complete real spectrum in
[c−s,c+s] consists precisely of the two controlled energies, every
eigenvector there has zero leakage, and the distance to every other
real spectral energy (or energy of an eigenvector with nonzero leakage)
is at least 1/128−ρ/2−s>0. Since s≤ρ/2, ρ<1/128 suffices with
gap at least 1/128−ρ. This doubles the earlier pure-axis sufficient
ranges. Full Lean and the existing preparation Comparator passed.
The new principal theorem is `coordinatedCluster_centered_isolation`,
with numerical corollaries `coordinatedCluster_centered_condition_of_budget`
and `coordinatedCluster_centered_gap_ge`. See [README §4.110](coordinated-quantum-control.md#4110-spectral-protection-during-coordinated-control)
for the complete declarations and proof. The separate
[Palomar package](../palomar/spectral-protection-during-coordinated-control/) passed full Lean and independent comparison of all 15 selected propositions with the bundled NanoDa and con-ron kernels. It was registered on 26 November 2026 as [PALOMAR-2026-11-26-000015 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000015&version=1).

**L8a proof obligations**

- [x] **L8a.1:** Exact bounded control decomposition, `M² = 2M`, exact
  norms `‖R‖ = 1`, `‖M‖ = 2`, and `‖B‖ ≤ |δ| + 2|η|`.
- [x] **L8a.2:** Exact two-way controlled plane eigenvalue characterization,
  degeneracy criterion and reducing projections on the natural domain.
- [x] **L8a.3:** Quantitative exterior residual and eigenvalue exclusion,
  full real-spectrum characterization and zero leakage in the explicit
  open window.
- [x] **L8a.4:** Consolidated full-real-spectrum isolation for ρ < 1/256,
  with positive separation 1/128−2ρ, including zero controls.
- [x] Verify the centered spectral-protection refinement.
- [x] Independently compare the new spectral-protection candidate.
- [x] Submit the candidate for separate registry verification and record the fourth registration.
- [x] Exact variable-duration three-pulse preparation with arbitrarily weak ideal controls,
  normalized continuous zero-leakage evolution, target up to global phase,
  and prescribed real spectral separation in each setting (§4.111). Lean-verified.
- [x] Independently compare all 19 selected propositions of the fifth candidate (Lean default, NanoDa and con-ron).
- [x] Complete separate registry verification and record the fifth registration: [PALOMAR-2026-11-27-000003 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-27-000003&version=1).
- [ ] Investigate further sharp bounds and imperfect control dynamics.

**Scope and continuation.** L8a is a verified static spectral-protection
theorem for ideal controls. Later L8b–L8e may address nonuniform control
errors, leakage, preparation fidelity and robust pulse design.
No dynamical noise bound, arbitrary-strength spectral gap, hardware
robustness is asserted. The fourth registration concerns static spectral protection. L6 and all
Track A objectives remain open and are currently paused.

