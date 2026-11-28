[← Main README and table of contents](../README.md) · [Verified milestones](verified-milestones.md) · [Historical roadmap](research-roadmap-history.md)

## 6. Roadmap: proof status and next steps

**Active priority:** Track B / L9 (§6.10). Track A is paused, and the original L6 and L8b–L8e programs are deferred, not abandoned. This roadmap contains remaining objectives only. Results already proved are recorded in the scientific chapters and [verified milestones](verified-milestones.md). Historical numbering is retained: §6.2 is complete and is no longer an active section.

<details>
<summary>Open research objectives by section</summary>

- [6.1. P2 — Spectral foundations and the complex-resolvent interface](#61-p2--spectral-foundations-and-the-complex-resolvent-interface)
- [6.3. P3 — Full spectral products and their exact zero divisors](#63-p3--full-spectral-products-and-their-exact-zero-divisors)
- [6.4. P4 — A confined Ammann–Beenker model and a finite intervention](#64-p4--a-confined-ammannbeenker-model-and-a-finite-intervention)
- [6.5. Local geometric defects and relative spectral products](#65-local-geometric-defects-and-relative-spectral-products)
- [6.6. Certified finite-patch approximation and zero response](#66-certified-finite-patch-approximation-and-zero-response)
- [6.7. Exploratory objectives: zero statistics and structural constraints](#67-exploratory-objectives-zero-statistics-and-structural-constraints)
- [6.8. Independent statement verification and research-interest assessment](#68-independent-statement-verification-and-research-interest-assessment)
- [6.9. L8 — Deferred robustness and control refinements](#69-l8--deferred-robustness-and-control-refinements)
- [6.10. L9 — Independently controllable spectrally protected localized qubits (open)](#610-l9--independently-controllable-spectrally-protected-localized-qubits-open)

</details>

### 6.1. P2 — Spectral foundations and the complex-resolvent interface

**Paused — Track A.** The real spectral foundations are established in [§§4.1–4.39](infinite-spectral-theory.md). The remaining interface is complex, on the original confined natural domain.

- [ ] Construct the required complexification and complex shifted inverse
  on the natural domain, and relate it to the verified real spectral data.
- [ ] Prove the resolvent identities, analyticity and compression facts
  needed to define $G_S(z)$. The real completeness theorem is not by
  itself this complex-resolvent interface.

### 6.3. P3 — Full spectral products and their exact zero divisors

**Paused — Track A.** The full products and zero-counting results are documented in [§§4.49–4.67](infinite-spectral-theory.md). Only the following refinements remain.

- [ ] Derive numerical cofactor and isolation-radius certificates for
  this interacting geometric product. The linear onsite constants cannot
  be transferred unchanged to it.
- [ ] Extend counting to noncircular contours if an application needs
  them. This does not block §6.4. Finite-patch error certificates remain
  the separate task of §6.6.

### 6.4. P4 — A confined Ammann–Beenker model and a finite intervention

**Paused / deferred.** The concrete graph, compact crossing and exact coordinated preparation are documented in [§§4.68–4.79](ammann-beenker-geometry.md), [§§4.80–4.98](single-edge-control.md) and [§§4.99–4.111](coordinated-quantum-control.md). The unbounded confined operator still requires general complex propagation; the bounded plateau evolution of §4.117 does not discharge that obligation. The original L6 single-edge program remains separate from the completed L7 protocol.

- [ ] Construct a general full complex Hilbert-space unitary propagator.
- [ ] **L6 (deferred): define the single-edge controlled dynamics.** Extend the relevant setting to
  complex quantum states and a time-dependent edge weight, while keeping
  the underlying infinite operator and its domain well defined. Determine
  how the two compact-mode amplitudes interact with the remaining modes.
- [ ] **L6 (deferred): characterize reachability and test a two-control protocol.**
  Prove the conserved dark-state occupation for edge-only time-dependent
  dynamics. Starting from one compact mode, test a weak edge pulse to
  change the amplitudes, then restore the edge and detune `t` to
  adjust their relative phase. Seek an explicit bound on preparation
  error and leakage into other energy levels; determine whether this
  achieves arbitrary targets in the compact plane up to a chosen error.
  See [the research note](edge-control-reachability.md) for the
  proposed protocol and its limitations.
- [ ] **General complex dynamics and L6 controlled A/B preparation (open).** Build the genuine complex-Hilbert-space
  unitary evolution with natural-domain invariance and generator
  commutation, apply the proved leakage bounds to it, and then
  certify nontrivial bright-mode mixing, target amplitudes,
  relative phase and reachability limitations.
- [ ] Derive an isolation radius and a nonzero analytic-cofactor lower
  certificate for a specified geometric spectral level or cluster.
  Account for multiplicity; do not assume simple spectrum.
- [ ] Combine these data with a quantitative spectral-tail bound to
  certify a finite-product cutoff and exact disk zero count (§6.3).
  The onsite constants of §4.67 do not automatically apply here.
- [ ] Prove a uniform vertex-separation estimate if needed for sharper
  geometric estimates; it is not a prerequisite for the established
  summability and full-product application.
- [ ] Formalize global rotational symmetry, polygonal tiling coverage and
  aperiodicity when these properties are part of a claimed application.
  The present spectral theorem is about the explicitly defined graph.
- [ ] Compare the proved multiplicity-two classification of §4.78 with
  the compact-state literature and obtain an expert assessment (§6.8).

### 6.5. Local geometric defects and relative spectral products

**Paused — Track A.** The relative determinant and its geometric application remain open.

- [ ] Specify the allowed changes of site energies or couplings and
  prove their finite-support operator representation. If a geometric
  move changes the site set, construct and justify the identification
  used for the two Hilbert spaces.
- [ ] Verify self-adjointness, a strictly positive gap, compact resolvent
  and the summability assumptions for both operators.
- [ ] Construct the complex Green matrix using the interface of §6.1.
  Prove the determinant identity and its normalization, with an explicit
  common domain and meromorphic continuation statement.
- [ ] Track the difference of zero multiplicities through the relative
  identity, including shared zeros and pole cancellations.
- [ ] Relate finite-coordinate observation to the visibility of low
  eigenspaces in the compressed resolvent. Prove any residue-rank or
  nonvanishing statement that is used; do not assume that restriction
  injectivity already supplies the entire determinant theorem.
- [ ] Apply the result to an explicitly verified intervention or geometric
  change in the concrete model. State the resulting information about
  zero response with its actual parameter and energy range.

### 6.6. Certified finite-patch approximation and zero response

**Paused — Track A.** The objective is a certified approximation to the infinite operator, not merely a finite numerical spectrum.

- [ ] Define a finite-patch operator with explicit boundary conditions and
  its embedded resolvent. Preserve the distinction between truncating a
  fixed confined operator and changing the infinite-volume model.
- [ ] Bound the error of the Green matrix on specified compact sets away
  from spectral poles. Derive any exponential buffer estimate from
  verified locality and barrier assumptions, with explicit constants;
  do not assume a universal exponential rate.
- [ ] Propagate the matrix error to the relative determinant and the
  analytic products, controlling their normalizations. The absolute
  scalar tail budget of §4.61 and the linear-growth rate of §4.66 are
  available for a fixed spectral sequence; deriving the required data
  from a finite-patch matrix remains to be justified. The worked numerical
  onsite certificate of §4.67 does not supply such a matrix error.
- [ ] Certify zero counts in contours and intervals for the finite-patch
  approximation, with multiplicities. The bounded common-domain operator
  certificate of §4.56 is available only after a compatible error bound
  has been proved; it does not identify a finite matrix with the infinite
  operator. Sections 4.60–4.65 supply local location estimates with
  exponent $1/m$ and exact counts with multiplicities on disks under a
  strict scalar boundary error. A finite-patch application must still
  construct that error certificate and its boundary margins. Counts on
  noncircular contours and the required finite-patch error bounds remain
  open.
- [ ] Make the resulting error bounds small relative to the spectral
  scale of the proposed application. In statistical comparisons, fix the
  unfolding independently and control its amplification of spectral error.
- [ ] Produce a worked finite certificate for the concrete geometric
  application, separating proved error bounds from numerical evidence.

### 6.7. Exploratory objectives: zero statistics and structural constraints

**Exploratory / paused — Track A.** These questions are independent of the established exact zero locations.

- [ ] Define the energy windows, symmetry sectors, normalization and
  averaging procedure for the zero statistics being compared.
- [ ] Investigate whether a specified model or geometric family has local
  correlations approaching a random-matrix law. A CUE/GUE bulk comparison
  targets the sine-kernel process after unfolding, not merely the
  mean density of zeros or one matching histogram.
- [ ] Analyze the operator's symmetry class. The current real model does
  not automatically provide unitary-class statistics; any magnetic
  extension requires complex couplings, verified self-adjointness and
  analysis of residual symmetries.
- [ ] Treat convergence of pair correlations, convergence of all local
  correlations and evidence from finite spectra as different claims.
  None follows from the prescribed line or from the relative-product
  identity.
- [ ] Define an analytically meaningful object from an independently
  specified geometric construction without encoding a desired zero line
  in its factors or an affine coordinate. Investigate whether a proved
  structural mechanism then forces its zeros onto a line.

### 6.8. Independent statement verification and research-interest assessment

**Open — scientific assessment.** Registry acceptance and mechanical verification do not establish mathematical novelty or experimental relevance.

- [ ] Compare the precise new theorem against the specialist
  literature and obtain independent expert assessment of interest
  and novelty independently of registry verification.
- [ ] Continue the separate scalar cofactor and finite-patch
  certificates required in §§6.3, 6.5 and 6.6.

<a id="69-l8a--quantitative-spectral-protection-under-coordinated-controls-verified-refinements-open"></a>

<a id="69-l8a--quantitative-spectral-protection-under-coordinated-controls-open"></a>

### 6.9. L8 — Deferred robustness and control refinements

**Deferred — Track B.** Ideal spectral protection and arbitrarily weak protected preparation are completed in [§§4.106–4.111](coordinated-quantum-control.md). Future L8b–L8e concern nonuniform control errors, leakage, preparation fidelity and robust pulse design; see the [specialized control roadmap](bright-spectral-splitting-roadmap.md).

- [ ] Investigate further sharp bounds and imperfect control dynamics.

### 6.10. L9 — Independently controllable spectrally protected localized qubits (open)

**Active — Track B.** The immediate target is to determine the spectral and robustness limits of the natural remote two-state architecture on the unchanged canonical plateau. See [§§4.114–4.118](natural-plateau-architecture.md) for the established results and the [L9 roadmap](multi-qubit-roadmap.md) for the detailed open tasks.

- [ ] Determine whether the full eigenspaces at the two natural energies have positive collective gaps, or whether other spectral energies accumulate there. An individual residual gap against equal-energy replicas is impossible.
- [ ] Investigate arbitrarily weak spatial controls, variable pulse durations and any collective protection that can actually be proved.
- [ ] Study larger supported modes, concrete disorder, mixing of equal-energy replicas, refocusing and long-time robustness.
- [ ] Assess the natural direct-sum architecture against the deferred alternative of engineered distinct degenerate energies; do not assume tensor-product qubits or add static wells without a demonstrated need.
- [ ] Complete registry review of the independently compared eighth candidate and assess related literature; consider further candidate selections for the verified control and stability results separately.

## Historical references

<a id="62-p2--quantitative-observation-and-control-of-low-energy-levels"></a>

[Former §6.2 — Quantitative observation and control of low-energy levels (completed)](research-roadmap-history.md#62-p2--quantitative-observation-and-control-of-low-energy-levels). The scientific results remain in [§§4.40–4.59](infinite-spectral-theory.md).

The [complete earlier roadmap](research-roadmap-history.md) retains the original checklists and all completed material. See [Chapter 7 — Research methodology and maintenance rules](maintenance-rules.md#7-research-methodology-and-maintenance-rules).
