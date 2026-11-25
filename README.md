# Spectral Geometry

**A research program in Lean 4 and Mathlib studying how local changes to
operators on infinite geometric graphs affect their energy levels and the
zeros of analytic functions built from those levels.**

## Executive summary

We study how local changes affect waves in an infinite Ammann–Beenker network, a mathematical model with an octagonal structure.

### First Palomar result — Exactly two localized crossing states

At a particular energy, the network has two localized wave patterns, which we call A and B. An earlier theorem, registered with Palomar on 6 November 2026 as [PALOMAR-2026-11-06-000012 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-06-000012&version=1), proved that these two patterns account for all independent states at that energy in the entire infinite network.

Further results proved in Lean establish that, at this special setting, no other real energy level lies within a distance of 1/128 of their common energy.

The exact multiplicity is the registered result; the quantitative baseline gap is a separate Lean-verified theorem.

### Second Palomar result — A One-Edge Change Splits Two Energy Levels in an Infinite Ammann–Beenker Graph

One way to change the energies is to change a parameter that affects the first ring of the network. This raises or lowers the energy of A by exactly the parameter change, while leaving the energy of B unchanged. Both patterns remain exact eigenstates of the infinite system, without spreading outside their original localized forms. The spectral gap was proved at the original setting; for sufficiently small changes to this parameter, separation from the other energy levels also follows from the general eigenvalue-stability estimates already established in Lean.

Another way is to change the strength of a single edge connecting the two rings. Here the situation is more subtle. One combination of the original patterns, called the dark state, remains protected at the original energy. The other, called the bright state, responds to the change and interacts with the rest of the infinite network.

The second theorem, separately registered with Palomar on 23 November 2026 as [PALOMAR-2026-11-23-000017 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-23-000017&version=1), proves what actually happens in this second case. For a sufficiently small, nonzero edge change, there are exactly two distinct real energy levels represented by eigenvectors in a specified narrow range. One remains fixed, while the other moves upward when the edge is strengthened and downward when it is weakened. Each level has only one independent wave pattern.

The theorem also gives two precise numerical guarantees. The moving energy differs from the original energy plus one quarter of the edge change by no more than 112 times the square of that change. For a normalized wave at the moving energy, the size of the part extending beyond the original two-state space is at most 64 times the square root of 7, multiplied by the absolute size of the edge change.

This means that we can make the external part of the moving wave as small as desired while keeping the two energy levels distinct. These are exact results for the infinite system, not predictions from a simplified two-state model.

What happens if the edge change is temporary? Separate theorems, already proved in Lean, study an edge change applied for a period of time and then switched off. They give a bound on the wave's component outside the original two-state space: no more than 512 times the absolute size of the edge change, multiplied by the initial wave's size. This bound is independent of the duration of the pulse and of the time elapsed after switching it off.

These temporal conclusions are conditional: they assume that the supplied evolution preserves norms, preserves the operator's mathematical domain, and commutes with the relevant Hamiltonian during each stage. A general physical quantum propagator has not yet been constructed in this formalization.

The results fit together in a natural way. Changing the first-ring parameter offers an exact way to adjust the relative energies of the two original patterns without changing their shapes. Changing the connecting edge produces a genuine energy separation involving a bright-derived state, while the associated spreading into the infinite network can be kept small. The temporal results complement these spectral findings by showing that, under suitable evolution assumptions, the wave remains close to the original two-state space during and after a temporary edge change.

The exact signed spectral-splitting theorem is the second registered result; the baseline gap and conditional pulse bounds are not independently selected in any of the three registrations.

### Third result — Exact Leakage-Free Quantum State Preparation on an Infinite Ammann–Beenker Graph

We study a particular infinite Ammann–Beenker network, an octagonal mathematical graph with a confining potential. At a special energy it supports two localized wave patterns, A and B. Their normalized sum is called the dark state, and their normalized difference the bright state. Earlier registered results prove that the two patterns account for all independent states at the crossing energy, and that changing a single edge splits this energy while allowing a small part of the bright-derived wave to spread into the rest of the network.

The new theorem asks whether we can prepare any desired mixture of the dark and bright waves without any such spreading. The answer is yes, under two independently adjustable signed real controls. The first changes a common parameter on the eight vertices of the first ring, shifting the energy of A relative to B. The second changes eight genuine edges connecting corresponding sites on the two rings, all by the same amount. These edges are distinct and share no endpoints. Their combined effect leaves the dark state unchanged and shifts the bright energy by twice the edge-strength change. Both controls preserve the original two-state space exactly on the full infinite graph.

The controls change the state in different ways: one mixes the dark and bright amplitudes, while the other changes their relative phase. By applying three consecutive pulses of unit duration (edge control, first-ring control, edge control), we can start with the dark wave and reach any chosen normalized pair of complex dark and bright amplitudes, including the pure bright wave. The final state differs from the desired state only by a common phase of modulus one, which does not change the relative amplitudes or the physical ray. The accumulated phase is given explicitly. The pulse strengths can be chosen from the magnitudes and phases of the desired amplitudes.

The result concerns the actual infinite operator, not a numerical simulation or a two-state approximation. Lean constructs a continuous time-dependent state as two real square-summable graph vectors representing its real and imaginary parts. These vectors lie in the natural domain of the unbounded Hamiltonian at every time and satisfy the coupled full-graph Schrödinger equations during each open pulse interval. The total squared complex norm stays exactly one. The part of each vector outside the original localized two-state space is exactly zero throughout the protocol, including both switching times and the final state. No small-control assumption or pre-existing time-evolution map is required. The Hamiltonian may change discontinuously at the switches, so differentiability at the switching instants is not asserted.

This is an existence theorem for preparation from the dark state in this specified compact plane with independently tunable signed controls. It does not construct a general complex unitary propagator for arbitrary initial data on the infinite graph, prove phase-sensitive equality without a common phase, claim an optimal number of controlled edges, or establish experimental feasibility or originality. The earlier single-edge spectral-splitting theorem is a separate result.

**Palomar registration.** The third result was registered on 25 November 2026 as [PALOMAR-2026-11-25-000001 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-25-000001&version=1). Full Lean verification, independent statement comparison and Challenge renderability passed. The automated editorial review reported no identified problems with the selected statements, their presentation or their research relevance. The first two Palomar registrations remain unchanged. Registration establishes mechanical verification of selected statements, not human peer review, novelty or experimental feasibility.

The research direction was conceived and directed by Alessandro Odasso, who is not a mathematician. According to the maintainer, AI generated the mathematical proofs and Lean formalizations under his direction. The originality and scientific significance of these results have not yet been independently assessed.

## Research tracks and current priority

The project has **two complementary research tracks**, not a replacement
of its original goals:

| Track | Question | Status and next steps |
| --- | --- | --- |
| **A — Spectral geometry and analytic zeros (original program)** | How do local changes affect the full infinite-operator spectrum and the zeros of its canonical products? | Extensive formal results (§§2–4, 6.1–6.4); open cofactor and isolation certificates, relative determinant identities, certified finite-patch estimates and exploratory zero statistics (§§6.3, 6.5–6.7). |
| **B — Localized modes and coherent control (emergent program)** | Can local graph controls manipulate the dark/bright states of the same infinite Hamiltonian? | L1–L5 verified; L5 registered. **L7 registered.** **L7a complete** (§§4.99–4.100); **L7b complete at the algebraic level** (§§4.100–4.101): exact matrix, full Lie generation and constructive Euler state reachability. **L7c.1–4 complete for compact-plane preparation** (§§4.102–4.105): exact single-axis trajectories, phase-weighted rotations, continuous three-pulse dynamics and arbitrary normalized target preparation from dark up to global phase, with zero leakage at all times. General full-space complex dynamics remain open. The original **L6** single-edge approximate control is kept for later. |

Track B emerged from the verified graph geometry and spectral splitting,
but quantum control is **not a prerequisite** for completing Track A.
L7 now proves exact normalized target preparation from dark under coordinated controls; the distinct L6 single-edge approximate preparation theorem remains open.
See the [L7/L6 research roadmap](docs/bright-spectral-splitting-roadmap.md)
and the preserved [single-edge research note](docs/edge-control-reachability.md).
The detailed Lean-module catalogue and all existing theorem descriptions
remain below.

## Table of contents

- [Executive summary](#executive-summary)
  - [First Palomar result](#first-palomar-result--exactly-two-localized-crossing-states)
  - [Second Palomar result](#second-palomar-result--a-one-edge-change-splits-two-energy-levels-in-an-infinite-ammannbeenker-graph)
  - [Third result](#third-result--exact-leakage-free-quantum-state-preparation-on-an-infinite-ammannbeenker-graph)
- [Research tracks and current priority](#research-tracks-and-current-priority)
- [Scientific audience and possible relevance](#scientific-audience-and-possible-relevance)
- [Current status and verified milestones](#current-status-and-verified-milestones)
- [1. Research program and geometric model](#1-research-program-and-geometric-model)
- [2. Canonical products and analytic foundations](#2-canonical-product-and-analytic-foundations)
- [3. Finite-dimensional geometric operators](#3-finite-dimensional-geometric-operators)
- [4. Infinite-dimensional operators and spectral theory](#4-infinite-dimensional-geometric-operators-and-spectral-theory)
  - **Ammann–Beenker model, crossing and controls**
    - [4.68–4.70. Graph construction and spectral response](#468-an-explicit-octagonal-cut-and-project-vertex-set)
    - [4.74–4.75. Localized modes and exact crossing](#474-compact-eigenvectors-on-the-infinite-natural-domain)
    - [4.78. Exactly two crossing states](#478-central-support-and-exact-multiplicity-of-the-infinite-crossing)
    - [4.79. Certified spectral gap](#479-a-conservative-quantitative-real-spectral-gap-at-the-crossing)
    - [4.80. Two ways to change the energies: ring parameter and connecting edge](#480-first-exact-algebraic-results-for-controlling-the-two-compact-modes)
    - [4.81. Projection onto the two-mode space and external leakage](#481-exact-qubitleakage-bookkeeping-after-a-temporary-pulse)
    - [4.85–4.88. Temporary edge pulses and switch-off bounds](#485-uniform-post-pulse-leakage-without-a-perturbed-spectral-projector)
    - [4.89–4.91. Dark-state evolution and bright-state response](#489-an-exact-complex-phase-schrödinger-trajectory-for-the-dark-mode)
  - **Quantitative spectral splitting, registration and coordinated control**
    - [4.93–4.96. From existence to quantitative bounds](#493-verified-dark-simplicity-and-a-distinct-perturbed-spectral-level)
    - [4.97. Final L5 theorem: signed bright splitting](#497-signed-shift-and-consolidated-infinite-operator-splitting)
    - [4.98. Palomar registration and independent verification](#498-palomar-registration-signed-bright-splitting)
    - [4.99. Coordinated eight-edge matching and exact dark cancellation](#499-coordinated-eight-edge-matching-and-exact-dark-cancellation)
    - [4.100. Exact invariant-plane control and Pauli generator algebra](#4100-exact-invariant-plane-control-and-pauli-generator-algebra)
    - [4.101. Full Lie generation and constructive two-state rotations](#4101-full-lie-generation-and-constructive-two-state-rotations)
    - [4.102. Exact natural-domain Schrödinger trajectories for both control axes](#4102-exact-natural-domain-schrödinger-trajectories-for-both-control-axes)
    - [4.103. Exact identification of physical pulses with Pauli rotations](#4103-exact-identification-of-physical-pulses-with-pauli-rotations)
    - [4.104. Continuous three-pulse protocol with exact zero leakage](#4104-continuous-three-pulse-protocol-with-exact-zero-leakage)
    - [4.105. Exact arbitrary target preparation from dark without leakage](#4105-exact-arbitrary-target-preparation-from-dark-without-leakage)
- [5. Building and verification](#5-building-and-verification)
- [6. Roadmap: both research tracks and open questions](#6-roadmap-proof-status-and-next-steps)
  - [6.1–6.4. Original spectral and geometric program](#61-p2--spectral-foundations-and-the-complex-resolvent-interface)
  - [6.4. L7 exact preparation verified; L6 preserved](#64-p4--a-confined-ammannbeenker-model-and-a-finite-intervention)
  - [6.5–6.7. Relative products, finite patches and exploratory zeros](#65-local-geometric-defects-and-relative-spectral-products)
  - [6.8. Scientific assessment and submission status](#68-independent-statement-verification-and-research-interest-assessment)

## Scientific audience and possible relevance

The results concern one explicitly defined **confined infinite Ammann–Beenker graph**. Their value is not that dark states, localized waves or single-edge perturbations are new ideas, but that several spectral statements have been proved for the complete infinite operator rather than inferred from a finite sample.

- **Mathematicians studying spectral theory and discrete Schrödinger operators** may be interested in the exact two-dimensional crossing eigenspace, the certified real spectral gap, and the response to a rank-one edge change. The main result identifies the two nearby simple eigenvalues, the direction of the moving level, a quadratic energy-error bound and a bound on the moving eigenvector's exterior component.
- **Researchers on quasicrystals, compact localized states and flat bands** may find the contrast between two interventions useful. Changing the first-ring parameter shifts one compact mode's energy exactly while preserving both mode shapes. Changing the connecting edge instead protects the dark combination but gives the bright-derived state a controlled coupling to the rest of the infinite network. The original localized patterns themselves were known before this formalization. The coordinated matching (§§4.99–4.100) supplies a distinct bounded symmetric intervention that preserves the whole two-mode plane exactly.
- **Theorists working on wave control, photonic lattices or coupled-resonator networks** may find the temporary-edge results relevant as a mathematical starting point. The proved duration-independent leakage estimates require supplied norm-preserving, domain-preserving evolutions that intertwine their respective Hamiltonians. These conditional single-edge bounds do not establish a general physical propagator or the L6 preparation theorem. The distinct coordinated-control theorem (§4.105) does establish exact arbitrary normalized target preparation from dark, not experimental feasibility.
- **Researchers in formalized mathematics** may be interested in how natural domains of unbounded operators, complete real eigenbases, explicit spectral gaps and quantitative perturbation estimates are handled in Lean 4 and Mathlib.

These are **plausible research audiences**, not evidence of originality, practical usefulness or scientific impact. Independent expert evaluation and comparison with the specialist literature are still needed.

## Current status and verified milestones

The table below separates proved results from remaining research tasks.

| Part of the program | Status |
| --- | --- |
| Natural-domain operators, bounded matching interactions, conditional self-adjointness and compact resolvents | Formalized under the explicit hypotheses documented in §4 |
| Real spectral completeness, exact geometric multiplicities, ordered infinite enumeration and qualitative divergence | Formalized under the additional hypotheses of §§4.23–4.38 |
| Finite-coordinate detection and the multiplicity bound for one low-energy eigenspace | Formalized in §4.40; foundational observation result |
| Simultaneous quantitative observation and total low-energy multiplicity counting | Formalized in §§4.41–4.43, with symmetry for simultaneous spectral control |
| Variational characterization, ordered onsite comparison and finite-sector eigenvalue response | Formalized in §§4.44–4.47 with complete eigenbases, exact multiplicities and explicit infinite-indexing conditions |
| Positive full-spectrum inverse-square summability and its preservation under nonnegative finite-sector interventions | Formalized under §4.48's signed-correction criterion and §4.58's positive-interaction criterion |
| Entire canonical products and exact zero divisors for admissible positive full spectra | Formalized in §§2.4 and 4.49: every zero has its exact geometric multiplicity; normalization and paired symmetry are proved |
| Indexed finite-sector response of full spectral-product zeros, with operator-specific exact geometric orders | Formalized in §§4.50–4.52 and 6.3 for the positive finite-sector family under the stated infinite-indexing, gap and summability conditions |
| Exact zero-cluster certificates under small symmetric bounded operator errors | Formalized in §§4.53–4.56: finite boundary margins certify both reflected zero sets and their total multiplicity |
| Onsite ordering from properness and sharpened positive-interaction spectral and zero response | Formalized in §§4.57–4.59: the onsite gap is preserved without a small interaction-norm assumption; the onsite ordering is constructed |
| Scalar analytic approximation and local zero certificates with multiplicities | Formalized in §§4.60–4.65: explicit product-tail errors, multiplicity-dependent location bounds and exact total zero counts under a strict circular-boundary error; no simplicity assumption |
| Numerical tail rates and a worked scalar zero certificate | Formalized in §§4.66–4.67: explicit radius, cofactor bound and cutoff for the linear onsite model; numerical tail bounds also hold after symmetric nonnegative bounded interactions |
| Explicit octagonal cut-and-project vertex graph and nine-level finite-sector response | Formalized in §§4.68–4.70: infinite embedded vertices, exact central star, matching Laplacian and a nonempty controlled window |
| Planar vertex counting, geometric summability and full-product zero response | Formalized in §§4.71–4.72 for the explicit graph, with a nonempty nine-level window and no supplied summability hypothesis |
| Radial barrier, compact eigenvectors and ring-induced crossing | Formalized in §§4.73–4.75; includes a stationary one-edge state and an exact Rayleigh response; the later certified split spectral pair is in §§4.93–4.97 |
| Exact central sector and its boundary | Formalized in §4.76: origin and two eight-site rings, complete internal adjacency, ring degrees three and four, and exactly sixteen edges to the exterior |
| Complete central crossing kernel and supported eigenvectors | Formalized in §4.77; the central-support hypothesis remains explicit |
| Central support and exact global crossing multiplicity | Proved in §4.78: the two seed amplitudes give coordinates on the entire natural-domain eigenspace, of real dimension exactly two |
| Conservative quantitative real spectral gap at the crossing | Proved in §4.79: for $K_{t_*}$ the complete real bounded-inverse spectrum has no point other than $E_*$ within the closed radius $1/128$; exact spacing is not claimed by this result; separate edge-change splitting estimates are proved in §§4.93–4.97 |
| Exact edge and detuning control algebra | Formalized in §4.80 and two Lean modules: exact two-mode edge coupling, a normalized dark eigenstate on the full natural domain, and exact detuning identities. These are static operator results, not a quantum-control protocol |
| Qubit/leakage bookkeeping and control response | §4.81: Lean-verified orthogonal real-space decomposition, squared-norm budget, restored eigenstate and exact two-control off-plane formula |
| Uniform leakage estimate from nearby invariant planes | §4.82: Lean-verified generic conditional norm inequality independent of pulse duration; the graph spectral projector estimate and general complex unitary evolution remain separate; L7 exact preparation is established by a different coordinated-control construction in §4.105 |
| Pulse-residual and post-pulse control bounds | §§4.85–4.88: Lean-verified full-graph, duration-independent leakage inequalities for supplied norm-preserving, domain-preserving, Hamiltonian-intertwining real evolutions, plus full real self-adjointness; they do not construct the physical propagator |
| Explicit dark-state Schrödinger solution | §4.89: Lean-verified full-natural-domain, real/imaginary Schrödinger equations for the normalized dark mode, exact norm conservation and zero leakage; one trajectory, not arbitrary-state evolution or an A/B rotation |
| Exact bright generator response and preserved earlier Palomar candidate | §4.91: fourteen source theorems establish the full bright identity, dark amplitude and external-feedback bound. §4.92 documents the previous, unsubmitted generator-response candidate; its independent Challenge/Solution snapshots and Comparator are preserved in `palomar/dark-bright/`. The stronger L5 theorem is the registered selection of §4.98 |
| Explicit gap-to-eigenvector stability reduction | §§4.83–4.84: Lean-verified edge norm 2, reduced-gap residual bound and explicit nearby-eigenvector estimate; full perturbed spectral projector bounds remain open |
| Dark simplicity and genuine mobile spectral-level existence | §4.93: L1 dark-only eigenspace for ε ≠ 0; L2a ordered eigenbases and `2|ε|` stability; L2b exact double consecutive baseline slots; L2c real, distinct perturbed eigenvalue and nonzero natural-domain eigenvector within `2|ε|` for every ε ≠ 0. Lean-verified |
| Isolated simple dark/bright **point-spectrum** pair | §4.94: for `0<|ε|≤1/1024`, exactly two genuine natural-domain eigenvalue energies occur inside `|t-E_*|≤1/256`: the fixed simple dark level and one unique simple moving level within `2|ε|`. Lean-verified |
| Genuine moving-eigenvector bright amplitude and exterior bound | §4.95: the true moving eigenvector has `⟨D,x⟩=0`, `c=⟨F,x⟩≠0`, `x=cF+Qx` and `‖Qx‖≤256|ε||c|‖QWF‖`, with `‖QWF‖²=7/16`. Lean-verified |
| True infinite-operator quadratic energy law | §4.96: for the actual unique simple moving natural-domain level, `|E_b-(E_*+ε/4)|≤112ε²` when `0<|ε|≤1/1024`. Uses the exact bright residual pairing and `‖QWF‖²=7/16`. Lean-verified |
| Signed dark/bright spectral splitting, final theorem | §4.97: for `0<|ε|≤1/1024`, the moving energy shifts strictly in the direction of ε. The consolidated theorem explicitly asserts both nonzero eigenvectors, their simple eigenspaces, the point-spectrum window, quadratic energy law and exterior bright control. Lean- and Comparator-verified |
| L5 Palomar registration | §4.98: the strengthened L5 theorem, explicitly including the nonzero fixed dark eigenvector and its equation, was independently verified and registered as [PALOMAR-2026-11-23-000017 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-23-000017&version=1) on 23 November 2026 |
| Relative products and certified finite-patch zero response | Remaining obligations in §§6.5–6.6; geometric scalar cofactor/radius certificates also remain open |
| Coordinated eight-edge control, L7a first milestone | §4.99: eight genuine adjacent pairs with no shared endpoints, matched amplitudes, bounded symmetric correction and exact dark cancellation `MD=0`. Lean-verified |
| Exact invariant plane under both controls, L7a complete | §4.100: `Ma=a-b`, `Mb=b-a`, `MF=2F`, `QMP=0`, and full natural-domain invariance at arbitrary real control strengths. Lean-verified |
| Exact Pauli control algebra, L7b first part | §4.100: exact effective matrix in the normalized dark/bright basis, Pauli decomposition, noncommuting complex generators and all three commutators. Lean-verified |
| Full Lie generation and constructive Euler state reachability, L7b complete | §4.101: the smallest real commutator-closed subspace containing the two generators is all of `su(2)`; a three-rotation matrix product reaches every normalized complex pair from dark, with independent signed control coefficients. Lean-verified |
| Exact single-axis Schrödinger trajectories, L7c.1 | §4.102: arbitrary complex compact-mode coefficients, exact coupled real/imaginary full-domain equations, conserved squared complex norm and zero leakage of both components for all real times; the combined real Hamiltonian is self-adjoint at arbitrary real control strengths. Lean-verified |
| Exact phase-weighted rotation action, L7c.2 | §4.103: the full natural-domain single-axis trajectories equal the embeddings of the X and Z rotation matrices with their common phases, for every complex initial pair and real strength and time. Lean-verified |
| Continuous three-pulse protocol, L7c.3 | §4.104: exact Z–X–Z composition for arbitrary complex initial pairs and real strengths, continuous full-space components and exact switch matching, natural-domain membership, conserved squared complex norm and zero leakage at every time, with full Schrödinger equations on each open pulse interval. Lean-verified |
| Exact arbitrary target preparation, L7c.4 | §4.105: every normalized complex dark/bright pair is reached from dark up to the explicit common phase by three unit-duration local control pulses; continuous full-graph components, natural-domain membership, conserved unit norm, full piecewise Schrödinger equations and zero leakage at all times. Lean-verified and registered as [PALOMAR-2026-11-25-000001 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-25-000001&version=1) |
| Remaining control research | General complex full-space propagator, preparation from arbitrary initial states as a separately stated theorem, control optimality and the distinct L6 approximate single-edge theorem remain open (§6.4) |

The program already has formal results on infinite-operator spectral
enumeration, finite-coordinate observation, exact eigenvalue multiplicities,
spectral response, and zeros of canonical products. The explicit octagonal
graph supplies concrete examples, including the crossing described above.
The more ambitious geometric cofactor certificates, relative-product
identity and certified finite-patch comparisons remain open (§6).
The registered crossing result (§4.78), the separately proved gap (§4.79),
the certified dark/bright generator algebra (§§4.80–4.91), the archived
unsubmitted combined theorem (§4.92), the registered L5 spectral splitting
(§§4.93–4.98), exact coordinated-plane invariance, full Lie generation, constructive matrix reachability, exact single-axis phase-weighted rotations, continuous three-pulse dynamics and exact arbitrary target preparation from dark (§§4.99–4.105), and
the still-open dynamical coherent-control problem (§6.4) have distinct scopes.

The chosen affine line is part of the definition of the analytic family.
Originality and research significance must come from the geometric and spectral
information established about that family, rather than from choosing the line.
No identification with the Riemann zeta function or proof of the Riemann
hypothesis is claimed.

## 1. Research program and geometric model

### 1.1. The research question

How can a local change in an infinite geometric system be detected in an
analytic function whose zeros record its spectrum? Which finite sets of sites
observe low-energy modes, how do perturbations on those sites move the
corresponding levels, and with what error can finite patches certify that
response?

The program studies these questions for an operator with a confining onsite
potential, bounded local interactions and controlled perturbations. It then
transports the spectral information to a normalized canonical product on a
fixed complex line. The concrete application uses the centered octagonal
cut-and-project vertex graph (§§4.68–4.79). The spectral proofs use its
verified vertex and edge geometry. Polygonal tiling coverage and aperiodicity
remain open (§6.4).

The concrete Ammann–Beenker results may interest researchers in
spectral theory, localization on quasiperiodic networks, wave control and
formal verification. The [scientific audience and possible relevance](#scientific-audience-and-possible-relevance)
section explains what each community might find useful and which
conclusions are not yet established. The broader analytic-product part
of the program may also interest specialists in entire functions
associated with operator spectra.

### 1.2. First substantive milestone: finite-coordinate observation

Let
```math
H=M_V+B,\qquad
D(V)=\{\psi\in\ell^2(T):V\psi\in\ell^2(T)\},
\qquad
F_R=\{t\in T:V(t)\le R\}.
```

Here the real Hilbert space of sites may be infinite, the potential may be
unbounded, and the full correction $B$ is bounded. Under the precise
properness and resolvent hypotheses in §4.40, the proved theorem gives
```math
\lambda<R-\|B\|,\qquad \lambda\ne a
\quad\Longrightarrow\quad
\dim E_\lambda(H)\le \#F_R.
```

Its central construction is an injective linear restriction map
```math
E_\lambda(H)\longrightarrow\mathbb R^{F_R},
\qquad \psi\longmapsto\psi|_{F_R}.
```

Thus two vectors in the same fixed-eigenvalue eigenspace that agree on $F_R$
agree everywhere. The result observes the entire eigenspace, not merely one
chosen eigenvector. It concerns geometric multiplicity and does not require
the bounded correction to be symmetric.

The foundational Lean declaration is
[SpectralGeometry.infiniteLocalMatching_full_eigenspace_finrank_le_lowEnergyTiles](SpectralGeometry/InfiniteLocalFullLowEnergyCounting.lean).
It assumes finite onsite sublevel sets, a real shift $a$ with
$V(t)-a\ge1$, the onsite resolvent $R_a^{\mathrm{on}}=(M_V-aI)^{-1}$,
the bound $\|B R_a^{\mathrm{on}}\|<1$, and the displayed restrictions on
$\lambda$. Its eigenspace is represented through the equivalent eigenspace
of the full compact shifted inverse; the source development connects that
representation to natural-domain eigenvectors.

The proof uses a quadratic-form obstruction: a vector vanishing on all sites
with $V(t)<R$ has energy at least $(R-\|B\|)\|\psi\|^2$. This is
incompatible with a nonzero eigenvector below that threshold. Applied to the
kernel of restriction, the obstruction gives injectivity and the dimension
bound.

**Role in the research program.** The theorem identifies a finite observation
sector for each sufficiently low eigenspace. Under the additional symmetry
and lower-bound assumptions, §§4.41–4.43 now prove quantitative observation of
the whole low-energy spectral subspace and a total count with multiplicities.
The variational bridge of §§4.44–4.46 turns that form inequality into
$\kappa\tau\le\lambda_n(H+\tau P_{F_R})-\lambda_n(H)\le\tau$
for the levels and parameter interval specified in §6.2, including repeated
levels. Section 4.48 transfers onsite summability to the positive full spectrum
and preserves it along this intervention. Section 4.49 now turns the exact
full spectral enumeration into an entire product whose zeros have precisely
the geometric eigenspace multiplicities. Sections 4.50–4.52 now transfer this response to the actual indexed zeros of
the two entire full spectral products, with fixed affine data and the correct
operator-specific geometric orders. Sections 4.53–4.56 now certify the total
zero multiplicity in a separated window under a small symmetric bounded
operator error. They derive all-index error bounds and use finite neighboring
level checks at the window boundaries. Sections 4.57–4.59 construct the onsite
ordering from properness and prove a stronger positive-interaction family:
the gap remains $v_0>0$, and the response coefficient becomes
$(R-E)/(R-v_0)$, with no interaction-norm penalty. Sections 4.60–4.62 add a
different kind of certificate: scalar approximation near a zero of order
$m$ preserves at least one nearby zero and bounds every zero in the certified
disk at the scale $\varepsilon^{1/m}$. The full product's geometric
multiplicities supply $m$, and inverse-square tails supply explicit product
truncation errors. Sections 4.63–4.65 now prove the disk argument principle
and Rouché's theorem, upgrading the local certificate to exactly $m$ zeros
counted with multiplicity under $\varepsilon<C\rho^m$. The approximant may
split a multiple zero. The conserved count is the original operator's
geometric multiplicity. Sections 4.66–4.67 now turn this into a numerical
worked certificate for onsite multiplication by $n+1$: radius $1/4$,
cofactor lower bound $1/5$, and a sufficient finite-product cutoff $16384$,
including a nonzero additional approximation-error budget. The same
quantitative tail estimates apply to its full spectrum with a symmetric
nonnegative bounded interaction, while the explicit cofactor and radius
are proved for the onsite model. Sections 4.68–4.70 now construct the
octagonal cut-and-project vertex graph and prove a concrete response for
its first nine ordered levels. Sections 4.71–4.72 use the geometric counting
and summability estimates to prove how the corresponding product zeros move.
For $0\le\tau\le4$, every level of $H$ and $H_\tau$ is at least one.
In either product, the order of a zero equals the geometric multiplicity of
the corresponding eigenvalue for that product's operator.

The concrete full-product response of §4.72 uses these source results under
its verified geometric hypotheses. They do not provide a numerical reconstruction
algorithm or independent control of several zeros. The relative
determinant identity in §6.5 is a separate proof obligation; it does not follow
from this theorem alone.

This is the first substantive observation milestone of the program, supported by
the operator-theoretic results catalogued in §§3–4. Its position in the program
does not assert mathematical priority, a new proof technique or an independent
research-interest assessment. The proof mechanism is a standard
quadratic-form and restriction argument. The first registered Palomar
result is documented in §4.78; the new proposal and its provenance are
described in §§4.92 and 6.8 and in [formalization.yaml](formalization.yaml).

### 1.3. The operator and its geometric inputs

The proposed geometric family is
```math
H_\varepsilon=M_V+L_w+\varepsilon P,
```
with action, whenever the geometric interaction is defined,
```math
(H_\varepsilon\psi)(t)
=V(t)\psi(t)
+\sum_{u\ne t}w(t,u)\bigl(\psi(t)-\psi(u)\bigr)
+\varepsilon(P\psi)(t).
```

The potential $V(t)$ assigns an onsite energy. The weights describe
interactions between sites, and $P$ is a bounded controlled perturbation.
For symmetric nonnegative weights, the interaction is a graph Laplacian.
The amplitude $\psi(t)$ belongs to a state of the entire system; it is not
a prescribed eigenfunction or an intrinsic energy of an individual tile.

The Lean type named Tile is an abstract site type. In a concrete application
its elements may be tiles or vertices of a tiling; that choice must be stated.
The Ammann–Beenker application in §6.4 uses vertices. Geometric rules determine
the potential and the couplings before the spectrum is studied.

For a finite patch the construction has matrix form
```math
H_\varepsilon
=\operatorname{diag}\!\left(V_i+\sum_jw_{ij}\right)-W+\varepsilon P.
```
For infinitely many sites it acts on the natural multiplication domain
$D(V)$, with bounded corrections added on that same domain.

The formalized infinite local interaction uses finitely many matching colors:
each involutive permutation $\sigma_i$ pairs a site with at most one neighbor
of color $i$, with a constant weight for that color. Under
$0\le w_i\le W$,
```math
L_w=\sum_{i=1}^{D}w_i(I-U_{\sigma_i}),
\qquad \|L_w\|\le2DW.
```
A named tiling must be represented by such matchings, or the framework must
first be extended with a proved alternative. The existing modules do not
already establish a representation theorem for every bounded-degree graph.

### 1.4. Confinement, observation and local changes

Finite onsite sublevel sets are a genuine growth assumption. On a
finite-local-complexity tiling, a potential determined only by a finite set of
local tile types takes finitely many values and cannot by itself supply that
assumption on infinitely many sites. On the octagonal graph, the chosen
potential is $V(v)=1+|p(v)|^2$, where $p(v)$ is the physical position.
Each bounded disk contains finitely many vertices, so the onsite sublevels
are finite (§§4.68, 4.70).

Raising the onsite energies by $\tau$ on $F_R$ gives the operator
```math
H_\tau=H+\tau P_{F_R},\qquad \tau\ge0.
```
On the octagonal graph, $F_5=\{v:|p(v)|\le2\}$ is the radius-two sector.
For this intervention, §4.72 compares the zeros of the full spectral products
of $H$ and $H_\tau$ using a common center, direction and normalization.
Perturbing just the eight neighbors of the origin produces the crossing of
§4.78, with the conservative real spectral isolation proved in §4.79.
Changing the weight of the edge specified in §4.75 leaves the sum of
the two compact modes at the crossing energy.

For a more general local change, the relative-product program in §6.5
requires a proof that the operator difference has the form $\iota_S K\iota_S^*$
on a finite set $S$. A change of site sets also requires identifying the two
Hilbert spaces.

## 2. Canonical product and analytic foundations

### 2.1. Verified analytic core

For positive levels $q_n$, a center $c\in\mathbb C$ and a nonzero direction
$d\in\mathbb C$, the analytic core defines
```math
D_q(s)=\prod_{n=0}^{\infty}
\left(1-\frac{(s-c)^2}{d^2q_n^2}\right).
```

[CanonicalProduct.lean](SpectralGeometry/CanonicalProduct.lean) defines
admissibility by positivity and a summable compact-set majorant for the
deviations of these factors from one. It proves compact-uniform convergence,
zero localization on the prescribed affine line, a sufficient admissibility
criterion
```math
\sum_{n=0}^{\infty}q_n^{-2}<\infty,
```
and the existence of a zero at each positive prescribed level. The paired
factors encode symmetric locations. The extensions in §2.4 now prove entire
holomorphy, the exact zero set, and the order at every point. Repeated levels
are counted exactly; an infinite tail cannot create additional zeros.

Section 4.48 now proves positive inverse-square summability for full interacting
levels under explicit properness, onsite ordering, summability and gap
hypotheses. Its power-growth corollary reuses the onsite criterion with exponent
greater than one half. `fullSpectrum_admissible_of_positive_summable` applies the
existing admissibility criterion to these levels, including the nonnegative
finite-sector family. Section 4.57 constructs the sorted onsite bijection on
infinite proper site types. Section 4.58 gives a separate positive-interaction
transfer with $V\ge v_0>0$, retaining the gap $v_0$ regardless of the
interaction norm. The analytic theorems apply to these inputs, and §4.49
identifies repetition counts with the original full geometric multiplicities.
The new indexed-point and exact-tag bridge of §§4.50–4.52 also makes this a
quantitative analytic displacement statement for positive finite-sector
perturbations; §4.59 proves its sharper positive-interaction version.
No complex resolvent is needed for this scalar product construction; the
complex-resolvent interface required for relative determinants remains open.
For the explicit octagonal graph, §§4.71–4.72 now derive the summability
inputs and instantiate the entire full products throughout 0≤τ≤4.

### 2.2. A common analytic coordinate for geometric operators

The spectral family, now verified under the hypotheses below, is
```math
F_H(z)=\prod_{n=0}^{\infty}
\left(1-\frac{z^2}{\lambda_n(H)^2}\right),
\qquad
D_H(s)=F_H\!\left(\frac{s-c}{d}\right).
```

The positive full spectrum with exact multiplicities and inverse-square
summability is now available under §§4.44–4.48. The sufficient signed-correction
criterion requires $v_0>\|B\|$ separately from onsite growth; compact resolvent
alone does not give summability or positivity. For symmetric nonnegative $B$,
§4.58 instead proves $\lambda_n(H)\ge v_0>0$ and summability from proper,
inverse-square-summable onsite energies, without a bound on $\|B\|$.
The onsite ordering is constructed by §4.57. Each of these baseline gaps and
summability conclusions persists for nonnegative finite-sector perturbations.
Section 4.49 proves the
exact zero divisor
```math
s=c\pm d\,\lambda_n(H),\qquad D_H(c)=1,
```
with orders equal to the corresponding geometric multiplicities. Both
$F_H$ and $D_H$ are entire, and $D_H(2c-s)=D_H(s)$. The affine-coordinate
identity, normalization and symmetry are proved in §2.4. The exact sequence
interface here addresses the infinite case; finite and empty spectra are not
represented by an artificial infinite repetition of levels.

Using the same $c,d$ for every operator makes zero displacement comparable
across the family. For $c=\tfrac12$ and $d=i$, the positive zero heights
are the positive eigenvalues. The affine coordinate fixes the line; it does
not create spectral correlations or encode a preferred distribution.
For the positive finite-sector intervention of §4.52, the bound
$|d|\kappa\tau\le |z_n^\pm(\tau)-z_n^\pm(0)|\le |d|\tau$ holds for every
index $n$ with $\lambda_n(H)\le E$, throughout $0\le\tau\le R-v_0$ and for
fixed $c,d$. The coefficient is positive since $E<R-\|B\|$ and $v_0<R$.
The energy window may be empty and different indices may share a zero.
For nonnegative $B$, §4.59 proves the same type of conclusion with the sharper
$\kappa=(R-E)/(R-v_0)>0$ under $E<R$, again with the explicit interval
$0\le\tau\le R-v_0$ and without asserting a nonempty target window.
Section 4.72 supplies a concrete application with at least nine indexed
levels on each branch, coefficient $1/2$, and summability derived from the
geometric model. Different indices may coincide; nine slots do not assert
nine distinct zero locations.

### 2.3. Target: a relative product for a finite geometric defect

Suppose the self-adjoint operators $H$ and
```math
H'=H+\iota_S K\iota_S^*
```
have a strictly positive spectral gap, compact resolvent and inverse-square-summable
ordered spectra. Here $S$ is finite, $\iota_S$ is coordinate insertion and
$K$ is a finite Hermitian matrix (real symmetric in the real model).

After constructing the necessary complex resolvent interface, define the
finite Green matrix and perturbation determinant
```math
G_S(z)=\iota_S^*(H-zI)^{-1}\iota_S,
\qquad
\Delta_S(z)=\det(I+K G_S(z)).
```

The proposed identity to establish is
```math
\frac{F_{H'}(z)}{F_H(z)}
=\frac{\Delta_S(z)\Delta_S(-z)}{\Delta_S(0)^2}.
```

It must be stated away from the original spectrum, with nonvanishing
normalization at zero and a meromorphic interpretation accounting for common
zeros, poles and multiplicities. **This identity is a research target, not a
theorem currently verified in this repository.**

The determinant has finite size, but its Green-matrix entries still depend on
the infinite operator. Certified finite-patch approximation is therefore part
of the intended result, rather than a consequence of the determinant's size.
The framework of finite-rank perturbation determinants is classical; see,
for example, [Golinskii, Spectra of infinite graphs with tails](https://doi.org/10.1080/03081087.2016.1155529).
The new §4.52 indexed zero-displacement inequality compares the products'
zeros without a relative determinant; it does not establish the proposed
identity or approximate a determinant. Any originality claim must concern a
precisely identified geometric or quantitative contribution beyond that
framework.

### 2.4. Entire products, exact zeros and their orders

[CanonicalProductAnalytic.lean](SpectralGeometry/CanonicalProductAnalytic.lean)
proves `canonicalProduct_differentiable` for every admissible positive sequence.
The proof applies the locally uniform limit theorem to finite polynomial
products. `canonicalProductAlong_differentiable` also covers every injectively
indexed subproduct, including finite and empty subproducts.

For $d\ne0$, `canonicalProduct_zero_iff` proves
```math
D_q(s)=0\quad\Longleftrightarrow\quad
\exists n,\ s=c+dq_n\ \text{or}\ s=c-dq_n.
```
Absolute summability of the factor deviations prevents a nonzero-factor tail
from acquiring an extra zero. `canonicalProduct_affine_coordinate` identifies
$D_q(s)$ with the standard-coordinate product at $(s-c)/d$.
`canonicalProduct_at_center` and `canonicalProduct_reflection` prove
$D_q(c)=1$ and $D_q(2c-s)=D_q(s)$; they do not require a choice of normalization
that varies with the operator.

[CanonicalProductZeroOrder.lean](SpectralGeometry/CanonicalProductZeroOrder.lean)
proves that only finitely many factors vanish at any point. Each such factor
has a simple zero when the level is positive and $d\ne0$. Splitting off this
finite set leaves an entire product nonzero at the point, so
`canonicalProduct_analyticOrderAt` gives its exact order. In particular,
`canonicalProduct_order_at_signed_level` proves, for $r>0$,
```math
\operatorname{ord}_{c+dr}D_q
=\operatorname{ord}_{c-dr}D_q
=\#\{n:q_n=r\}.
```
For $d\ne0$, the fiber is finite under the admissibility hypotheses. No simple-spectrum
assumption is made. For the full spectral enumeration, §4.49 identifies this
cardinality with the previously defined geometric eigenspace dimension.
The extensions in §§4.50–4.52 prove the oriented differences and
quantitative norm estimates between corresponding indexed points for the
same fixed $c,d$. Via an explicitly constructed zero-color matching tag
enumeration and uniqueness of complete monotone domain eigenbases, the
points are zeros of the full products and their orders agree with the
respective operators' geometric multiplicities. The first statement keeps
the absolute value of the real level difference until positivity is known.
The additional bounded-error zero certificates are described in §2.5.
A relative determinant identity, a complex operator spectral theorem and
finite-patch approximation estimates remain open.

### 2.5. Certified zero clusters from bounded operator error

Sections 4.53–4.56 give a quantitative certificate using **operator error**
and **spectral boundary margins**. Let $H=M_V+B$, $\widetilde H=H+K$ on the
same natural domain, with symmetric bounded $B,K$. Under the explicit properness,
onsite-ordering and summability assumptions, require
```math
\|K\|\le\eta<v_0-\|B\|,\qquad V\ge v_0.
```
Both complete ordered spectra exist, remain positive and inverse-square
summable, and satisfy
```math
|\lambda_i(\widetilde H)-\lambda_i(H)|\le\eta,
\qquad
|z_i^\pm(\widetilde H)-z_i^\pm(H)|\le |d|\eta.
```

Write $q_i=\lambda_i(H)$. A cut at energy $t$ and index $k$ is certified by
```math
k>0\ \Longrightarrow\ q_{k-1}+\eta<t,
\qquad t+\eta<q_k.
```
At $k=0$ only the second inequality is required. For a positive window
$0<a<b$, apply these finite checks at $(a,m)$ and $(b,n)$. For both operators,
the indices in $(a,b)$ are then exactly $m,\ldots,n-1$. On **each** reflected
segment $c\pm d[a,b]$, the finite set $Z^\pm$ consists of all product zeros,
the endpoints are zero-free, and
```math
\sum_{z\in Z^\pm}\operatorname{ord}_z D=n-m.
```
The sum is over distinct complex points, weighted by their exact analytic
orders, which are the respective operators' geometric multiplicities.
Repeated levels may split or merge inside the window. Empty windows are
included; the underlying full-spectrum sequence still requires infinitely
many sites. The certificate does not assert that every chosen window has
large enough boundary margins.

Compact-uniform convergence of products alone is not used to infer these
bounds. A finite-patch application must first supply a justified comparison
of operators or resolvents and an appropriate quantitative error certificate.
A finite matrix on a different Hilbert space does not automatically satisfy
the common-domain bounded-error hypothesis. Scalar local zero-location
and exact disk-count certificates are now proved in §2.6 under a strict
circular-boundary error. Noncircular contour counts and a finite-patch
error certificate require further work.

### 2.6. Scalar approximation near a multiple spectral zero

Sections 4.60–4.65 give a local certificate for an arbitrary analytic
approximant $g$ of a full spectral product $f=D_H$. At a zero $a$ with
finite positive order $m$, the formalization constructs $\rho,C>0$ such that
```math
|f(z)|\ge C|z-a|^m\qquad (|z-a|\le\rho).
```
The reference disk contains only the distinct zero $a$, with its full
multiplicity $m$. Suppose $g$ is analytic on a neighborhood of the closed
disk and, on its boundary,
```math
|g(z)-f(z)|\le\varepsilon,\qquad
\varepsilon\ge0,\qquad \varepsilon<C\rho^m.
```
Then $g$ has exactly $m$ zeros in the open disk **counting analytic
multiplicities**, has none on its boundary,
and every zero $z$ in the closed disk satisfies
```math
|z-a|^m\le\varepsilon/C,
\qquad |z-a|\le(\varepsilon/C)^{1/m}.
```
For the full spectral product, $m$ is the original geometric eigenspace
multiplicity. A linear location estimate is obtained when $m=1$; no
simple-spectrum assumption is imposed in the general result. The location
bound uses local analytic factorization and the maximum modulus principle;
the exact count uses the disk argument principle and Rouché's theorem.
The earlier existence/location theorem with $2\varepsilon<C\rho^m$
remains available unchanged in §4.60. An arbitrary approximant's zeros may
split and may lie off the prescribed line; their total order is conserved.

More generally, if $f,g$ are analytic near any closed disk of radius $R>0$
and $|g-f|<|f|$ on its circular boundary, their total interior zero orders
are equal (§§4.63–4.64). The strict inequality proves that neither function
vanishes on the boundary. The reference disk need not isolate a single
zero; zero-free disks and disks containing several distinct or repeated
zeros are covered. This statement concerns circular contours, not arbitrary
Jordan curves.

The scalar error can be certified from a finite product
$P_N=\prod_{n<N}(1-((z-c)/d)^2/q_n^2)$. For positive $q_n$ with
$S=\sum_nq_n^{-2}<\infty$, put $T_N=\sum_{k\ge0}q_{k+N}^{-2}$.
On any set with $|(z-c)/d|^2\le A$, $A\ge0$, the proved bound is
```math
|D_q(z)-P_N(z)|\le e^{AS}(e^{AT_N}-1).
```
The right side tends to zero; certified upper bounds for $S,T_N$ can
replace the infinite sums. An additional error $\eta$ in approximating
$P_N$ adds to this bound. The estimate remains valid at zeros of $P_N$
and includes $N=0$. With $\varepsilon=E_N(A)+\eta<C\rho^m$, §4.65
certifies the exact local count as well as the location bound. Since
$E_N(A)\to0$, every sufficiently long exact partial product has the full
local count; a numerical cutoff still requires a numerical tail bound.
These are truncations of one fixed spectral sequence. Neither a
finite-patch operator error nor numerical values for the local
constants $C,\rho$ are supplied by the abstract existence theorem.

Sections 4.66–4.67 now supply a worked numerical instance. For
$q_n=n+1$, $c=0$, $d=1$, $a=1$, the full onsite spectral product has an
explicit entire cofactor $G$ with $F(z)=(z-1)G(z)$ and
```math
|G(z)|\ge\frac15\quad (|z-1|\le\tfrac14),\qquad
\sum_nq_n^{-2}\le2,\qquad
\sum_{k\ge0}q_{k+N}^{-2}\le\frac1N\quad(N\ge1).
```
For any sequence with $q_n\ge n+1$, the existing error budget satisfies
$E_N(A)\le324/N$ when $0\le A\le2$ and $N\ge2$. On the displayed disk,
$A=25/16$, so every $N\ge16384$ gives $|F-P_N|\le1/50$.
If an analytic $g$ has boundary error $|g-P_N|\le1/100$, then
$|g-F|\le3/100<1/20=C\rho$. The proved certificate gives total zero
order **one**, no boundary zeros, and $|z-1|\le3/20$ for every zero
in the disk. The cutoff is sufficient, not asserted minimal. This is an
infinite diagonal operator on its natural domain, not a finite-patch or
a named tiling construction; the complete spectral identification is
proved in §4.67.

## 3. Finite-dimensional geometric operators

### 3.1. Symmetry under controlled perturbations

The first theorem about our geometric operator is formalized in **[`SpectralGeometry/FinitePerturbation.lean`](SpectralGeometry/FinitePerturbation.lean)** and checked by Lean.

**In simple terms:** imagine a finite collection of tiles. Each tile has its own energy, pairs of tiles interact with symmetric weights, and we add a perturbation matrix `P` whose influence is controlled by `ε`. If both the interaction weights and `P` are symmetric, **the complete matrix remains symmetric whatever real value we choose for `ε`**:

```math
w(t,u)=w(u,t),\quad P_{tu}=P_{ut}
\quad\Longrightarrow\quad
(H_{\varepsilon})_{tu}=(H_{\varepsilon})_{ut}
\quad\text{for every }\varepsilon\in\mathbb R.
```

The file also proves that setting `ε=0` recovers exactly the unperturbed geometric matrix. This is useful because real symmetric finite matrices have real eigenvalues, so changing a symmetric perturbation cannot destroy that structural feature.

**Scope of this module:** the verified theorem concerns a *finite* matrix; symmetry alone does not imply positive eigenvalues or any infinite-dimensional spectral conclusions. Later §§4.20–4.30 establish conditional self-adjointness, compact resolvent, and isolation and local finiteness of genuine real eigenvalues for the abstract infinite matching-family operator. Conditional real-spectrum enumeration with exact geometric multiplicities is established later in §§4.36–4.37, qualitative divergence in §4.38, and a positive real spectral gap under explicit assumptions in §4.39. Quantitative index-wise comparison and sufficient full-spectrum inverse-square summability are proved under the additional hypotheses in §§4.44–4.48.

### 3.2. Positivity under controlled perturbations

The next theorem is formalized in **[`SpectralGeometry/FinitePositiveEnergy.lean`](SpectralGeometry/FinitePositiveEnergy.lean)**. It concerns the *quadratic energy* of the very same finite matrix defined in the preceding file. For a state `ψ`, define:

```math
Q_M(\psi)=\sum_{t,u}\psi(t)\,M_{tu}\,\psi(u).
```

The formalized identity says that the perturbed energy separates exactly into two parts:

```math
Q_{H_\varepsilon}(\psi)=Q_{H_0}(\psi)+\varepsilon Q_P(\psi).
```

**In simple terms:** if the original geometric operator has nonnegative energy for every configuration, and the chosen perturbation also has nonnegative energy, then turning on that perturbation with `ε\ge0` cannot make the total energy negative:

```math
\bigl(Q_{H_0}(\psi)\ge0,\ Q_P(\psi)\ge0,\ \varepsilon\ge0\bigr)
\quad\Longrightarrow\quad Q_{H_\varepsilon}(\psi)\ge0.
```

The Lean file also proves that **strictly positive** base energy on every nonzero configuration stays strictly positive under the same assumptions. These results concern all tile-amplitude configurations, not a selection of eigenfunctions.

**Scope of the second result:** this finite-dimensional theorem proves *stability* of positivity, assuming positivity of the original and perturbation energies. The following section derives a sufficient condition for the original energy from the geometric inputs themselves. The distinct infinite-operator results, including conditional self-adjointness, compact resolvent and locally finite real point spectrum, are proved later in §§4.20–4.30. Under additional hypotheses, the full interacting real spectrum is subsequently enumerated with exact geometric multiplicities (§4.37) and its ordered eigenvalues are proved to tend to `+∞` (§4.38). Quantitative growth comparison and sufficient inverse-square summability are proved under the additional hypotheses in §§4.46–4.48.

### 3.3. Nonnegative energy from geometry

The third geometric result is developed in **[`SpectralGeometry/FiniteGeometricEnergy.lean`](SpectralGeometry/FiniteGeometricEnergy.lean)**. It answers the natural question left open by the previous section: *when do the tile energies and interaction weights themselves guarantee nonnegative energy?*

For a finite set of tiles, assume the individual energies are nonnegative, the pair weights are symmetric and nonnegative, and self-interaction weights vanish (`w(t,t)=0`, consistent with summing only over `u\ne t`). The quadratic energy of the unperturbed matrix can then be rewritten as a **sum of squares**:

```math
Q_{H_0}(\psi)=
\sum_t V(t)\psi(t)^2+
\frac12\sum_{t,u}w(t,u)\bigl(\psi(t)-\psi(u)\bigr)^2.
```

Each summand is nonnegative. Thus **the geometry alone forces `Q_{H_0}(\psi)\ge0` for every real tile-amplitude configuration**. The factor `1/2` compensates for counting each pair of distinct tiles in both directions.

Combining this with the preceding perturbation theorem also gives nonnegative energy for `H_\varepsilon=H_0+\varepsilon P` whenever `\varepsilon\ge0` and the quadratic energy of `P` is nonnegative.

**Scope:** this is a statement about finite quadratic forms. Nonnegative energy allows *zero* eigenvalues; it does not itself establish strictly positive eigenvalues, an infinite self-adjoint operator, compact resolvent, or the inverse-square spectral summability needed for the canonical product.

### 3.4. Strictly positive energies and eigenvalues

The next step is formalized in **[`SpectralGeometry/FiniteStrictPositivity.lean`](SpectralGeometry/FiniteStrictPositivity.lean)**. The preceding theorem ruled out *negative* quadratic energy, but still allowed energy equal to zero. Here we prove a sufficient condition that excludes zero for every nonzero configuration.

Assume **every tile has strictly positive individual energy** (`V(t)>0`), while interactions have symmetric nonnegative weights (`w(t,u)=w(u,t)\ge0`, with `w(t,t)=0`). Then the established sum-of-squares identity gives:

```math
\psi\ne0 \quad\Longrightarrow\quad
Q_{H_0}(\psi)=
\sum_t V(t)\psi(t)^2+
\frac12\sum_{t,u}w(t,u)(\psi(t)-\psi(u))^2>0.
```

**Why is it strictly positive?** For a nonzero configuration there is at least one tile where `\psi(t)\ne0`. Since `V(t)>0`, the individual-energy term for that tile is strictly positive, and every other term is nonnegative.

The same conclusion holds for the perturbed operator `H_\varepsilon=H_0+\varepsilon P` if `\varepsilon\ge0` and `Q_P(\psi)\ge0` for every configuration. The Lean file additionally proves the corresponding **real eigenvalue positivity**: for every real eigenpair `H_\varepsilon\psi=\lambda\psi` with `\psi\ne0`, we have `\lambda>0`. Indeed, on an eigenvector:

```math
Q_{H_\varepsilon}(\psi)=
\lambda\sum_t\psi(t)^2>0
\quad\Longrightarrow\quad \lambda>0.
```

Together with the **symmetry theorem** (when `P` is symmetric), this means every eigenvalue of the real symmetric *finite* perturbed matrix is strictly positive under these hypotheses.

**Scope:** the result is finite-dimensional; the hypothesis `V(t)>0` for every tile is sufficient, not necessarily optimal. This finite-dimensional theorem does not itself construct the infinite operator or establish a uniform gap across growing patches. The later abstract infinite-operator construction appears in §4; sufficient inverse-square summability for the interacting spectrum is proved in §4.48 under explicit growth, ordering and positive-gap hypotheses.

## 4. Infinite-dimensional geometric operators and spectral theory

### 4.1. Square-summable states and the natural operator domain

The next Lean module, **[`SpectralGeometry/InfiniteOnsite.lean`](SpectralGeometry/InfiniteOnsite.lean)**, begins the transition from finite matrices to an arbitrary, possibly infinite, set of tiles `T`.

A state now belongs to the real Hilbert space of square-summable tile amplitudes:

```math
\ell^2(T)=\left\{\psi:T\to\mathbb R:
\sum_{t\in T}|\psi(t)|^2<\infty\right\}.
```

There is an essential distinction from the finite case: a potential `V(t)` may grow without bound, so even when `\psi\in\ell^2(T)`, the pointwise product `V(t)\psi(t)` need not lie in `\ell^2(T)`. An operator must therefore have a **specified domain**. For the onsite (diagonal) contribution we choose its natural multiplication domain:

```math
D(V)=\left\{\psi\in\ell^2(T):t\mapsto V(t)\psi(t)\in\ell^2(T)\right\},
\qquad (M_V\psi)(t)=V(t)\psi(t).
```

The new Lean file proves that `D(V)` is a real **linear subspace**, constructs `M_V:D(V)\to\ell^2(T)` as a linear map, checks its value on each tile, and proves that when `V(t)\ge0`, each local energy contribution `\psi(t)(M_V\psi)(t)` is nonnegative. These facts require neither a finite number of tiles nor a bounded potential.

**Scope of this first infinite result:** only the individual-energy contribution is built here. The pair-interaction Laplacian `L_w` and the perturbation `\varepsilon P` are not yet included **in this first module**; §§4.6–4.9 subsequently construct infinite interactions. The density of `D(V)` is addressed in §4.2; §§4.20–4.30 establish conditional self-adjointness, compact resolvent, finite eigenspace dimension, and isolation and local finiteness of the full operator's genuine real eigenvalues. These later theorems require additional hypotheses and do not follow merely from defining the domain; conditional multiplicity-aware ordering and qualitative divergence of the full real spectrum are subsequently proved in §§4.37–4.38; quantitative indexed comparison and sufficient inverse-square summability are proved under the additional hypotheses in §§4.46–4.48.

### 4.2. Density of the natural operator domain

The new Lean module **[`SpectralGeometry/InfiniteOnsiteDensity.lean`](SpectralGeometry/InfiniteOnsiteDensity.lean)** establishes that the natural domain `D(V)` introduced in the previous section is **dense in `\ell^2(T)`**, even when the potential `V(t)` is unbounded and the set of tiles is infinite.

**The idea is simple:** switch on amplitudes at only finitely many tiles and leave all other amplitudes equal to zero. Every such finite-support configuration belongs to `D(V)`, because multiplying its finitely many nonzero amplitudes by real numbers `V(t)` still leaves finitely many nonzero amplitudes.

Any square-summable configuration can be approximated arbitrarily closely (in the `\ell^2` norm) by these finite-support configurations. Consequently:

```math
\overline{D(V)}=\ell^2(T).
```

This does **not** say `D(V)=\ell^2(T)`. It says every square-summable state can be approximated as accurately as desired by states on which the onsite operator is well-defined. Mathlib's convergent sum of `lp.single` states supplies the approximation theorem.

**Why it matters:** density is a crucial prerequisite for the Hilbert-space theory of adjoint and self-adjoint unbounded operators. It does *not*, by itself, establish self-adjointness, compact resolvent, a discrete infinite spectrum, or spectral summability. The infinite interaction operator and perturbation are constructed in later modules (§§4.6–4.9), not as consequences of density alone.

### 4.3. Point eigenvalues and positivity

The Lean module **[`SpectralGeometry/InfiniteOnsiteEigenvalues.lean`](SpectralGeometry/InfiniteOnsiteEigenvalues.lean)** studies which eigenvalues the densely defined multiplication operator `M_V` can have on an infinite tiling. No bound on `V` and no finiteness of the tile set are assumed.

**In simple terms:** suppose a nonzero state `ψ` is an eigenstate with eigenvalue `λ`. At each tile, the eigenvalue equation says

```math
V(t)\psi(t)=\lambda\psi(t).
```

Therefore, wherever the amplitude `ψ(t)` is nonzero, we must have **`λ=V(t)`**. Conversely, the amplitude must vanish at every tile where `V(t)\ne\lambda`. So a possible eigenstate is supported entirely on tiles with the same onsite energy. This is a property of the *diagonal* infinite operator, not a statement about the full interacting system.

The file formalizes this support restriction and two consequences:

- If every onsite energy satisfies `V(t)>0`, then **every eigenvalue with a nonzero eigenstate is strictly positive**: `λ>0`.
- If all energies satisfy the uniform lower bound `V(t)\ge c`, then every such eigenvalue satisfies `λ\ge c`.

**Scope and important limitation:** these are results about the *point spectrum* of the infinite onsite multiplication operator. They do not prove that the operator is self-adjoint, that every `V(t)` occurs as an eigenvalue, that the entire spectrum is positive or discrete, or that the inverse-square eigenvalue series converges. The subsequent §§4.6–4.9 construct interactions and bounded perturbations, while §§4.20–4.30 prove further conditional results for the full geometric operator `H_\varepsilon`, culminating in isolation and local finiteness of genuine real eigenvalues.

### 4.4. A sufficient growth condition for summable spectral levels

The Lean module **[`SpectralGeometry/InfiniteOnsiteSummability.lean`](SpectralGeometry/InfiniteOnsiteSummability.lean)** provides the next connection between an *infinite* diagonal geometric operator and the already formalized canonical product.

Suppose the tiles have been indexed by natural numbers, and assume their onsite energies grow at least linearly with this index:

```math
V(n)\ge n+1,\qquad n=0,1,2,\ldots.
```

Then each energy is positive, and the new theorem proves the crucial **inverse-square summability**:

```math
\sum_{n=0}^{\infty}\frac{1}{V(n)^2}<\infty.
```

**Why?** The inverse squares are nonnegative and bounded term by term by `1/(n+1)^2`, whose series is convergent. This makes `q_n=V(n)` an admissible sequence for the canonical-product results already checked in `CanonicalProduct.lean`. The new Lean file also proves that **each `V(n)` is a genuine eigenvalue of the diagonal onsite operator**, using a single-tile state as its eigenvector.

**Important limitations:** the linear growth condition is *assumed*, **not** derived from Penrose or any other tiling geometry. It depends on the chosen indexing and is sufficient rather than necessary. The result concerns the diagonal onsite operator alone; it does not establish self-adjointness, compact resolvent, or spectral estimates for the full interacting and perturbed operator `H_\varepsilon`. Nor does canonical-product admissibility identify the resulting zeros with those of the Riemann zeta function.

### 4.5. Power-law growth: the critical exponent one half

The Lean module **[`SpectralGeometry/InfiniteOnsitePowerGrowth.lean`](SpectralGeometry/InfiniteOnsitePowerGrowth.lean)** improves the linear-growth hypothesis in §4.4.

For tiles indexed by the natural numbers, assume the **onsite levels obey**

```math
V(n)\ge (n+1)^\alpha,\qquad \alpha>\frac12.
```

Even though the growth may be *slower than linear*, the formalized comparison with a convergent `p`-series proves

```math
\sum_{n=0}^\infty\frac{1}{V(n)^2}<\infty.
```

The file proves that these levels are positive and form an `Admissible` sequence for the already-verified canonical-product theory. **The threshold is sharp for exact power-law levels**: for `V(n)=(n+1)^α`, the same sum diverges when `α≤1/2`. Thus the theorem separates the *sufficient growth condition* from the critical boundary, rather than imposing linear growth unnecessarily.

**Scope:** indexing the tiles and assuming this lower bound are external modeling choices here; no Penrose, Pinwheel, or other aperiodic tiling has been proved to generate the prescribed growth. The converse divergence applies only to the exact power-law example, not to all sequences satisfying a weak lower bound. These are statements about the diagonal onsite spectrum and its analytic product, **not** self-adjointness or compact resolvent for the full interacting operator and **not** an identification with the Riemann zeta zeros.

### 4.6. Geometric interactions acting on infinite square-summable states

The Lean module **[`SpectralGeometry/InfiniteFiniteEdgeInteraction.lean`](SpectralGeometry/InfiniteFiniteEdgeInteraction.lean)** introduces genuine pairwise interaction operators on the infinite Hilbert space `ℓ²(T)`. For an edge joining tiles `a` and `b` with weight `w≥0`, its action is

```math
L_{a,b}\psi = w(\psi(a)-\psi(b))(\delta_a-\delta_b).
```

This state remains square-summable even when `T` is infinite: only two coordinates can be affected. Its exact quadratic energy is

```math
\langle \psi,L_{a,b}\psi\rangle
 = w(\psi(a)-\psi(b))^2\ge0.
```

The module proves that the edge operator is linear and symmetric, and that **any finite collection of these geometric edges** gives a well-defined symmetric, nonnegative interaction on infinite `ℓ²(T)`.

**Precise scope:** the ambient set of tiles may be infinite, but the number of active interaction edges in this first construction is **finite**. The genuinely infinite-edge Laplacian requires a convergence or uniform-weight hypothesis, addressed by later constructions in §§4.8–4.9. This finite-edge theorem does not model every edge of a particular Penrose or other aperiodic tiling.

### 4.7. Combining infinite onsite energies, interactions, and perturbations

The Lean module **[`SpectralGeometry/InfiniteBoundedPerturbation.lean`](SpectralGeometry/InfiniteBoundedPerturbation.lean)** combines the existing potentially unbounded onsite operator `M_V` with the finite-edge interaction operator and an **everywhere-defined bounded linear** perturbation `P`:

```math
H_\varepsilon\psi = M_V\psi+L_{E,w}\psi+\varepsilon P\psi,
\qquad \psi\in D(V).
```

All terms map the same state into `ℓ²(T)`; hence their sum is defined on the existing dense onsite domain `D(V)`. Lean formalizes the **exact decomposition of the full quadratic energy**. Assuming `V(t)≥0`, nonnegative active edge weights, `\langle\psi,P\psi\rangle≥0` and `\varepsilon≥0`, the combined energy is nonnegative. The combined operator is also symmetric if the perturbation is symmetric.

**Crucial distinction:** positivity *does* survive an operator sum when the three quadratic forms are well-defined and nonnegative on a shared domain (and the perturbation has the correct sign). However, **self-adjointness, compact resolvent, discrete spectrum, strict positivity and inverse-square spectral summability do not follow automatically from these componentwise hypotheses**. The `V(n)` growth results in §§4.4–4.5 concern the diagonal operator. Sections 4.46–4.48 now transfer their sufficient summability conditions to full interacting levels with explicit ordering, properness and positive-gap hypotheses.

### 4.8. Countably infinite geometric interactions with summable weights

The Lean module **[`SpectralGeometry/InfiniteSummableEdgeInteraction.lean`](SpectralGeometry/InfiniteSummableEdgeInteraction.lean)** removes the *finite number of edges* restriction in §§4.6–4.7 under a rigorous, explicit convergence hypothesis.

Suppose geometric edges are enumerated by natural numbers, with endpoints `(a_n,b_n)` and real weights `w_n`. Assume **absolute summability**:

```math
\sum_{n=0}^\infty |w_n|<\infty.
```

The edge vector is `v_n=δ_{a_n}-δ_{b_n}`. Since `||v_n||≤2`, each rank-one edge operator has norm at most `4|w_n|`. Therefore the **infinite series of operators converges in operator norm**, defining a bounded linear operator on all of `ℓ²(T)`:

```math
L_w=\sum_{n=0}^\infty w_n\lvert v_n\rangle\langle v_n\rvert.
```

If in addition every `w_n≥0`, the module proves the infinite operator is **symmetric and has nonnegative, finite quadratic energy** on every square-summable state. Lean also proves that the combined `M_V+L_w+εP` on the **original dense domain `D(V)`** is symmetric under symmetric `P` and nonnegative when `V≥0`, `w≥0`, `ε≥0`, and the bounded perturbation `P` has nonnegative quadratic energy.

**What is not claimed:** this is a sufficient `ℓ¹` condition on the *entire* edge list, not yet a bounded-degree local graph condition. Infinite tilings with uniformly bounded non-decaying weights typically have infinitely many edges and do not satisfy `∑|w_n|<∞`. The matching-family construction in §4.9 addresses a different infinite-edge model; the subsequent §§4.20–4.22 prove compact resolvent and self-adjointness for that model under explicit hypotheses. This summable-edge module alone establishes neither those results nor full-spectrum inverse-square summability.

### 4.9. Bounded-degree local interactions from infinite matching families

The Lean modules **[`SpectralGeometry/InfiniteLocalMatching.lean`](SpectralGeometry/InfiniteLocalMatching.lean)** and **[`SpectralGeometry/InfiniteLocalBoundedDegree.lean`](SpectralGeometry/InfiniteLocalBoundedDegree.lean)** introduce a genuinely infinite set of interacting edges without imposing the global summability of their weights.

In this *matching-colorable* model, each of the `D` colors specifies an involutive bijection `σᵢ:T≃T`; it connects every tile to at most one tile of that color. Thus every tile has at most `D` candidate neighbors. The color has a single nonnegative constant weight `wᵢ≤W`. The corresponding matching operator acts by

```math
(L_i\psi)(t)=\psi(t)-\psi(\sigma_i(t)),
\quad
L_w=\sum_{i=1}^{D} w_iL_i.
```

Even though each color may cover infinitely many edges of fixed nonzero weight, `L_w` acts on all of `ℓ²(T)`. The formalized results show that the norm satisfies

```math
\|L_w\|\le 2DW,
```

that all nonnegative matching weights give **nonnegative, finite quadratic energy**, and that involutive matchings make the operator **symmetric**. The same module combines `L_w` with the possibly unbounded onsite operator and a bounded perturbation on their common dense domain `D(V)`, obtaining conditional positivity and symmetry of the *total* operator.

**Scope:** this is an important subclass of uniformly bounded-degree graphs: those described by finitely many involutive matching permutations with a constant weight per color. We have **not** proved that arbitrary locally finite graphs (including a specific Penrose adjacency graph) have been represented this way; tile-dependent edge weights and general graph decompositions require additional work. Symmetry and positivity still do **not** establish self-adjointness, compact resolvent, or inverse-square summability of the full spectrum.

### 4.10. Lower bounds on point eigenvalues of infinite local operators

The Lean module **[`SpectralGeometry/InfiniteLocalEigenvalueBounds.lean`](SpectralGeometry/InfiniteLocalEigenvalueBounds.lean)** studies point eigenvalues of the **full infinite local matching model** introduced in §4.9, including the unbounded onsite term, infinitely many local interactions (represented by finitely many involutive matching colors), and a bounded perturbation.

Suppose the onsite potential is nonnegative (`V(t)≥0`), the matching weights are nonnegative (`wᵢ≥0`), and the bounded perturbation `P` has nonnegative quadratic energy. For `ε≥0`, every nonzero eigenstate of the combined operator has a **nonnegative eigenvalue**:

```math
H_\varepsilon\psi=\lambda\psi,\quad\psi\ne0
\quad\Longrightarrow\quad \lambda\ge0.
```

The proof uses the nonnegative total quadratic energy established in §4.9 and the eigenvector identity `⟨ψ,Hεψ⟩=λ‖ψ‖²`. It does **not** presuppose an eigenbasis or a discrete spectrum.

A particularly transparent way to obtain a **strict positive lower bound** is a uniform scalar (identity) perturbation `P=I`. With `V≥0` and `wᵢ≥0`, any existing point eigenvalue obeys, for **every real** `ε`,

```math
H_\varepsilon=M_V+L_w+\varepsilon I,\qquad
H_\varepsilon\psi=\lambda\psi,\ \psi\ne0
\quad\Longrightarrow\quad \lambda\ge\varepsilon.
```

Indeed, the onsite and interaction quadratic energies are nonnegative, so `(λ-ε)‖ψ‖²≥0`. If `ε>0`, every point eigenvalue is **strictly positive**. This bound holds without absolute summability of all edge weights and without bounding `V` from above.

**Scope:** these theorems constrain eigenvalues *if nonzero eigenvectors exist*; they do not by themselves establish spectral completeness or exclude continuous spectrum. Subsequent §§4.20–4.30 prove conditional self-adjointness and compact resolvent, density of genuine eigenvectors, and isolation and bounded-interval finiteness of distinct real eigenvalues. Section 4.32 subsequently establishes the real bounded-inverse spectral-mapping theorem for the unbounded operator; complex-spectrum formalization remains open. Section 4.48 proves sufficient full-spectrum inverse-square summability and admissibility for the existing canonical product.

### 4.11. Stable spectral lower bounds under signed bounded perturbations

The Lean module **[`SpectralGeometry/InfiniteLocalSignedPerturbationGap.lean`](SpectralGeometry/InfiniteLocalSignedPerturbationGap.lean)** extends §4.10 to a **bounded perturbation of arbitrary sign**. We no longer assume that its quadratic energy is nonnegative, nor that the coupling parameter is positive.

For a bounded real-linear perturbation `P` and a square-summable state `ψ`, the operator norm controls its quadratic energy:

```math
\left|\langle\psi,P\psi\rangle\right|
\le \|P\|\,\|\psi\|^2.
```

Assume nonnegative onsite energies `V(t)≥0` and nonnegative matching weights `wᵢ≥0`. Whenever a **nonzero** state in the natural onsite domain is a real eigenvector of the full operator `H_ε=M_V+L_w+εP`, Lean now proves:

```math
H_\varepsilon\psi=\lambda\psi,\quad \psi\ne 0
\quad\Longrightarrow\quad
\lambda\ge -|\varepsilon|\,\|P\|.
```

Thus an arbitrary signed bounded perturbation can lower a **real point eigenvalue** by at most `|ε|‖P‖` relative to the zero lower bound supplied by the nonnegative onsite-plus-matching quadratic energy.

To obtain a positive gap, the file also defines the independently shifted operator

```math
H_{\varepsilon,m}=M_V+L_w+\varepsilon P+mI.
```

Every real point eigenvalue obeys the **quantitative lower bound**

```math
\lambda\ge m-|\varepsilon|\,\|P\|.
```

In particular, when `m>|ε|‖P‖`, **every existing real point eigenvalue is strictly positive**. This generalizes the identity-only shift of §4.10: `P` may now be a non-positive or nonsymmetric bounded operator, and `ε` may have either sign.

**Precise scope:** these are estimates on **real point eigenvalues**, assuming a nonzero eigenvector exists. Without symmetry of `P`, no claim that the operator has only real spectrum is made. The theorems do **not** establish self-adjointness, the existence of eigenvalues, compact resolvent, absence of continuous spectrum, discreteness, or the inverse-square summability needed for the canonical product.

### 4.12. Coercive energy and residual gap for infinite local operators

The Lean module **[`SpectralGeometry/InfiniteLocalCoerciveGap.lean`](SpectralGeometry/InfiniteLocalCoerciveGap.lean)** strengthens the point-eigenvalue results of §§4.10–4.11. Instead of making a statement only **if an eigenvector exists**, it proves a bound on **every state in the natural domain** `D(V)` of the complete infinite local matching operator.

Continue to assume nonnegative onsite energies `V(t)≥0` and nonnegative constant matching weights `wᵢ≥0`. Let `P` be an arbitrary bounded real-linear perturbation, with no positivity or symmetry assumption, and let `ε,m∈ℝ`. For

```math
H_{\varepsilon,m}=M_V+L_w+\varepsilon P+mI
```

the formalized **quadratic-form lower bound** is

```math
\langle\psi,H_{\varepsilon,m}\psi\rangle
\ge \left(m-|\varepsilon|\|P\|\right)\|\psi\|^2
\qquad(\psi\in D(V)).
```

Set `g=m-|ε|‖P‖`. For **every real** trial spectral parameter `a`, Lean also proves the quantitative **residual norm bound**

```math
\left\|(H_{\varepsilon,m}-aI)\psi\right\|
\ge (g-a)\|\psi\|
\qquad(\psi\in D(V)).
```

If `a<g`, the right-hand coefficient is strictly positive. Therefore the equation `Hψ=aψ` has **only the zero solution**. Even more strongly, for every unit-norm domain state we have `‖Hψ-aψ‖≥g-a>0`: there cannot be a sequence of normalized domain states whose residual tends to zero at such a real `a`.

**Why this advances the project:** §4.11 controlled only real point eigenvalues. The new estimate controls *all* admissible states and excludes both exact and approximate real eigenvectors below an explicit threshold, without assuming a discrete spectral decomposition.

**Essential limitation:** injectivity and a lower norm bound for `H-aI` do **not** by themselves prove surjectivity or an everywhere-defined inverse. Without appropriate self-adjointness or further range arguments, we do not claim `a` is outside the full spectrum or that there is a compact resolvent. Neither a complete real spectrum, eigenvalue existence, spectral discreteness, inverse-square summability, nor any geometric model of a particular aperiodic tiling has yet been established by this module.

### 4.13. Graph-norm control for infinite local operators

The Lean module **[`SpectralGeometry/InfiniteLocalGraphNorm.lean`](SpectralGeometry/InfiniteLocalGraphNorm.lean)** prepares the next analytic question, **closedness** of the full operator on its natural domain, by quantifying how the unbounded onsite operator and its bounded local corrections compare.

Write, as before,

```math
H_{\varepsilon,m}=M_V+L_w+\varepsilon P+mI,\qquad
\psi\in D(V).
```

Although the onsite energy `V` may be unbounded, the infinite matching Laplacian `L_w` is a bounded operator on all of `ℓ²(T)`, as is `P`. Let

```math
C=\|L_w\|+|\varepsilon|\|P\|+|m|.
```

Lean proves that the full operator differs from the onsite operator by a **uniformly bounded correction**:

```math
\|(H_{\varepsilon,m}-M_V)\psi\|\le C\|\psi\|.
```

The resulting two-sided **graph estimates** are:

```math
\|H_{\varepsilon,m}\psi\|\le\|M_V\psi\|+C\|\psi\|,
\qquad
\|M_V\psi\|\le\|H_{\varepsilon,m}\psi\|+C\|\psi\|.
```

For `D` matching colors with nonnegative weights `wᵢ≤W` and `W≥0`, the earlier geometric estimate `‖L_w‖≤2DW` gives the explicit bound

```math
\|M_V\psi\|\le\|H_{\varepsilon,m}\psi\|
+(2DW+|\varepsilon|\|P\|+|m|)\|\psi\|.
```

**Interpretation:** the bounded interactions and perturbations cannot change the size of the unbounded part in an uncontrolled way. The natural domain stays `D(V)`, and the graph measurements of `M_V` and `H_{\varepsilon,m}` control one another quantitatively. These statements require no positivity assumption on `V`, and no positivity or symmetry assumption on `P`.

**Scope:** this module establishes explicit norm comparisons, not closedness, self-adjointness, surjectivity, compact resolvent, discreteness of spectrum, or eigenvalue summability. Closedness of the natural onsite operator and of its boundedly perturbed counterpart is established separately in §4.14.

### 4.14. Closed graphs of the onsite and full infinite local operators

The Lean module **[`SpectralGeometry/InfiniteLocalClosedGraph.lean`](SpectralGeometry/InfiniteLocalClosedGraph.lean)** establishes a first genuine **closed-operator** property, building on the graph-norm estimates of §4.13.

The onsite operator `M_V` is multiplication by an arbitrary real onsite potential `V(t)`, possibly unbounded. Its natural domain is

```math
D(V)=\{\psi\in\ell^2(T): V\psi\in\ell^2(T)\}.
```

The module proves that the graph

```math
G(M_V)=\{(\psi,M_V\psi):\psi\in D(V)\}
\subseteq\ell^2(T)\times\ell^2(T)
```

is **closed**. Informally, whenever the inputs `ψₙ` converge in `ℓ²` and their outputs `M_V ψₙ` also converge in `ℓ²`, the limiting input is still in the natural domain, and the limiting output equals the onsite operator applied to it. The proof identifies the graph with the coordinatewise equations `η(t)=V(t)ψ(t)`; each coordinate evaluation on `ℓ²` is continuous, so these simultaneous equations define a closed set.

The interaction Laplacian built from finitely many matching colors is a **bounded** operator, as is any bounded linear perturbation `P` and the identity shift. Therefore, for

```math
H_{\varepsilon,m}=M_V+L_w+\varepsilon P+mI
\quad\text{on }D(V),
```

the graph `G(H_{\varepsilon,m})` is also **closed**. The proof is explicit: subtracting the bounded correction `B=L_w+εP+mI` from the output of a graph pair reduces it to a pair in `G(M_V)`. This subtraction is continuous.

No nonnegativity of `V`, matching weights or `P` is needed for closedness, and no symmetry of `P` is assumed. The matching-family representation remains the same special class of infinite local interactions as in §4.9.

**Scope:** closedness is **not the same as self-adjointness**. This module alone does not establish an adjoint equality, a bounded or compact resolvent, spectral discreteness, or inverse-square summability. Self-adjointness is subsequently proved in §4.22, compact resolvent under explicit hypotheses in §§4.20–4.21, and isolation and local finiteness of genuine real eigenvalues in §§4.29–4.30. Full real bounded-inverse spectral mapping is subsequently established in §4.32; a complex-spectrum extension remains open, while §4.48 proves sufficient full-spectrum inverse-square summability under its additional hypotheses.

### 4.15. Explicit adjoint characterization and self-adjointness criterion

The Lean module **[`SpectralGeometry/InfiniteLocalAdjointCharacterization.lean`](SpectralGeometry/InfiniteLocalAdjointCharacterization.lean)** begins the self-adjointness stage by characterizing **exactly which input-output pairs satisfy the adjoint pairing identity** for the densely defined operator on its natural domain `D(V)`.

For a real Hilbert-space operator `A`, a pair of square-summable states `(η,χ)` is an *adjoint pair* when

```math
\langle A\varphi,\eta\rangle=\langle\varphi,\chi\rangle
\quad\text{for every }\varphi\in D(V).
```

The module first shows that, for onsite multiplication `M_V` by an arbitrary real potential (even if unbounded), this identity holds **if and only if** `η∈D(V)` and `χ=M_Vη`. The key proof tests the identity on states concentrated on a single tile, forcing the coordinatewise equation `χ(t)=V(t)η(t)`. Because `χ∈ℓ²`, this also forces `η` into the natural onsite domain. The reverse implication uses the previously proved symmetry of onsite multiplication.

For the **complete infinite local matching operator**

```math
H_{\varepsilon,m}=M_V+L_w+\varepsilon P+mI
```

the analogous characterization is established assuming **involutive matching permutations** and **a symmetric bounded perturbation `P`**. Under these conditions its bounded correction `B=L_w+εP+mI` is symmetric, so an adjoint-pair identity for `H` reduces to one for `M_V` with output `χ-Bη`. The result is

```math
\bigl[\ \langle H\varphi,\eta\rangle
=\langle\varphi,\chi\rangle\ \ \forall\varphi\in D(V)\ \bigr]
\iff
\bigl[\ \eta\in D(V),\ \chi=H\eta\ \bigr].
```

Combined with the independently formalized **density of `D(V)`** (§4.2) and **closedness** (§4.14), this is a mathematically explicit **adjoint-domain equality**, the defining substance of self-adjointness for these real densely defined operators. Unlike symmetry alone, it excludes additional adjoint-domain states.

**Technical scope:** the proof states the full adjoint-pair characterization directly rather than packaging it as a Mathlib `UnboundedLinearOperator`/`IsSelfAdjoint` API instance. This does **not** establish compact resolvent, discrete spectrum, eigenvalue existence, inverse-square summability, or a particular tiling graph. The conclusion for the full operator requires the symmetry hypotheses on the matching permutations and `P`; it is not asserted for arbitrary nonsymmetric perturbations.

### 4.16. Solving a real shifted onsite resolvent equation

The Lean module **[`SpectralGeometry/InfiniteOnsiteResolvent.lean`](SpectralGeometry/InfiniteOnsiteResolvent.lean)** starts the constructive resolvent program. §4.15 established an explicit adjoint-pair characterization for the onsite and symmetric interacting operators; here we obtain **existence and uniqueness** of solutions to a shifted onsite operator equation, rather than only spectral inequalities or adjoint information.

Take an arbitrary real onsite potential `V:T→ℝ`, which may be unbounded above, and a real parameter `a` such that **every onsite energy is at least one unit above** `a`:

```math
V(t)-a\ge 1\qquad\text{for all tiles }t.
```

For **every** input `f∈ℓ²(T)`, Lean proves there exists exactly one `ψ∈D(V)` solving

```math
(M_V-aI)\psi=f,\qquad
\psi(t)=\frac{f(t)}{V(t)-a}.
```

The proof shows that the coordinatewise inverse gives a square-summable state because `|(V(t)-a)^{-1}|≤1`. It then checks that `Vψ=f+aψ` is square-summable, so the solution lies in the **natural unbounded onsite domain**. A separate injectivity argument proves that distinct domain states cannot have the same image, giving bijectivity.

**What this establishes:** the shifted **onsite** operator `M_V-aI : D(V)→ℓ²(T)` is a bijection under the explicit unit-gap assumption, with a concrete coordinate formula for its inverse. This is a genuine solvability statement, stronger than merely excluding real point eigenvalues.

**Relation to subsequent results:** this module establishes bijectivity and the coordinate formula, but does not itself package the inverse as a continuous linear map. The bounded inverse and its compactness are established in §§4.18–4.19. Sections 4.20–4.21 subsequently prove two-sided invertibility of a shifted **interacting** operator and compactness of its resolvent under explicit hypotheses; §§4.29–4.30 establish isolation and local finiteness of genuine real eigenvalues. Section 4.32 establishes spectral mapping for the full real bounded-inverse spectrum. Its complex extension remains open (§6.1). Section 4.70 applies the real operator theory to the octagonal vertex graph. Sufficient full-spectrum inverse-square summability is proved separately in §4.48. The one-unit condition is a convenient sufficient hypothesis, not a necessary one.

### 4.17. Finite low-energy sectors under a proper onsite potential

The Lean module **[`SpectralGeometry/InfiniteOnsiteFiniteLowEnergy.lean`](SpectralGeometry/InfiniteOnsiteFiniteLowEnergy.lean)** makes explicit an important growth hypothesis for the *diagonal onsite operator* `M_V`: for any fixed energy threshold `R`, there are only finitely many tiles with `V(t)≤R`.

Lean proves two consequences on the natural onsite domain: any genuine point eigenvector with real eigenvalue `λ≤R` can be nonzero only on those finitely many low-energy tiles, and only finitely many **distinct onsite point eigenvalues** can lie at or below `R`. These follow from the previously proved coordinate identity `λ=V(t)` whenever an eigenvector is nonzero at tile `t`.

The hypothesis of finite low-energy sublevel sets is a precise form of *onsite potential growth at infinity*. It is additional to previous results and is **not claimed for an arbitrary potential or automatically for a particular geometric tiling**.

**Important scope:** these results concern `M_V`, **not the fully interacting operator** `H=M_V+L_w+εP+mI`. On their own they do not prove compact resolvent, spectral discreteness, inverse-square summability, or eigenvalue existence for an arbitrary potential. The finite-rank approximation and compact onsite resolvent are proved in §4.18 under the additional unit-gap assumption. A compact resolvent for the **interacting** operator is subsequently proved in §§4.20–4.21, and local finiteness of genuine real eigenvalues in §4.30. Quantitative onsite comparison and sufficient inverse-square summability for the interacting spectrum are proved in §§4.46–4.48 under explicit additional hypotheses.

### 4.18. Compact resolvent of a proper onsite potential

The Lean module **[`SpectralGeometry/InfiniteOnsiteCompactResolvent.lean`](SpectralGeometry/InfiniteOnsiteCompactResolvent.lean)** packages the inverse of the shifted diagonal onsite operator as a continuous linear map on real `ℓ²(T)`. It then uses the finite-low-energy property of §4.17 to prove compactness.

Fix a real shift `a` and assume both the **uniform gap** `V(t)-a≥1` for every tile and **properness of the onsite potential**: every sublevel set `{t | V(t)≤R}` is finite. The inverse furnished by §4.16 acts coordinatewise as

```math
(R_a f)(t)=\frac{f(t)}{V(t)-a}.
```

For each natural number `n`, truncate to the finite set `S_n={t | V(t)≤a+n+1}`. The corresponding operator `R_{a,n}` has finite rank and is compact, while the discarded coefficients satisfy the explicit operator-norm estimate

```math
\|R_a-R_{a,n}\|\le \frac{1}{n+1}.
```

The finite truncations thus converge to `R_a` in operator norm. Since compact operators are closed under operator-norm limits, **`R_a` is compact**.

**Scope:** this is a compact-resolvent theorem only for diagonal onsite multiplication under an additional, explicitly assumed growth condition. It does not prove compactness of the full interacting and perturbed operator, any property of an actual aperiodic tiling, or inverse-square summability of the resulting eigenvalues. Compact resolvent by itself is insufficient to guarantee the summability required for the canonical product.

### 4.19. The bounded onsite resolvent is the shifted inverse on its natural domain

The Lean module **[`SpectralGeometry/InfiniteOnsiteResolventIdentity.lean`](SpectralGeometry/InfiniteOnsiteResolventIdentity.lean)** connects the bounded continuous resolvent constructed in §4.18 to the unbounded onsite multiplication operator of §4.1 and the bijectivity theorem of §4.16.

Under the unit-gap hypothesis `1≤V(t)-a`, let `R_a` be the coordinatewise bounded operator from §4.18. Lean proves that **for every** `f∈ℓ²(T)` the state `R_a f` belongs to the natural domain `D(V)` and satisfies

```math
R_a f\in D(V),\qquad (M_V-aI)(R_a f)=f.
```

Conversely, **for every** `ψ∈D(V)`, Lean proves the other inverse identity:

```math
R_a\bigl((M_V-aI)\psi\bigr)=\psi.
```

Thus the bounded continuous map is explicitly shown to be the **two-sided inverse of the shifted onsite operator on its actual natural domain**, rather than merely a map with the expected coordinate formula. Combined with §4.18, proper onsite potential growth makes this genuine inverse compact.

**Scope:** this completes the onsite inverse-identification argument without introducing any new potential-growth hypothesis. By itself it does **not** establish invertibility or compact resolvent of the full interacting operator `H=M_V+L_w+εP+mI`; those conditional results are subsequently proved in §§4.20–4.21.

### 4.20. Compact resolvent under small bounded interactions and perturbations

The Lean module **[`SpectralGeometry/InfiniteLocalCompactResolvent.lean`](SpectralGeometry/InfiniteLocalCompactResolvent.lean)** transfers the compact onsite resolvent of §§4.18–4.19 to an operator with a bounded correction. Let `B:ℓ²(T)→ℓ²(T)` be a continuous linear map and let

```math
H=M_V+B\quad\text{on }D(V),\qquad
R_a=(M_V-aI)^{-1}.
```

Assume the unit gap `V(t)-a≥1`, finite onsite sublevel sets as in §4.18, and the quantitative **smallness condition** `‖B R_a‖<1`. Neumann-series invertibility of `I+B R_a` provides

```math
(H-aI)^{-1}=R_a(I+B R_a)^{-1}.
```

The module constructs this expression as a continuous linear map, shows that its outputs belong to `D(V)`, proves both inverse identities for the **full** shifted operator, and proves its compactness by composition with the compact onsite resolvent.

The result applies to any bounded correction satisfying the stated condition, in particular to the finite-color matching-family interaction with a bounded controlled perturbation encoded by `B=L_w+εP+mI`. It does **not** claim that `‖B R_a‖<1` holds automatically for arbitrary coupling strengths or at an arbitrary spectral shift. Compactness alone does not imply the quantitative inverse-square eigenvalue estimate. The subsequent §§4.23–4.30 derive spectral completeness, finite-dimensional eigenspaces, and isolation and local finiteness of genuine real eigenvalues under additional hypotheses; the complete **real** spectral mapping is subsequently proved in §4.32, while a complex-spectrum extension remains open, while §4.48 proves sufficient full-spectrum inverse-square summability under its additional hypotheses.

### 4.21. Quantitative compact-resolvent bounds and sufficiently negative shifts

The Lean module **[`SpectralGeometry/InfiniteLocalCompactResolventBounds.lean`](SpectralGeometry/InfiniteLocalCompactResolventBounds.lean)** strengthens the conditional compact-inverse theorem of §4.20. If a positive gap `δ` satisfies `V(t)-a≥δ>0` and the earlier unit-gap condition holds, it establishes the **operator norm estimate**

```math
\|R_a\|\le\delta^{-1}.
```

For any bounded correction `B` with `‖B‖<δ`, the product estimate implies `‖B R_a‖<1`; consequently, the inverse of `M_V+B-aI` exists on the natural onsite domain and is compact under the same finite-sublevel hypothesis as §4.18.

**No global smallness assumption is needed to find one resolvent point.** If `V(t)≥v₀` for all tiles, then choosing `δ=‖B‖+1` and `a=v₀-δ` supplies a real shift with compact inverse for *any fixed bounded B*. This proves existence of **some sufficiently negative real resolvent point**, not invertibility at all spectral parameters.

For the finite-color matching-family model from §4.9, with `D` matching colors and weights `0≤wᵢ≤W`, the formalized geometric bound is

```math
\|L_w+\varepsilon P+mI\|
 \le 2DW+|\varepsilon|\,\|P\|+|m|.
```

Thus `V(t)-a≥δ≥1` and `δ>2DW+|ε|‖P‖+|m|` suffice for the compact shifted inverse of the actual local matching operator via its already-proved bounded-correction identity. Neither symmetry of `P` nor a fixed small coupling is required for this existence result. With the additional symmetry assumptions, §4.22 proves self-adjointness, §4.27 proves density of genuine eigenvectors, and §§4.29–4.30 establish isolation and local finiteness of distinct real eigenvalues. Full real bounded-inverse spectral mapping is subsequently proved in §4.32. Conditional ordering with exact geometric multiplicities and qualitative divergence are subsequently established in §§4.36–4.38. The complex-spectrum extension remains an open P2 objective. Quantitative ordered-level comparison and sufficient inverse-square summability are proved under the additional hypotheses in §§4.44–4.48.

### 4.22. Self-adjoint onsite and infinite local operators in Mathlib's partial-operator API

The Lean module **[`SpectralGeometry/InfiniteLocalSelfAdjointPMap.lean`](SpectralGeometry/InfiniteLocalSelfAdjointPMap.lean)** bridges the explicit natural-domain operators and adjoint-pair characterizations of §§4.14–4.15 to Mathlib's **`LinearPMap`** type for partially defined (potentially unbounded) linear operators.

The module first packages onsite multiplication `M_V` as a `LinearPMap` with domain `D(V)`. It then combines density of `D(V)` with the previously proved adjoint-pair equivalence to establish

```math
M_V^*=M_V
```

in the precise sense of Mathlib's `IsSelfAdjoint` predicate for `LinearPMap`. Thus the conclusion is no longer solely an explicit characterization of possible adjoint pairs.

For the complete infinite local matching operator

```math
H_{\varepsilon,m}=M_V+L_w+\varepsilon P+mI
\quad\text{on }D(V),
```

the same argument proves `IsSelfAdjoint` for its `LinearPMap` representation when each matching permutation is involutive and the bounded perturbation `P` is symmetric. A reusable graph-and-pairing lemma identifies the adjoint graph with the original graph, using Mathlib's `LinearPMap.adjoint_graph_eq_graph_adjoint`. **The actual domain remains `D(V)`; it is not silently replaced by all of `ℓ²(T)`.**

**Scope:** this establishes the operator-theoretic interface needed before applying later spectral results. It requires the stated symmetry assumptions for the full local operator and makes no claim about compactness without the properness/gap hypotheses of §§4.20–4.21. The later §4.25 proves finite-dimensional full-operator eigenspaces under compact-resolvent hypotheses, while §4.29 proves isolation of nonzero real spectral points of the compact bounded resolvent. Section 4.30 subsequently establishes isolation and bounded-interval finiteness for **genuine full-operator real eigenvalues**. Section 4.32 subsequently characterizes the complete **real bounded-inverse spectrum** on the natural domain. Conditional multiplicity-aware ordering and qualitative divergence are proved later (§§4.36–4.38); the complex-spectrum extension remains open. Quantitative ordered-level comparison and sufficient inverse-square summability are proved under the additional hypotheses in §§4.44–4.48.

### 4.23. Compact self-adjoint resolvents and their eigenspaces

The Lean module **[`SpectralGeometry/InfiniteLocalResolventSpectrum.lean`](SpectralGeometry/InfiniteLocalResolventSpectrum.lean)** begins the P2 spectral stage by applying Mathlib's compact self-adjoint spectral results to the **bounded resolvent** of the interacting operator. Let `H=M_V+B` on the natural domain `D(V)`; assume the shifted inverse `R_a=(H-aI)⁻¹` is constructed as in §§4.20–4.21, and that the bounded correction `B` is symmetric.

The new module proves that `R_a` is self-adjoint as a continuous linear map, using the two inverse identities from §4.20 and symmetry on `D(V)`. Under the finite-sublevel hypothesis on `V`, `R_a` is also compact. Mathlib's compact-operator results then imply:

- **Finite eigenspace dimension:** for every nonzero real eigenvalue `μ` of `R_a`, its eigenspace is finite-dimensional.
- **Spectral totality:** the orthogonal complement of the supremum of all eigenspaces of `R_a` is zero. Equivalently, their linear span is dense in the real Hilbert space.
- **Local matching specialization:** if each matching permutation is involutive and the bounded perturbation `P` is symmetric, the corrected geometric resolvent is self-adjoint whenever the explicit Neumann condition is satisfied. The gap bounds of §4.21 provide sufficient conditions for its existence.

**Important distinction:** these are formalized properties of the **compact bounded resolvent**. Section 4.24 separately transfers nonzero resolvent eigenpairs to eigenpairs of the unbounded operator `H` via `λ=a+μ⁻¹`; §4.29 subsequently proves isolation of nonzero real spectral points of the compact resolvent. Section 4.30 also isolates genuine full-operator real eigenvalues and proves that only finitely many distinct eigenvalues occur in each bounded interval. The complete **real bounded-inverse spectrum** is subsequently characterized in §4.32. Later §§4.36–4.38 establish conditional multiplicity-aware ordering and qualitative divergence for the full real spectrum. A full complex-spectrum extension remains open. Sections 4.46–4.48 prove quantitative onsite comparison and sufficient full-spectrum inverse-square summability under their additional hypotheses.

### 4.24. Eigenpair correspondence between the compact resolvent and the full operator

The Lean module **[`SpectralGeometry/InfiniteLocalEigenpairCorrespondence.lean`](SpectralGeometry/InfiniteLocalEigenpairCorrespondence.lean)** connects the spectral statements about the **bounded** resolvent in §4.23 to genuine eigenvectors of the **unbounded** geometric operator on its natural domain. Let `R_a=(M_V+B-aI)⁻¹` denote the two-sided inverse constructed in §4.20, with its original norm-smallness and unit-gap hypotheses. For each **nonzero** real `μ` and state `f∈ℓ²(T)`, Lean proves the equivalence

```math
R_a f=\mu f\quad\Longleftrightarrow\quad
\exists\,\psi\in D(V):\ \psi=f,\quad
(M_V+B-aI)\psi=\mu^{-1}f.
```

In the forward direction, the domain witness is constructed explicitly from the resolvent applied to `μ⁻¹ f`. Consequently, every resolvent eigenvector with nonzero eigenvalue belongs to the natural domain. Conversely, the already formalized left-inverse identity recovers the bounded-resolvent eigenvector equation.

For the complete finite-color matching operator `H=M_V+L_w+εP+mI`, the corresponding Lean theorem gives

```math
R_a f=\mu f\quad\Longleftrightarrow\quad
\exists\,\psi\in D(V):\ \psi=f,\quad
H\psi=(a+\mu^{-1})f.
```

An additional formulation starts with an arbitrary real `λ≠a` and uses `μ=(λ-a)⁻¹`. For nonzero `f`, these are genuine eigenpairs. The correspondence itself is algebraic and does **not** require the bounded correction to be symmetric; the compact self-adjoint spectral conclusions of §4.23 still require their own properness and symmetry hypotheses.

**Scope:** the eigenpair correspondence at a fixed resolvent shift is now formalized. Subsequent §4.30 transfers resolvent isolation to the full operator's **real point spectrum**, including finiteness of distinct eigenvalues on bounded intervals. The subsequent §4.32 identifies the full **real bounded-inverse spectrum** of the unbounded operator. Conditional ordering with exact multiplicities and qualitative divergence are established in §§4.36–4.38. The complex-resolvent interface remains open (§6.1). Quantitative comparison and sufficient full-spectrum summability are proved under the additional hypotheses in §§4.44–4.48.

### 4.25. Finite multiplicity and orthogonality of full local eigenvectors

The Lean module **[`SpectralGeometry/InfiniteLocalFullEigenspaces.lean`](SpectralGeometry/InfiniteLocalFullEigenspaces.lean)** transfers the finite-dimensional eigenspace result of §4.23 from the compact bounded resolvent to the **unbounded full local operator**, using the eigenpair correspondence of §4.24. For a spectral parameter `a` where the inverse exists, each real eigenvalue `λ≠a` has a well-defined full eigenspace, realized by the resolvent eigenspace at `(λ-a)⁻¹`.

The module identifies membership in this submodule with the actual domain-restricted eigenvalue equation for `H=M_V+L_w+εP+mI` on `D(V)`. Assuming finite sublevel sets for the onsite potential and the existing resolvent smallness condition, it proves that **each such full eigenspace is finite-dimensional**. It also shows that `a` itself cannot be an eigenvalue, because the full shifted operator has a two-sided inverse. Thus the finite-multiplicity statement covers all real eigenvalues of `H`.

Under involutive matching permutations and symmetry of the bounded perturbation `P`, eigenvectors corresponding to **different real eigenvalues are orthogonal**. This orthogonality theorem is an operator-symmetry consequence and does not need the extra compactness hypotheses.

**Scope:** finite-dimensional eigenspaces and orthogonality alone do not imply isolation. Section 4.30 uses the additional compact-resolvent spectral isolation from §4.29 to establish isolation and bounded-interval finiteness of **genuine full-operator eigenvalues**. Section 4.32 later identifies the full **real bounded-inverse spectrum** with the point spectrum under explicit hypotheses, and §4.33 introduces unordered multiplicity tags. Conditional ordered enumeration with exact multiplicities is established in §§4.36–4.37 and divergence in §4.38. The complex-resolvent interface remains open (§6.1). Quantitative comparison and sufficient full-spectrum summability are proved under the additional hypotheses in §§4.44–4.48.

### 4.26. Fredholm spectral exhaustion for the nonzero local resolvent spectrum

The Lean module **[`SpectralGeometry/InfiniteLocalFredholmSpectralExhaustion.lean`](SpectralGeometry/InfiniteLocalFredholmSpectralExhaustion.lean)** makes a first rigorous spectral-exhaustion statement using Mathlib's **Fredholm alternative for compact operators**. Let `H=M_V+L_w+εP+mI` on its natural domain `D(V)`, and suppose the resolvent `R_a=(H-aI)⁻¹` exists and is compact under the already formalized onsite-gap, finite-sublevel and Neumann-smallness hypotheses.

For every real `μ≠0`, the module proves the following equivalence, where the spectrum on the left is the standard **bounded-operator spectrum in Mathlib**:

```math
\mu\in\sigma(R_a)
\quad\Longleftrightarrow\quad
\exists\,\psi\in D(V)\setminus\{0\}:
H\psi=(a+\mu^{-1})\psi.
```

Equivalently, for a real parameter `λ≠a`, the transformed value `(λ-a)⁻¹` belongs to the resolvent spectrum **if and only if** `λ` admits a nonzero eigenvector of the unbounded full local operator. The forward implication uses Fredholm's alternative; the reverse implication uses the two-sided inverse and the eigenpair correspondence from §4.24. **No symmetry hypothesis is needed** for this compact-operator spectral-point/eigenpair equivalence.

**Precise scope:** the proof exhausts the **nonzero spectrum of the compact bounded resolvent**, not the full spectrum of the unbounded `LinearPMap` by a separate spectral-mapping theorem. The special point `0` of the compact resolvent spectrum is deliberately excluded from this correspondence. Section 4.29 subsequently proves that the nonzero real spectral points of the compact resolvent are isolated and that zero is their only possible accumulation point. Section 4.30 further isolates the actual full-operator real eigenvalues and rules out finite accumulation. Section 4.32 subsequently characterizes the complete **real bounded-inverse spectrum** on the natural domain. Conditional ordered enumeration with exact multiplicities is established in §§4.36–4.37 and divergence in §4.38. The complex-resolvent interface remains open (§6.1). Quantitative comparison and sufficient full-spectrum summability are proved under the additional hypotheses in §§4.44–4.48.

### 4.27. Completeness of genuine eigenvectors of the full infinite local operator

The Lean module **[`SpectralGeometry/InfiniteLocalFullEigenvectorsComplete.lean`](SpectralGeometry/InfiniteLocalFullEigenvectorsComplete.lean)** proves the strong **eigenvector completeness** consequence of compact self-adjoint resolvent for the *unbounded full matching-family operator* `H=M_V+L_w+εP+mI` on its unchanged natural domain `D(V)`.

First, the resolvent `R_a=(H-aI)⁻¹` has **trivial kernel**, because its constructed natural-domain solution satisfies the explicit right-inverse equation (§4.20). Thus its zero eigenspace is the zero subspace, and the complete compact self-adjoint spectral theorem from §4.23 implies that the eigenspaces of `R_a` with **nonzero** real eigenvalues alone span a dense subspace of `ℓ²(T)`.

Second, by the eigenpair correspondence of §4.24, every nonzero resolvent eigenvalue `μ` gives a real full-operator eigenvalue `λ=a+μ⁻¹` and exactly the same eigenspace, now interpreted as natural-domain eigenvectors. Lean proves that the orthogonal complement of the supremum of these **actual full local eigenspaces**, indexed by real `λ≠a`, is `⊥`. Equivalently, the linear span of all such full-operator eigenvectors is dense in the Hilbert space.

This result requires the existing compactness conditions (onsite finite sublevels, the unit gap and the Neumann smallness condition), involutive matchings and symmetry of the bounded perturbation. It is stronger than merely stating that the resolvent has complete eigenvectors; it directly packages the genuine unbounded operator's natural-domain eigenvectors as a total family.

**Scope:** the complete eigenvector family need not yet be enumerated or ordered. Dense eigenvector span alone does **not** establish that finite full-operator eigenvalues are isolated, that there are no finite spectral accumulation points, or any spectral growth or inverse-square summability estimate. Section 4.30 subsequently establishes isolation and no finite accumulation for genuine real eigenvalues. Conditional ordering with exact multiplicities and qualitative divergence are established in §§4.36–4.38. Quantitative comparison and sufficient full-spectrum inverse-square summability are proved under the additional hypotheses in §§4.44–4.48.

### 4.28. A resolvent-norm exclusion zone for full-operator eigenvalues

The Lean module **[`SpectralGeometry/InfiniteLocalResolventNormGap.lean`](SpectralGeometry/InfiniteLocalResolventNormGap.lean)** adds a quantitative consequence of the Fredholm spectral correspondence from §4.26. Fix a real shift `a` for which the full matching-family operator `H` has a bounded compact resolvent `R_a=(H-aI)⁻¹`, under the same onsite gap, finite-sublevel and Neumann-smallness assumptions as before.

If a nonzero state in the natural domain is a full-operator eigenvector at a real eigenvalue `λ≠a`, the reciprocal `(λ-a)⁻¹` belongs to the spectrum of the bounded resolvent (§4.26). Mathlib's norm bound on the spectrum therefore gives

```math
\left|\frac{1}{\lambda-a}\right|\le\|R_a\|\,\|I\|.
```

The module also formalizes the contrapositive: whenever `λ≠a` and `|(λ-a)⁻¹|>‖R_a‖‖I‖`, every natural-domain solution of `Hψ=λψ` is zero. Here `I` is the identity operator on `ℓ²(T)`. Its norm is one on a nonzero Hilbert space; the Lean statement retains the factor `‖I‖` to avoid requiring a nontrivial-space instance when the tile type can be empty. This excludes genuine eigenvalues from a quantitative neighborhood of the **chosen resolvent shift**. It does not require the symmetry assumptions used for self-adjoint spectral completeness.

**Precise scope:** the result isolates the selected resolvent shift from point eigenvalues with an explicit norm test. It does **not** prove that each full-operator eigenvalue is isolated from other eigenvalues, that the entire unbounded spectrum is exhausted by eigenvalues, that the spectrum can be ordered, or that inverse-square summability holds. Section 4.30 subsequently establishes isolation and bounded-interval finiteness for genuine full-operator real eigenvalues, and §4.32 identifies the complete **real bounded-inverse spectrum**. Conditional ordered enumeration with exact multiplicities and qualitative divergence are established in §§4.36–4.38. The complex-resolvent interface remains open (§6.1); sufficient full-spectrum summability is proved separately in §4.48.

### 4.29. Isolation of nonzero points in the compact resolvent spectrum

The Lean module **[`SpectralGeometry/InfiniteLocalResolventSpectralIsolation.lean`](SpectralGeometry/InfiniteLocalResolventSpectralIsolation.lean)** establishes the P2 isolation result for the **bounded compact resolvent**. Assume the onsite gap, finite onsite sublevel sets, and Neumann-smallness condition already used for `R_a=(H-aI)⁻¹`. Assume also that the bounded correction is symmetric, making `R_a` self-adjoint.

The key intermediate result says that for each `δ>0` there are **only finitely many distinct real spectral values** satisfying `|μ|≥δ`:

```math
\#\{\mu\in\sigma_{\mathbb R}(R_a):|\mu|\ge\delta\}<\infty
\qquad(\delta>0).
```

The proof uses compactness: an infinite family of distinct eigenvalues bounded away from zero would produce infinitely many orthogonal unit eigenvectors, whose images under the compact operator remain uniformly separated, contradicting sequential compactness. Fredholm's alternative turns the eigenvalue statement into one about the full **real bounded-operator spectrum**.

Consequently, **every nonzero real spectral point is isolated**. More precisely, if `μ≠0` and `μ∈σ_ℝ(R_a)`, there exists `r>0` such that

```math
\nu\in\sigma_{\mathbb R}(R_a),\quad |\nu-\mu|<r
\quad\Longrightarrow\quad \nu=\mu.
```

In particular, **zero is the only possible accumulation point** of the real spectrum of the compact resolvent. The module does not require a nonempty tile type or an infinite-dimensional Hilbert space.

**Scope:** this finishes the bounded-resolvent isolation milestone. The following §4.30 transfers it via `λ=a+μ⁻¹` to **genuine real eigenvalues** of the unbounded operator. The subsequent §4.32 establishes real bounded-inverse spectral mapping on the natural domain; conditional ordering with exact multiplicities and qualitative divergence are established in §§4.36–4.38. The complex-resolvent interface remains open (§6.1); the quantitative observation, comparison and finite-sector response results are proved in §§4.41–4.48.

### 4.30. Isolation and local finiteness of genuine full-operator eigenvalues

The Lean module **[`SpectralGeometry/InfiniteLocalFullEigenvalueIsolation.lean`](SpectralGeometry/InfiniteLocalFullEigenvalueIsolation.lean)** transfers the compact-resolvent spectral results of §4.29 to the actual **real point spectrum** of the unbounded matching-family operator `H=M_V+L_w+εP+mI` on its unchanged natural domain `D(V)`.

Write `Eig(H)` for the set of real parameters `λ` for which there is a **nonzero** `ψ∈D(V)` with `Hψ=λψ`. Under the earlier unit onsite gap at `a`, finite onsite sublevel sets, Neumann smallness, involutive matchings, and symmetry of `P`, the module proves:

- **Pointwise isolation:** for each `λ∈Eig(H)`, there exists `r>0` such that every `ν∈Eig(H)` with `|ν−λ|<r` satisfies `ν=λ`. Unlike §4.28, this concerns *every* genuine eigenvalue, not just the selected shift.
- **Finiteness in bounded intervals:** for every `M≥0`, the set `{λ∈Eig(H) : |λ|≤M}` is finite. Thus distinct genuine real eigenvalues have **no finite accumulation point**, even at a real parameter that is not itself an eigenvalue.

The transfer uses the existing equivalence `λ∈Eig(H) ↔ (λ−a)⁻¹∈σ_ℝ(R_a)` for `λ≠a` (§4.26). The already-checked two-sided inverse excludes `a` as an eigenvalue (§4.25). Continuity and injectivity of `λ↦(λ−a)⁻¹` yield isolation, while bounded `|λ|` ensures the corresponding resolvent spectral parameters remain uniformly away from zero, so §4.29 gives finiteness.

**Precise scope:** these results by themselves identify properties of the **real point spectrum**; the subsequent §4.32 defines and characterizes the full **real bounded-inverse spectrum** on the same natural domain. Local finiteness counts **distinct eigenvalues**, not multiplicities. The next §4.31 proves countability and constructs a complete, possibly repeating listing of these real eigenvalues when nonempty. Ordered enumeration **with exact geometric multiplicities** and qualitative divergence are proved separately in §§4.36–4.38. Quantitative eigenvalue comparison and sufficient inverse-square summability are proved under the additional hypotheses in §§4.44–4.48.

### 4.31. Countability and a complete (unordered) listing of full-operator eigenvalues

The Lean module **[`SpectralGeometry/InfiniteLocalFullEigenvalueEnumeration.lean`](SpectralGeometry/InfiniteLocalFullEigenvalueEnumeration.lean)** builds on the bounded-interval finiteness theorem from §4.30. Under the same explicit compact self-adjoint resolvent hypotheses (onsite gap, finite onsite sublevel sets, Neumann-small correction, involutive matchings, and symmetric perturbation), the set `Eig(H)` of **genuine real eigenvalues of the full operator on `D(V)`** is **countable**:

```math
\operatorname{Eig}(H)=\bigcup_{n\in\mathbb N}
\{\lambda\in\operatorname{Eig}(H):|\lambda|\le n\},
\qquad
\#\{\lambda\in\operatorname{Eig}(H):|\lambda|\le n\}<\infty.
```

If `Eig(H)` is **nonempty**, Lean also constructs a sequence `e : ℕ → ℝ` whose range is **exactly** `Eig(H)`. This works whether the underlying tile type or the point spectrum is finite or infinite: **repetitions are allowed** in the sequence, so a finite nonempty point spectrum is handled correctly. No eigenvalue-existence assertion is made for arbitrary tile types; an empty point spectrum is countable but has no real-valued sequence with exactly that range.

**Scope:** this is a full *set-theoretic listing* of the real **point spectrum**, not a classification of the whole unbounded `LinearPMap` spectrum. The sequence is not asserted increasing or injective and **does not record eigenspace multiplicities**. The project has already proved finite-dimensional eigenspaces (§4.25). The following §4.32 formalizes the **full real bounded-inverse spectral mapping** on the natural domain; conditional ordering **with exact geometric multiplicities** and qualitative divergence are proved later in §§4.36–4.38, while the complex-spectrum extension remains open (§6.1). Quantitative eigenvalue growth and inverse-square summability do not follow from countability alone; §§4.44–4.48 supply the necessary variational bridge and sufficient growth/positivity hypotheses.

### 4.32. The full real bounded-inverse spectrum on the natural domain

The Lean module **[`SpectralGeometry/InfiniteLocalFullRealResolvent.lean`](SpectralGeometry/InfiniteLocalFullRealResolvent.lean)** goes beyond eigenpair correspondence (§4.26) and constructs actual bounded inverse operators for **arbitrary real spectral shifts** of `H=M_V+B` with the original domain `D(V)`. Here `B` is any bounded real-linear correction; the existing matching-family model is recovered by taking `B=L_w+εP+mI`.

Define a real *regular point* `b` by the existence of a bounded linear `Q_b : ℓ²(T) → ℓ²(T)` satisfying all three conditions: every `Q_b f` lies in `D(V)`, `(H-bI)Q_b f=f` for every input `f`, and `Q_b(H-bI)ψ=ψ` for every `ψ∈D(V)`. The **full real bounded-inverse spectrum** is the complement of this regular-point set. This is a definition based on two-sided bounded invertibility, **not a renaming of the eigenvalue set**.

Suppose a real shift `a` has the previously checked bounded inverse `R_a=(H-aI)⁻¹`, under the unit-gap and Neumann-smallness assumptions, and the onsite potential has finite sublevel sets so `R_a` is compact. On the natural domain Lean proves

```math
(H-bI)=(I-(b-a)R_a)(H-aI).
```

Whenever `I-(b-a)R_a` is invertible in the bounded-operator algebra, a new inverse exists:

```math
Q_b=R_a\,(I-(b-a)R_a)^{-1}.
```

It maps back into `D(V)` and satisfies **both** inverse identities. Compactness and Fredholm's alternative then establish, for `b≠a`, the precise equivalence

```math
b\in\sigma_{\mathrm{real}}(H)
\quad\Longleftrightarrow\quad
(b-a)^{-1}\in\sigma_{\mathbb R}(R_a).
```

The known shift `a` itself lies in the regular set. Unlike §4.26, the left-hand notion concerns **failure of a bounded inverse for the entire shifted unbounded operator**, including surjectivity and the original domain condition; it is not limited to a nonzero eigenpair test.

For the **actual matching-family operator** `H=M_V+L_w+εP+mI`, combining this mapping with the earlier compact-operator Fredholm theorem (§4.26) also proves **real spectral exhaustion**:

```math
b\in\sigma_{\mathrm{real}}(H)
\quad\Longleftrightarrow\quad
\exists\,\psi\in D(V)\setminus\{0\}:H\psi=b\psi.
```

This includes `b=a`, excluded from both sides by the previously checked inverse. The statement requires compactness of the shifted resolvent, but **not self-adjointness**: it rules out additional real bounded-inverse spectral points that are not eigenvalues under these hypotheses.

**Precise scope:** this is a complete **real bounded-inverse spectral mapping** theorem for the natural-domain operator, under the explicit compact-resolvent assumptions. The project has not yet formalized the analogous full **complex** spectrum or a Mathlib-native spectrum API for unbounded `LinearPMap` operators. Conditional ordering **with exact geometric multiplicities** and qualitative divergence are established later in §§4.36–4.38; §4.39 also proves a positive real spectral gap under explicit assumptions. Quantitative ordered-eigenvalue comparison and sufficient inverse-square summability are proved under the additional hypotheses in §§4.44–4.48.

### 4.33. Countable eigenvalue enumeration with eigenspace multiplicity tags

The Lean module **[`SpectralGeometry/InfiniteLocalFullEigenvalueMultiplicity.lean`](SpectralGeometry/InfiniteLocalFullEigenvalueMultiplicity.lean)** extends the unordered real point-spectrum listing in §4.31. It defines the **geometric multiplicity** `m(λ)` as the finite rank of the full eigenspace from §4.25 when `λ ≠ a`; the known regular resolvent shift `a` is assigned multiplicity zero. Finite dimensionality depends on the stated properness and compact-resolvent hypotheses.

The module then defines the **multiplicity-tagged real point spectrum** as pairs `(λ, k)` such that `λ` is a genuine eigenvalue and `k < m(λ)`. Under the existing symmetry and compactness assumptions it proves that this tagged set is **countable**, and, **if nonempty**, has a sequence with exactly that set as its range.

**Precise limit:** a range-exact sequence may repeat the same tag arbitrarily; it is **not** an injective or ordered enumeration. The next §4.34 proves the missing positive-multiplicity and exact-coverage statements. Multiplicity-aware global ordering is established separately in §4.37 and qualitative divergence in §4.38; quantitative onsite comparison and sufficient inverse-square summability for the full interacting operator are proved under the additional hypotheses in §§4.44–4.48.

### 4.34. Positive geometric multiplicity and exact tagged-spectrum coverage

The Lean module **[`SpectralGeometry/InfiniteLocalFullEigenvalueMultiplicityCoverage.lean`](SpectralGeometry/InfiniteLocalFullEigenvalueMultiplicityCoverage.lean)** resolves the next P2 milestone following §4.33, using the existing full-operator eigenspaces and compact-resolvent hypotheses (§§4.24–4.25).

For the full natural-domain matching-family operator `H = M_V + L_w + εP + mI` and the §4.33 multiplicity `m(λ)`, it proves the **equivalence**:

```math
\lambda\in\operatorname{Eig}(H)\quad\Longleftrightarrow\quad m(\lambda)>0.
```

The proof separately treats the known resolvent shift `a`, which is excluded from the point spectrum by the existing two-sided inverse and has multiplicity zero. For every `λ ≠ a`, the eigenspace membership theorem (§4.25) equates a genuine nonzero natural-domain eigenvector with a nonzero vector in the corresponding finite-dimensional submodule; the finite-dimensional `finrank` criterion then yields `m(λ)>0`. **No symmetry assumption is needed for this equivalence** beyond the explicit hypotheses needed to construct the compact resolvent and the finite-dimensional eigenspaces.

Writing `Tags(H) = {(λ,k) : λ ∈ Eig(H), k < m(λ)}`, the module additionally proves

```math
\lambda\in\operatorname{Eig}(H)
\quad\Longleftrightarrow\quad
\exists k\in\mathbb N:(\lambda,k)\in\operatorname{Tags}(H),
\qquad
\operatorname{fst}(\operatorname{Tags}(H))=\operatorname{Eig}(H).
```

These are **unconditional in spectrum nonemptiness**: they also hold when both sets are empty. Together with §4.33, the tagged set is countable under the stated symmetry and compactness hypotheses and covers every genuine real eigenvalue.

**Scope:** these theorems concern the real point spectrum and its finite geometric eigenspace dimensions. This module does **not itself** build an injective, increasing, multiplicity-aware eigenvalue sequence; §4.37 subsequently constructs one under explicit lower-bound and infinitude hypotheses, and §4.38 proves qualitative divergence. No result about the full complex unbounded spectrum, quantitative eigenvalue comparison, full-operator inverse-square summability or a concrete aperiodic tiling follows here.

### 4.35. Completeness indexed by the full real bounded-inverse spectrum

The Lean module **[`SpectralGeometry/InfiniteLocalFullRealSpectralCompleteness.lean`](SpectralGeometry/InfiniteLocalFullRealSpectralCompleteness.lean)** closes the **real self-adjoint completeness alternative** in the P2 spectral-notion/completeness milestone, combining the earlier eigenspace totality (§4.27), intrinsic real bounded-inverse spectrum (§4.32), and positive geometric multiplicity (§4.34).

With the previously defined complete real bounded-inverse spectrum `σ_real(H)` and geometric multiplicity `m(λ)`, it proves

```math
\lambda\in\sigma_{\mathrm{real}}(H)\quad\Longleftrightarrow\quad m(\lambda)>0,
\qquad
\sigma_{\mathrm{real}}(H)
=\operatorname{fst}(\operatorname{Tags}(H)).
```

These two exact spectral identities require the same onsite-gap, properness and resolvent-smallness hypotheses as the preceding real spectral-exhaustion and multiplicity results, but **not** self-adjointness.

For the full matching-family operator with an **additional symmetric bounded correction** (involutive matchings and a symmetric `P`), Mathlib's compact self-adjoint resolvent theorem also yields a **spectrally indexed completeness statement**. If `E_\lambda` denotes the genuine full eigenspace at `λ`, then

```math
\left(\bigvee_{\lambda\in\sigma_{\mathrm{real}}(H)}E_\lambda\right)^\perp
=\{0\}.
```

The Lean version explicitly excludes the designated resolvent shift `a` in its index type; the previously proved two-sided inverse shows `a\notin\sigma_{\mathrm{real}}(H)`, so **no real spectral point is discarded**. The proof removes regular parameters from the dense family of §4.27 by showing their full eigenspaces are trivial; it then transfers density to the family indexed solely by actual real spectral points. This is **density of the linear span**, not a claim that the algebraic span is closed.

**Limitations:** these are results for the **real** bounded-inverse spectrum of the actual natural-domain operator, not a formal complex spectral theorem or a naturally indexed eigenbasis. Conditional ordering with exact multiplicities is established in §§4.36–4.37 and qualitative divergence in §4.38. Sections 4.44–4.48 subsequently construct complete tagged eigenbases and prove quantitative comparison, finite-sector spectral response and sufficient full-spectrum inverse-square summability. The complex-resolvent interface for the analytic response program remains open in §6.1.

### 4.36. Ordered finite spectral windows with exact multiplicity tags

The Lean module **[`SpectralGeometry/InfiniteLocalFullOrderedMultiplicityWindows.lean`](SpectralGeometry/InfiniteLocalFullOrderedMultiplicityWindows.lean)** begins the P2 milestone of ordered enumeration by combining **local finiteness of distinct eigenvalues** (§4.30) with **finite geometric eigenspace dimensions and exact tag coverage** (§§4.33–4.34).

For any radius `M ≥ 0`, it proves that the set

```math
T_M=\{(\lambda,k):\lambda\in\operatorname{Eig}(H),\
|\lambda|\le M,\ 0\le k<m(\lambda)\}
```

is **finite** under the same explicit onsite gap, properness, resolvent-smallness, and symmetry hypotheses as the local-finiteness theorem. The finite-fiber argument itself needs no symmetry: it uses the finite number of distinct eigenvalues in the window and the finite rank of each eigenspace.

More strongly, Lean constructs a **finite list** whose members are **exactly** the tags in `T_M`, **without repetitions**, ordered by lexicographic order: first by increasing `λ`, then by increasing copy index `k` when eigenvalues coincide. This preserves exactly the admissible multiplicity labels of each included eigenvalue; arbitrary duplicate entries are excluded by the proof's `Nodup` condition.

A separate theorem handles an **entire finite real point spectrum**, yielding a globally sorted finite tagged list, including the empty-spectrum case. This is conditional on finiteness of the real point spectrum; it is not a claim that every infinite tiling has only finitely many eigenvalues.

**Precise limit:** the ordered lists are finite on each bounded window or on an already finite spectrum. The module does **not** yet construct a coherent, globally indexed `ℕ → ℝ` eigenvalue sequence for an **infinite** spectrum, prove that the global spectrum is bounded below, or establish `λₙ → +∞`. The global infinite-spectrum enumeration under explicit lower-bound and infinitude hypotheses is subsequently proved in §4.37, and qualitative divergence to `+∞` in §4.38. Quantitative onsite comparison and sufficient inverse-square summability are proved under the additional hypotheses in §§4.44–4.48; the complex-spectrum interface remains open (§6.1).

### 4.37. Globally ordered infinite spectrum with exact geometric multiplicities

The Lean module **[`SpectralGeometry/InfiniteLocalFullGlobalOrderedEnumeration.lean`](SpectralGeometry/InfiniteLocalFullGlobalOrderedEnumeration.lean)** completes the **global-infinite enumeration** subgoal of P2, extending the finite ordered windows of §4.36.

First, it proves a general order-theoretic lemma: **every infinite linear order in which every strict initial segment is finite has a strictly increasing, surjective sequence indexed by ℕ**. The argument assigns to each element its finite number of predecessors; these ranks form an infinite subset of ℕ, whose canonical increasing enumeration can be pulled back injectively and surjectively to the original order.

For the full interacting matching-family operator, assume the previous onsite-gap, finite onsite-sublevel, resolvent-smallness and symmetry hypotheses. In addition, explicitly assume **a real lower bound** `L` for every genuine eigenvalue and **infinitude of the multiplicity-tag set**. Under these hypotheses, each lexicographic initial segment of the tagged spectrum is finite: any preceding tag has eigenvalue in the bounded interval from `L` up to the selected eigenvalue, and §4.36 controls every bounded spectral window *including multiplicities*.

Lean then constructs a **globally strictly increasing sequence of tags**:

```math
t:\mathbb{N}\to\operatorname{Tags}(H),\qquad
t_0<_{\rm lex}t_1<_{\rm lex}\cdots,\qquad
\{t_n:n\in\mathbb N\}=\operatorname{Tags}(H).
```

Writing `λₙ=(t_n)_1` yields a **nondecreasing sequence of real full-operator eigenvalues**. More precisely, the formalized exact-multiplicity assertion ensures

```math
\exists!\,n\in\mathbb{N}:\ t_n=(\lambda,k)
\quad\Longleftrightarrow\quad
\lambda\in\operatorname{Eig}(H)\ \land\ 0\le k<m(\lambda).
```

Consequently each real eigenvalue occurs precisely as often as its **finite geometric eigenspace dimension**, rather than merely being included in an unordered set-theoretic range. This does not follow from countability alone; the key additional ingredients are local finiteness, lower boundedness, and infinitude.

**Precise scope:** the hypotheses of lower boundedness and infinite spectrum are explicit, not inferred for all possible geometric models. Empty and finite spectra are handled separately by §4.36. The theorem concerns the *real* full interacting point/bounded-inverse spectrum, not the unformalized complex spectrum. **Divergence `λₙ→+∞` is proved in §4.38; quantitative comparison with onsite levels and sufficient inverse-square summability are proved under the additional hypotheses in §§4.44–4.48.** Sections 4.68–4.70 verify the hypotheses for the octagonal vertex graph. A proof of its aperiodicity remains open (§6.4).

### 4.38. Divergence to +∞ of the globally ordered full real spectrum

The Lean module **[`SpectralGeometry/InfiniteLocalFullOrderedEigenvalueDivergence.lean`](SpectralGeometry/InfiniteLocalFullOrderedEigenvalueDivergence.lean)** completes the divergence milestone in P2 after the exact multiplicity-aware global enumeration of §4.37.

First, an abstract filter lemma proves that a real sequence `f : ℕ → ℝ` converges to `+∞` whenever, for every real `B`, only finitely many indices satisfy `f(n) < B`. The proof uses the equality of the cofinite filter and `atTop` on the natural numbers; monotonicity is not required by this standalone criterion.

For the **full interacting matching-family operator**, suppose the onsite gap, finite onsite-sublevel, resolvent-smallness, and symmetry assumptions of §§4.30–4.37 hold. Additionally, assume a **uniform real lower bound** on all genuine eigenvalues and take an **injective global enumeration of the exact multiplicity tags** from §4.37. For any threshold `B`, all indexed tags below `B` lie in a bounded window of radius `|L|+|B|`. Section 4.36 proves that this window contains finitely many tags, **counting geometric multiplicities**. Injectivity of the tag enumeration therefore gives a finite set of such indices.

Lean establishes the full limit in the filter formulation:

```math
\operatorname{Tendsto}(\lambda_n,\operatorname{atTop},\operatorname{atTop}),
\qquad \lambda_n=(t_n)_1,
```

equivalently, `λₙ → +∞`. It also proves an existence theorem combining a **strictly increasing, range-exact global enumeration of tags** with divergence of the projected real eigenvalues. With §4.37, each eigenvalue is represented **exactly as many times as its finite geometric eigenspace dimension**.

**Scope:** the assumptions that the tagged spectrum is infinite and the real eigenvalues are bounded below are explicit and are **not** established here for every geometric potential. A limit of `+∞` is a **qualitative** result: it does not imply a polynomial growth rate, a positive spectral gap, or `∑ₙ λₙ⁻² < ∞`. Sections 4.44–4.48 now prove sufficient quantitative comparison and summability conditions for the full operator. They also derive infinite tag sets from infinite site types in the proper symmetric setting. These conclusions concern the real spectrum. Section 4.70 constructs the ordered spectrum for the octagonal vertex graph.

### 4.39. Variational comparison and uniform real spectral gap for the full operator

The Lean module **[`SpectralGeometry/InfiniteLocalFullVariationalComparison.lean`](SpectralGeometry/InfiniteLocalFullVariationalComparison.lean)** begins the quantitative P2 comparison program using the actual **full interacting operator** `H = M_V + B`, where `B=L_w+\varepsilon P+mI` is bounded and the possibly unbounded multiplication operator `M_V` retains its natural domain `D(V)`.

**Quadratic-form comparison.** For every state `ψ ∈ D(V)`, the full quadratic energy differs from the onsite quadratic energy by at most

```math
\big|\langle\psi,H\psi\rangle-\langle\psi,M_V\psi\rangle\big|
\le \|B\|\,\|\psi\|^2.
```

In particular, `\langle\psi,M_V\psi\rangle-\|B\|\|\psi\|^2
\le\langle\psi,H\psi\rangle
\le\langle\psi,M_V\psi\rangle+\|B\|\|\psi\|^2`. This uses the **norm of the total correction**, not only the norm of `P`. It holds on the common domain **without** symmetry or positivity assumptions on `B`.

**Full real spectrum, not just point eigenvalues.** If `V(t)\ge c` for every tile, the onsite quadratic form is at least `c\|\psi\|^2`. Hence every genuine real eigenvalue of `H` satisfies `\lambda\ge c-\|B\|`. Under the previously verified compact-resolvent/real spectral-exhaustion hypotheses (§4.32), this bound extends to the **entire real bounded-inverse spectrum**, not only eigenvectors selected in advance. In particular, the sufficient condition `c>\|B\|` yields the **uniform positive real spectral gap** `\lambda\ge c-\|B\|>0`.

**Scope and subsequent use:** this module proves the variational **form inequality**. The multiplicity-aware min–max principle and its bridge to the §4.37 enumeration are now proved in §§4.44–4.45, yielding the index-wise comparison `\lambda_n(H)\ge\lambda_n(M_V)-\|B\|` in §4.46. Sufficient full-spectrum summability is derived in §4.48 with additional growth and positivity hypotheses. Section 4.70 applies the comparison to the octagonal graph. The complex-spectrum interface remains a separate goal (§6.1).

### 4.40. Low-energy coordinate injection and eigenspace multiplicity counting

The Lean module **[`SpectralGeometry/InfiniteLocalFullLowEnergyCounting.lean`](SpectralGeometry/InfiniteLocalFullLowEnergyCounting.lean)** advances the P2 min–max/counting program using the **full natural-domain interacting operator** `H=M_V+B` and the sharp variational estimate from §4.39.

For any real threshold `R` and any `ψ∈D(V)` that vanishes on every tile where `V(t)<R`, it proves the high-energy quadratic-form bound

```math
\langle\psi,H\psi\rangle\ge (R-\|B\|)\,\|\psi\|^2.
```

Consequently, every **nonzero** eigenvector of `H` with `\lambda<R-\|B\|` must have a **nonzero coordinate** on some tile of onsite energy `V(t)<R`. Under the properness hypothesis, all such tiles belong to the **finite onsite sector** `F_R=\{t:V(t)\le R\}`.

**Stronger eigenspace result:** for a fixed `\lambda<R-\|B\|` distinct from the regular resolvent shift `a`, restriction of vectors in its full finite-dimensional eigenspace `E_\lambda(H)` to the coordinates in `F_R` is an **injective linear map** into `\mathbb{R}^{F_R}`. Thus the geometric multiplicity satisfies

```math
m_H(\lambda)=\dim E_\lambda(H)\le \#\{t:V(t)\le R\}.
```

This last theorem controls the **dimension of a complete eigenspace** rather than only detecting one eigenvector. It holds without requiring a global indexed onsite-eigenvalue sequence or a new complex-spectrum construction.

**Scope and subsequent strengthening:** the inequality above applies to *one eigenspace at a time* and cannot simply be summed over distinct eigenvalues. Sections 4.41–4.43 now control the **direct sum of all low-energy eigenspaces** using symmetry, orthogonality and one dimension comparison with the finite onsite sector. Sections 4.44–4.48 prove the ordered-level comparison, finite-sector response and sufficient interacting inverse-square summability. These are separate source results; this section records the foundational single-eigenspace theorem. The explicit vertex-graph application is proved in §§4.68–4.72; global tiling coverage and aperiodicity remain open (§6.4).

### 4.41. Simultaneous spectral subspaces on the natural domain

[DomainSpectralSubspace.lean](SpectralGeometry/DomainSpectralSubspace.lean)
defines `domainEigenspace` as the actual kernel of $A-\lambda I$ inside a
specified domain $d$, and `domainLowSpectralSubspace` as the span of **all**
eigenspaces with level at most $E$. For a symmetric domain operator,
`domainLowSpectralSubspace_energy_le` proves
$\langle x,Ax\rangle\le E\|x\|^2$ on this entire span. The proof groups
vectors by distinct levels and uses orthogonality, including arbitrary
combinations of vectors from different eigenspaces. No compactness or
finite-dimensionality is assumed in this abstract lemma.

### 4.42. Quantitative finite-sector observation and closedness

[InfiniteLowEnergyObservation.lean](SpectralGeometry/InfiniteLowEnergyObservation.lean)
constructs the symmetric positive coordinate contraction `finiteSectorProjection`
and the natural-domain operator `onsitePlusBounded`.
For $V\ge v_0$, finite $F$ and $V(t)\ge R$ outside $F$, it proves
```math
\langle x,Hx\rangle\ge(R-\|B\|)\|x\|^2-(R-v_0)\|P_Fx\|^2.
```
`onsitePlusBounded_lowSpectral_observation` combines this with §4.41:
```math
\frac{R-\|B\|-E}{R-v_0}\|x\|^2\le\|P_Fx\|^2,\qquad R>v_0.
```
Symmetry of $B$ is required for the spectral-subspace step. If
$E<R-\|B\|$, restriction is injective and the module **derives** finite
dimensionality, the bound $\dim L_E\le\#F$, and closedness of its image in
the ambient Hilbert space. Thus taking the closed low-energy eigenvector span
adds no vectors and does not lose the natural-domain condition. Properness
supplies $F=F_R$; the reusable form argument only needs the displayed finite
sector hypothesis. It covers finite, empty and infinite site types.

### 4.43. Total low-energy counting with the original multiplicities

[InfiniteLowEnergyCounting.lean](SpectralGeometry/InfiniteLowEnergyCounting.lean)
injects the direct sum of any finite family of distinct low eigenspaces into
the common observed subspace. It bounds the **sum of their dimensions once**,
not by adding separate upper bounds from §4.40.

[InfiniteLocalFullSpectralObservation.lean](SpectralGeometry/InfiniteLocalFullSpectralObservation.lean)
identifies these domain eigenspaces with the existing resolvent eigenspaces.
`infiniteLocalMatching_full_total_lowEnergy_count` constructs a finite set
whose membership is exactly $\lambda\in\sigma_{\rm real}(H)$ and
$\lambda<R-\|B\|$, and proves
```math
\sum_{\lambda<R-\|B\|}m_H(\lambda)\le\#F_R.
```
The multiplicity is the original `infiniteLocalMatchingFullMultiplicity`.
This bridge assumes properness, the unit shifted onsite gap, the small
resolvent-correction bound, involutive matchings and symmetric $P$.
The shift is excluded using its proved resolvent property. The finite set may
be empty; no infinite enumeration is needed for this count.

### 4.44. Complete eigenbases with exact multiplicity tags

[DomainEigenbasis.lean](SpectralGeometry/DomainEigenbasis.lean) records a
complete Hilbert basis of genuine eigenvectors in the specified domain.
`hasSum_energy` derives the energy expansion from symmetry and Parseval
applied to $x$ and $Ax$, without postulating an unbounded-operator expansion.

[InfiniteLocalFullEigenbasis.lean](SpectralGeometry/InfiniteLocalFullEigenbasis.lean)
constructs such a basis from the existing complete finite-dimensional
resolvent eigenspaces. `infiniteLocalMatching_full_exists_tagEigenbasis`
uses exactly the original multiplicity tags, also for finite or empty spaces.
`infiniteLocalMatching_full_exists_domainEigenbasis` reindexes it along any
exact strictly increasing tag enumeration from §4.37. Repeated eigenvalues
therefore have exactly their original number of orthonormal slots.
`infiniteLocalMatching_full_tags_infinite` derives infinitude of the tag set
from an infinite site type and completeness; it does not infer infinitude
from compactness alone. All these matching results retain the explicit
resolvent, properness and symmetry hypotheses.

### 4.45. A variational characterization of the ordered levels

[OrderedVariationalPrinciple.lean](SpectralGeometry/OrderedVariationalPrinciple.lean)
proves `DomainEigenbasis.eigenvalue_le_iff_trial`: for a symmetric domain
operator with a complete eigenbasis and monotone levels,
$\lambda_n\le E$ exactly when there is an injective trial map
$\mathbb R^{n+1}\to d$ whose Rayleigh numerators are at most $E\|x\|^2$.
The first $n+1$ basis vectors give one direction; a dimension argument against
the first $n$ coordinates gives the other.

`ordered_eigenvalues_affine_le` transfers any common-domain form inequality
$\alpha A+\beta I\le K$, $\alpha\ge0$, to
$\alpha\lambda_n(A)+\beta\le\lambda_n(K)$. The zero-coefficient case is
included. `DomainEigenbasis.ordered_levels_unique` proves independence from
basis choices inside repeated eigenspaces. The infinite sequence interface
requires actual complete $\mathbb N$-indexed eigenbases; it makes no infinite
listing claim for finite or empty spaces.

### 4.46. Ordered onsite comparison and finite-sector response

[InfiniteOrderedSpectralControl.lean](SpectralGeometry/InfiniteOrderedSpectralControl.lean)
constructs the onsite eigenbasis from an explicit bijection $e:\mathbb N\simeq T$.
If $v_n=V(e(n))$ is monotone, `onsitePlusBounded_ordered_comparison` proves
```math
v_n-\|B\|\le\lambda_n(H)\le v_n+\|B\|.
```
`infiniteLocalMatching_full_ordered_comparison` applies this directly to the
existing exact matching-spectrum tag enumeration. The site bijection and its
onsite ordering are explicit inputs of this API. Section 4.57 now constructs
such a bijection from properness on infinite site types; this is a classical
existence proof, not an executable numerical sorting algorithm.
For a nonnegative interaction $L$ and signed correction $Q$, the lower bound
improves to $v_n-\|Q\|$; a wholly nonnegative correction gives $v_n$.

`finiteSector_ordered_response` proves
```math
\frac{R-\|B\|-E}{R-v_0}\,\tau
\le\lambda_n(H+\tau P_F)-\lambda_n(H)\le\tau
```
for $V\ge v_0$, $R>v_0$, finite $F$ with $V\ge R$ outside $F$,
$\lambda_n(H)\le E$ and $0\le\tau\le R-v_0$. It assumes symmetric $B$
and actual monotone complete eigenbases of both operators on the **same**
natural domain. Section 4.47 supplies their existence in the infinite proper
setting. For $E<R-\|B\|$ the lower response coefficient is positive.
The proof uses the affine comparison with $\alpha=1-\tau/(R-v_0)$,
including the endpoint $\alpha=0$. It never assumes simple eigenvalues,
differentiable eigenvalue branches or an absence of crossings.
Section 4.58 proves the stronger coefficient $(R-E)/(R-v_0)$ when the whole
bounded interaction is nonnegative, using its sharper sector form bound.

### 4.47. Existence and operator hypotheses along the perturbation

[InfiniteOrderedSpectralExistence.lean](SpectralGeometry/InfiniteOrderedSpectralExistence.lean)
embeds a generic bounded correction into the existing matching construction
with zero matching colors. `onsitePlusBoundedPMap_isSelfAdjoint` proves genuine
self-adjointness on the unchanged natural domain for symmetric $B$.

For an infinite site type, proper $V$ and a global onsite lower bound,
`onsitePlusBounded_exists_orderedEigenbasis` derives a complete monotone
infinite eigenbasis: it chooses a sufficiently negative compact-resolvent
shift, proves the spectral lower bound and uses §4.44 to establish infinite
tags before invoking §4.37. `finiteSector_exists_orderedEigenbasis` proves
existence for every real perturbation parameter. Boundedness, symmetry,
properness and the natural domain persist; positivity is an additional result
for nonnegative parameters in §4.48. Finite and empty cases are handled by
the tag-basis and observation/counting results, not by this infinite listing.

### 4.48. Full-spectrum summability and a controlled positive family

[InfiniteFullSpectralSummability.lean](SpectralGeometry/InfiniteFullSpectralSummability.lean)
proves that a bounded lower error preserves inverse-square summability for
levels tending to infinity. Properness gives divergence along an injective
site listing. Thus `onsitePlusBounded_ordered_positive_summable` transfers
onsite summability to the complete full spectrum under §4.46's explicit
ordered bijection and eigenbasis assumptions. A separate bound
$V\ge v_0>\|B\|$ gives the uniform positive gap $v_0-\|B\|$.

`onsitePlusBounded_powerGrowth_positive_summable` instantiates this with the
existing sufficient growth $V(k)\ge(k+1)^\alpha$, $\alpha>1/2$, on sites
indexed by $\mathbb N$; these original labels need not already be sorted.
Other onsite criteria, including §4.4, enter through the general transfer.
The gap assumption is not inferred from growth or compactness.
The additional positive-interaction package in §4.58 instead retains the
onsite gap $v_0>0$, without requiring $v_0>\|B\|$; it uses §4.57 to obtain
the sorted onsite bijection rather than accepting one as an input.

`finiteSector_preserves_gap_summability` preserves any supplied positive
baseline gap and inverse-square summability for every $\tau\ge0$.
`finiteSector_preserves_compact_shift` provides a compact shifted inverse for
every real $\tau$; the chosen shift may depend on $\tau$.
`finiteSector_controlled_summable_family` combines the existence theorem,
the sufficient baseline gap/summability criterion and the response bound on
the entire interval $0\le\tau\le R-v_0$. It does not assume the perturbed
eigenbases or perturbed summability as input.

`fullSpectrum_admissible_of_positive_summable` connects these full levels to
the existing canonical-product predicate. Sections 2.4 and 4.49 now supply
entire holomorphy and exact zero orders from that input. The indexed
finite-sector zero-response theorem is proved in §4.52. Section 4.55 now
preserves a positive gap and summability for symmetric bounded errors of
either sign whose norm is smaller than the supplied gap. Sections 4.71–4.72
prove summability and construct the full products for the octagonal graph.
Relative determinants and extensions beyond the stated error bound remain open.

### 4.49. Full spectral products with exact geometric zero multiplicities

[InfiniteFullSpectralProduct.lean](SpectralGeometry/InfiniteFullSpectralProduct.lean)
connects the analytic results of §2.4 to the existing full operator and its
original geometric multiplicities $m_H(r)$. The enumeration is exactly the
strictly increasing sequence of tags $(\lambda,k)$ from §4.37, with
$0\le k<m_H(\lambda)$. `infiniteLocalMatching_full_sequence_levelMultiplicity`
proves that the fiber over each real level has cardinality $m_H(r)$, including
zero outside the spectrum. This uses exact tag coverage and injectivity,
rather than an arbitrary repeating enumeration.

`infiniteLocalMatching_full_product_entire_exact_zeros` proves entire
holomorphy and
```math
D_H(s)=0\quad\Longleftrightarrow\quad
\exists\lambda\in\sigma_{\mathrm{real}}(H),\quad
s=c+d\lambda\ \text{or}\ s=c-d\lambda.
```
At each positive level, including levels outside the spectrum, it also proves
```math
\operatorname{ord}_{c\pm dr}D_H=m_H(r)\quad(r>0).
```
Its hypotheses retain the natural-domain operator, finite onsite sublevel
sets, a real shift $a$ with $V-a\ge1$, the Neumann bound
$\|B R_a^{\mathrm{on}}\|<1$, an exact infinite tag sequence, admissibility of
its positive levels and $d\ne0$. Admissibility follows from positive levels
and inverse-square summability. The analytic bridge itself needs no additional
symmetry assumption once these spectral data are supplied; the existing
self-adjoint existence theorems justify the sequence in the symmetric setting.

`infiniteLocalMatching_full_product_admissible_of_onsite` obtains the required
admissibility for this very tag sequence from involutive matching colors,
symmetric $P$, $V\ge v_0>\|B\|$, properness, an explicitly sorted site bijection
and onsite inverse-square summability. It constructs the domain eigenbasis via
§4.44 and reuses §4.48's transfer. Together these theorems instantiate the exact
zero result for the interacting spectrum without assuming its summability in
that application. The onsite growth criteria feed this general input.

The theorem concerns the full **real bounded-inverse spectrum** already
identified with genuine natural-domain eigenvalues. It is not a new complex
operator spectrum theorem. The supplied infinite sequence is justified by
§§4.37 and 4.47 under their lower-bound, symmetry and infinitude hypotheses;
finite/empty spectral cases remain separate. Repeated levels are allowed and
produce the exact original geometric multiplicity at each paired zero.
Normalization and symmetry use the same arbitrary fixed $c,d$ throughout a
family. The formal indexed zero-displacement estimate is now proved in §4.52;
the concrete geometric instantiation is proved in §4.72.


### 4.50. Algebraic identities for indexed spectral points

[IndexedSpectralPoints.lean](SpectralGeometry/IndexedSpectralPoints.lean)
defines the points $z_n^+ = c+d\lambda_n$ and $z_n^- = c-d\lambda_n$
for a real sequence, a fixed complex center $c$, and a fixed direction $d$.
The two subtraction lemmas give exactly
$
z_n^\pm(\tau)-z_n^\pm(0)
=\pm d\,(\lambda_n(H_\tau)-\lambda_n(H)),
$
with the real difference cast into the complex numbers. The norm lemmas first
give $|d|\,|\lambda_n(H_\tau)-\lambda_n(H)|$. Only after an ordered
nonnegative response is established does
`indexedSpectralPoints_norm_bounds` remove the real absolute value.
`indexedSpectralPoints_ne` proves that a positive lower response, a
strictly positive parameter and $d\ne0$ exclude stationary *indexed*
points. It does not claim disjoint zero sets at different parameters.

### 4.51. Matching the variational levels to exact geometric zero orders

[OrderedSpectralProductBridge.lean](SpectralGeometry/OrderedSpectralProductBridge.lean)
bridges the two distinct spectral APIs. The min-max and response results use
arbitrary monotone complete `DomainEigenbasis` sequences. In contrast, the
exact order theorem of §4.49 uses a strictly increasing enumeration of *all*
geometric multiplicity tags. `onsitePlusBounded_ordered_eq_exact_tag_levels`
constructs the latter explicitly using zero matching colors, a sufficiently
negative resolvent shift, infinite sites, properness, symmetry and the
existing lower-bound and tag-infinitude proofs. It then applies
`DomainEigenbasis.ordered_levels_unique` to identify the sequences
index by index. It does not assume that the existential ordered-basis
theorem itself supplies tag coverage.

`HasExactFullSpectralProduct` records entire differentiability, the exact
two-sided zero set given by the real spectrum of the actual operator, and
zero orders equal to the original full geometric multiplicities at every
positive level. Its witnessing shift and Neumann bound are allowed to depend
on the bounded correction.
`onsitePlusBounded_hasExactFullSpectralProduct` establishes this predicate
from the complete ordered basis, positivity and inverse-square summability,
using §4.49; `indexedSpectralPoints_product_zeros` identifies both indexed
points as actual zeros. Each operator receives its own multiplicity function;
no invariance of multiplicities under perturbation is asserted.

### 4.52. Effective finite-sector displacement of full-product zeros

[FiniteSectorZeroResponse.lean](SpectralGeometry/FiniteSectorZeroResponse.lean)
proves `finiteSector_fullProducts_indexedZeroResponse` for infinitely many
sites with a symmetric bounded correction, proper onsite potential,
an explicitly monotone onsite bijection, onsite inverse-square summability,
$V\ge v_0>\|B\|$, $v_0<R$, a finite set $F$ with $V\ge R$ outside it,
and $E<R-\|B\|$. For each $0\le\tau\le R-v_0$, it constructs a monotone
complete ordered sequence of the actual operator
$H_\tau=M_V+B+\tau P_F$ on the same natural domain. Both its product and the
baseline product have the exact real zero sets and geometric orders of their
respective operators. With the *same* fixed $c,d\in\mathbb C$, $d\ne0$, for
each index with $\lambda_n(H)\le E$ it proves
$
|d|\,\frac{R-\|B\|-E}{R-v_0}\,\tau
\le |z_n^\pm(\tau)-z_n^\pm(0)|\le |d|\,\tau.
$
The oriented complex differences and the four zero identities are included
in the conclusion. For $\tau>0$ each indexed point changes position relative
to its baseline index. The proof invokes the already verified
`finiteSector_controlled_summable_family` and gap/summability preservation,
not an assumed response estimate or a new condition
$v_0>\|B+\tau P_F\|$. Both interval endpoints are included. The theorem
does not assert that the energy window is nonempty, rule out zero collisions
between *different* indices and parameter values, or select a global
eigenvector family depending on $\tau$. The concrete Ammann–Beenker
full-product response is proved in §4.72 using the positive-interaction
framework of §§4.58–4.59, which preserves the onsite gap. Relative
determinants and certified finite-patch approximation remain open.
Small signed-error stability and separated zero-window
certificates are proved in §§4.53–4.56 under their additional norm and
boundary-margin hypotheses. They do not restrict the positive-response
interval already verified in this section.

### 4.53. Ordered windows certified by neighboring levels

[OrderedSpectralWindow.lean](SpectralGeometry/OrderedSpectralWindow.lean)
defines `OrderedGapCertificate q δ t k` using only the two inequalities
$q_{k-1}+\delta<t$ (when $k>0$) and $t+\delta<q_k$.
For monotone reference levels and an all-index bound
$|\mu_i-q_i|\le\delta$, `orderedGapCertificate_separates` proves that every
index below $k$ is strictly below $t$ and every remaining index is strictly
above it. Boundary exclusion is a conclusion, not an assumption about the
unknown perturbed levels.

`orderedWindow_indices_iff` combines two cuts to identify the complete
window index set with `Finset.Ico m n`. `orderedWindow_finite_card` proves
its finiteness and cardinality $n-m$. A cut before the first index and an
empty index block are included. No separation is required between the
levels inside the block.

### 4.54. Counting exact analytic orders on the complex line

[CanonicalProductClusterCount.lean](SpectralGeometry/CanonicalProductClusterCount.lean)
proves `canonicalProduct_cluster_order_sum`: the sum of analytic orders over
the distinct levels of a finite, level-saturated index set is its cardinality.
Saturation means every copy of an included level is present; it is derived
for the certified window, so repeated levels are not partially counted.
The proof reuses §2.4's exact order theorem and a finite fiber decomposition.

`canonicalProduct_certified_window` constructs `CertifiedCanonicalWindow`
from the reference cuts, the level-error bound, admissibility of the compared
sequence, $d\ne0$ and a positive lower window endpoint. It records the exact
indices, the complete zero set on each closed reflected segment, and the
order sum. `spectralWindowZeros` is the finite set of distinct complex roots.
The methods `mem_zeros_iff`, `complex_order_sum` and `boundary_ne_zero` prove
that these are all segment zeros, that their analytic orders sum to $n-m$,
and that both endpoints are zero-free for $a\le b$. Injectivity of the signed
affine coordinate is proved explicitly before changing the order sum from
real levels to complex points. Empty windows and repeated levels are covered.

### 4.55. Small symmetric bounded errors: ordered levels, gap and summability

[InfiniteBoundedSpectralStability.lean](SpectralGeometry/InfiniteBoundedSpectralStability.lean)
proves `onsitePlusBounded_ordered_perturbation_bound` for symmetric bounded
$B,K$ and actual complete monotone domain eigenbases of $M_V+B$ and
$M_V+B+K$ on the same natural domain:
```math
|\lambda_i(M_V+B+K)-\lambda_i(M_V+B)|\le\|K\|.
```
The proof derives a two-sided quadratic-form comparison and invokes the
existing variational theorem. It permits either sign and infinite rank of
$K$, and does not assume simple eigenvalues.

`positive_invSq_summable_of_small_error` shows that a supplied baseline gap
$q_i\ge\gamma$ and inverse-square summability persist under
$\mu_i\ge q_i-\delta$, $0\le\delta<\gamma$. The new gap is
$\gamma-\delta>0$. Its proof compares $\mu_i$ to
$((\gamma-\delta)/\gamma)q_i$; no separate growth or summability hypothesis
is imposed on the perturbed sequence.
`onsitePlusBounded_small_error_preserves_summability` applies this to the
actual operator error. This abstract lemma accepts any proved baseline gap;
§4.56 uses the sufficient gap $v_0-\|B\|$ from the existing onsite transfer.

### 4.56. Full spectral zero-cluster certificates under operator error

[InfiniteFullSpectralCluster.lean](SpectralGeometry/InfiniteFullSpectralCluster.lean)
proves `onsitePlusBounded_exists_certified_zero_clusters`. It assumes infinitely
many sites, symmetric bounded $B,K$, $V\ge v_0$, proper onsite sublevel sets,
a supplied sorted onsite bijection, onsite inverse-square summability,
$\|K\|\le\eta<v_0-\|B\|$, and fixed $c,d$ with $d\ne0$.

The theorem derives both complete ordered spectra, their lower gaps,
admissibility and `HasExactFullSpectralProduct` for their respective actual
operators. Existence and the original geometric multiplicity identification
come from §§4.47 and 4.51; the witnessing compact-resolvent shifts may differ.
It proves the all-index level error and the two signed zero-displacement
bounds $|d|\eta$. Each positive energy window with the two reference cut
certificates receives `CertifiedCanonicalWindow` for **both** products,
hence the same total geometric zero multiplicity on each signed segment.

The theorem does not assume the perturbed spectrum, its summability, the
level error or the zero count as input. The boundary margins are independent
finite inequalities to verify in an application. Multiplicities inside a
window may change; their total is conserved. This is an infinite-operator
certificate for a bounded common-domain discrepancy. It does not yet supply
an error estimate for a finite patch, a contour theorem for arbitrary
analytic approximants, or an instantiation for the proposed tiling.

### 4.57. Sorted onsite enumeration from properness

[InfiniteOnsiteOrderedEnumeration.lean](SpectralGeometry/InfiniteOnsiteOrderedEnumeration.lean)
proves `infiniteOnsite_exists_monotone_equiv`. If the site type is infinite
and every onsite sublevel $\{t:V(t)\le R\}$ is finite, then there exists a
bijection $e:\mathbb N\simeq T$ with $n\mapsto V(e(n))$ nondecreasing.
All sites at repeated energies are retained. No countability hypothesis,
injectivity of $V$, supplied enumeration or additional lower bound is needed
for this ordering theorem.

The proof orders sites lexicographically by their energies and a classical
injective cardinal-valued tie breaker. Every predecessor set lies in a finite
onsite sublevel, so the enumeration theorem of §4.37 applies. This supplies
the ordering input of the existing comparison and growth-transfer APIs.
It is a noncomputable existence construction; it does not yet provide a
numerical sorting procedure. The infinite-site hypothesis is explicit:
finite and empty spaces are not represented by repeating sites indefinitely.

### 4.58. Positive-interaction gaps, summability and sharper spectral response

[InfinitePositiveSpectralControl.lean](SpectralGeometry/InfinitePositiveSpectralControl.lean)
proves `onsitePlusNonneg_ordered_positive_summable`. Assume symmetric bounded
$B$ with $\langle x,Bx\rangle\ge0$, $V\ge v_0>0$, finite onsite sublevels,
onsite inverse-square summability and infinitely many sites. For an actual
monotone complete eigenbasis of $H=M_V+B$ on $D(V)$, it proves
```math
\lambda_n(H)\ge v_0>0,
\qquad \sum_n\lambda_n(H)^{-2}<\infty.
```
The sorted onsite bijection comes from §4.57, and the existing positive
comparison $\lambda_n(H)\ge V(e(n))$ gives a termwise inverse-square bound.
The eigenbasis is supplied by §4.47. No smallness condition on $\|B\|$ is
required. `infiniteLocalMatching_exists_positive_summable_spectrum` derives
the complete ordered spectrum, gap and summability for the existing finite
family of involutive matchings with nonnegative weights. Its weights need
not be small; this corollary does not construct a named tiling.

`onsitePlusNonneg_sector_form_bound` proves
```math
H\ge R I-(R-v_0)P_F
```
on the natural domain when $V\ge R$ outside the finite set $F$.
`finiteSector_ordered_response_of_form_bound` first treats a general proved
sector inequality $H\ge A I-DP_F$, $D>0$. The resulting
`finiteSector_ordered_response_of_nonneg` gives
```math
\frac{R-E}{R-v_0}\,\tau
\le\lambda_n(H+\tau P_F)-\lambda_n(H)\le\tau,
\quad \lambda_n(H)\le E,\quad 0\le\tau\le R-v_0.
```
Here $R>v_0$, and the lower coefficient is positive for $E<R$.
The proof uses the same domain-aware variational principle as §4.46,
including multiplicities, crossings and both parameter endpoints.

`finiteSector_nonneg_controlled_summable_family` constructs the perturbed
ordered spectra for every $\tau\ge0$, preserves the gap $v_0$ and
inverse-square summability, and proves monotonicity of every ordered level.
The displayed quantitative response is restricted to $\tau\le R-v_0$.
Self-adjointness and compact shifted inverses follow from the existing
properness and symmetry theorems on the unchanged natural domain; the shift
may depend on $\tau$. No perturbed eigenbasis or perturbed summability is
assumed. This is an infinite-sequence result and does not assert that any
level lies in the selected low-energy window.

### 4.59. Sharpened full-product zero response for positive interactions

[PositiveFiniteSectorZeroResponse.lean](SpectralGeometry/PositiveFiniteSectorZeroResponse.lean)
proves `finiteSector_nonneg_fullProducts_indexedZeroResponse`. Under §4.58's
positive-interaction, properness and onsite summability hypotheses, it
constructs both ordered spectra and `HasExactFullSpectralProduct` for the
actual original and perturbed operators. Fixed $c,d$ with $d\ne0$ give
```math
|d|\frac{R-E}{R-v_0}\,\tau
\le |z_n^\pm(\tau)-z_n^\pm(0)|\le |d|\tau,
\quad \lambda_n(H)\le E<R,\quad 0\le\tau\le R-v_0.
```
The theorem also proves that these points are zeros of their respective
products, the oriented difference identities, and movement of each selected
indexed zero for $\tau>0$. Exact analytic orders are the geometric
multiplicities of each product's own operator. A supplied onsite ordering,
simple eigenvalues and $v_0>\|B\|$ are not hypotheses of this application.

For $v_0=1$, $R=5$, $E=3$, the coefficient is $1/2$. Sections 4.68–4.70
now construct the centered octagonal vertex set, matching interaction and
finite sector, and prove $\lambda_8(H)\le3$ from nine distinct central sites.
Sections 4.71–4.72 now prove its inverse-square summability and exact
full-product application, with a nonempty nine-level window. The abstract theorem itself does not assume or prove window
nonemptiness, and does not exclude common zero locations arising from
different indices at different parameters. Relative products and certified
finite-patch approximation remain separate obligations.

### 4.60. Local zero certificates from scalar boundary error

[AnalyticZeroLocalization.lean](SpectralGeometry/AnalyticZeroLocalization.lean)
defines `LocalAnalyticZeroControl f a m ρ C`. It records $m>0$,
$\rho,C>0$, analyticity on a neighborhood of the closed disk, exact order
$\operatorname{ord}_a f=m$, and
$C|z-a|^m\le|f(z)|$ throughout that disk.
`exists_localAnalyticZeroControl` derives these data from analyticity at
$a$ and finite positive zero order. It extracts the nonvanishing analytic
cofactor and uses continuity to obtain its positive lower bound. Thus
existence of the constants is proved, although their numerical values
remain to be certified in an application.

`LocalAnalyticZeroControl.zero_iff` proves that the reference disk isolates
the distinct zero $a$. `analytic_error_le_on_closedBall` extends a uniform
boundary error to the closed disk by the maximum modulus principle.
`LocalAnalyticZeroControl.approximation` assumes an approximant analytic
near the closed disk, a boundary error at most $\varepsilon\ge0$ and
$2\varepsilon<C\rho^m$. It proves existence of an interior zero, exclusion
of boundary zeros, and
```math
g(z)=0,\quad |z-a|\le\rho
\quad\Longrightarrow\quad |z-a|^m\le\varepsilon/C.
```
The existence proof applies the maximum principle to the inverse under a
contradictory zero-free hypothesis. `zero_distance_le` writes the bound as
$(\varepsilon/C)^{1/m}$; `approximation_ne_zero_of_norm_gt` gives the
complementary zero-exclusion test wherever the reference modulus exceeds
the certified error. These statements do not count the approximating
zeros, assume that they are simple, or keep them on a real affine line.
Section 4.64 adds exact counting under the weaker smallness condition
$\varepsilon<C\rho^m$, without changing these earlier statements.

### 4.61. Explicit inverse-square tail errors for canonical products

[CanonicalProductApproximation.lean](SpectralGeometry/CanonicalProductApproximation.lean)
defines `canonicalPartialProduct` and `canonicalProductApproximationError`.
For positive $q_n$, summable inverse squares, a finite cutoff $N$, and a
squared affine-coordinate bound $A$, `canonicalProduct_partial_error_le`
proves the uniform estimate of §2.6:
```math
|D_q(z)-P_N(z)|\le E_N(A),\qquad
E_N(A)=e^{AS}(e^{AT_N}-1),\quad
S=\sum_nq_n^{-2},\quad T_N=\sum_{k\ge0}q_{k+N}^{-2}.
```
`tprod_one_add_truncation_error` first proves the underlying estimate for
any complex product with a summable norm majorant. It splits the initial
product from its tail and passes finite exponential bounds to the limit.
It never divides by the initial product, so the bound includes its zeros
and the empty product at $N=0$.

`canonicalProductApproximationError_tendsto_zero` proves $E_N(A)\to0$ for
fixed $A$. `canonicalProductApproximationError_le_of_bounds` replaces
$S,T_N$ by independently verified upper bounds, giving an error budget
with no infinite sums in its conclusion.
`canonicalProduct_approximation_error_add` adds a certified error $\eta$
between an arbitrary approximant and $P_N$. A computable convergence rate
still requires a computable tail bound. No finite-volume spectrum is
identified with this truncation of the fixed full sequence. Section 4.66
adds the numerical bounds $S\le2$, $T_N\le1/N$ and $E_N(A)\le324/N$
under the stated linear growth and coordinate restrictions.

### 4.62. Scalar approximation at full spectral zeros

[FullSpectralZeroLocalization.lean](SpectralGeometry/FullSpectralZeroLocalization.lean)
connects the preceding certificates to the existing exact divisor.
`canonicalProduct_exists_local_zero_control` obtains local control at
each signed indexed zero, with exponent `levelMultiplicity q (q i)`.
`HasExactFullSpectralProduct.local_zero_controls` instead states that
exponent directly as the actual operator's geometric multiplicity, using
the compact-resolvent witness already belonging to that full product.
The order is not supplied independently of the spectral divisor.

`LocalAnalyticZeroControl.canonical_approximation` combines the local
certificate with §4.61's tail error and an independently bounded analytic
approximation to the finite product. For a disk about $a$, it proves the
affine-coordinate bound
```math
A=\left(\frac{|a-c|+\rho}{|d|}\right)^2
```
and uses $\varepsilon=E_N(A)+\eta$ in the condition
$2\varepsilon<C\rho^m$. Its conclusion includes an interior zero, the
power location bound for every zero in the disk, and a zero-free boundary.

`onsitePlusNonneg_exists_scalar_zero_control` constructs the required
ordered full spectrum, complete natural-domain eigenbasis, positivity,
inverse-square summability, exact full product and local zero controls.
It assumes infinitely many sites, symmetric nonnegative bounded $B$,
$V\ge v_0>0$, proper onsite sublevels, onsite inverse-square summability,
and fixed $c,d$ with $d\ne0$. It reuses §§4.47, 4.51 and 4.58, including
their self-adjointness and compact-resolvent construction on $D(V)$.
No smallness of $\|B\|$, simple eigenvalues or supplied onsite ordering
is required. Finite and empty spectra are not padded into an infinite
sequence; the local analytic lemmas themselves do not require an
infinite-dimensional operator.

The arbitrary approximant need not be a spectral product, share the
paired symmetry, or have its zeros on the prescribed line. The theorem
certifies persistence and local location, not equality of total zero
multiplicity, an index matching, or a finite-patch error. Section 4.65 adds
the exact disk count using the same local controls and tail budget.
Section 4.67 supplies numerical cofactor and tail bounds for a worked
linear onsite model. For the explicit octagonal graph, §4.72 proves the
full-product indexed zero response. A model-specific local approximation
certificate with numerical cofactor/radius bounds and a truncation cutoff
remains to be supplied (§6.4).

### 4.63. Finite disk zero counts and the argument principle

[AnalyticDiskZeroCount.lean](SpectralGeometry/AnalyticDiskZeroCount.lean)
defines `analyticDiskZeroSet` as the finite support of the divisor on a
closed disk and `analyticDiskZeroCount` as the sum of its natural-valued
orders. The interpretation requires $R>0$, analyticity on a neighborhood
of $\overline B(c,R)$ and a zero-free boundary. Under these hypotheses,
`analyticOrderAt_ne_top_on_disk` excludes infinite analytic orders,
`analyticDisk_divisor_order` identifies every divisor entry with the
actual analytic order, and `mem_analyticDiskZeroSet_iff` identifies the
finite support with **all** interior zeros. Thus no infinite-order point
or boundary zero is silently discarded by the total definition.

`analytic_disk_factorization` extracts all these zeros with their orders
and an analytic cofactor that is nonzero on the closed disk. Equality holds
as an analytic germ at every point of the disk, including its boundary.
`analytic_disk_argument_principle` then proves
```math
\oint_{|z-c|=R}\frac{f'(z)}{f(z)}\,dz
 = 2\pi i\,N_f(c,R),
\qquad N_f(c,R)=\sum_{z\in B(c,R):f(z)=0}\operatorname{ord}_z f.
```
The proof integrates the finite sum of pole terms from the factorization;
the nonvanishing cofactor contributes zero by Cauchy's theorem. The circle
has its usual positive orientation. The disk may contain no zeros, one
multiple zero, or several zeros. The zero function and radius-zero disks
are excluded by the explicit hypotheses; arbitrary contours and a
meromorphic zeros-minus-poles formula are not claimed.

### 4.64. Rouché conservation and exact local multiplicity

[AnalyticRouche.lean](SpectralGeometry/AnalyticRouche.lean) proves
`analytic_disk_rouche`: for $R>0$ and $f,g$ analytic near the closed disk,
```math
|g(z)-f(z)|<|f(z)|\quad (|z-c|=R)
\quad\Longrightarrow\quad N_g(c,R)=N_f(c,R).
```
`rouche_boundary_nonzero` proves the two boundary zero exclusions. On the
boundary $g/f$ lies in the open unit disk about $1$, so its principal
logarithm is defined analytically there. Integrating its derivative proves
`rouche_logDeriv_integral_eq`; §4.63 converts that equality into the exact
natural-valued counts. No homotopy invariant, zero-count equality or
simple-root condition is supplied as an assumption.

`LocalAnalyticZeroControl.zero_count` identifies the reference count with
$m$. `LocalAnalyticZeroControl.approximation_zero_count` combines this with
a uniform boundary error $\le\varepsilon<C\rho^m$ and proves
simultaneously: count $m$, a zero-free boundary, and
$|z-a|^m\le\varepsilon/C$ for every approximating zero in the closed disk.
The distance estimate of §4.60 remains available. The reference order
satisfies $m>0$; the general disk theorem also handles empty zero sets.
Approximating zeros may split, have different individual orders, and
leave the prescribed affine line. Conservation concerns their total order.

### 4.65. Exact approximation counts at full spectral zeros

[FullSpectralZeroCounts.lean](SpectralGeometry/FullSpectralZeroCounts.lean)
reuses the local controls of §4.62 and the explicit tail of §4.61.
`LocalAnalyticZeroControl.canonical_approximation_zero_count` proves the
exact count, boundary exclusion and the power bound from
```math
\sup_{|z-a|=\rho}|g(z)-P_N(z)|\le\eta,
\qquad E_N(A)+\eta<C\rho^m,
\qquad A=\left(\frac{|a-c|+\rho}{|d|}\right)^2.
```
It requires positive $q_n$, summable inverse squares, the local control,
and analyticity of $g$ near the closed disk. The approximant need not be
another spectral product. `eventually_partial_zero_count` proves that
all sufficiently long partial products have count $m$ and a zero-free
boundary; this general theorem's threshold index is existential.
Section 4.67 supplies a sufficient numerical cutoff for the linear onsite
example, using §4.66's additional growth and lower-bound estimates.

`canonicalProduct_exists_local_counting_control` constructs these local
controls at each signed indexed zero of an admissible product with
$d\ne0$, with count `levelMultiplicity q (q i)`.
`HasExactFullSpectralProduct.local_counting_controls` identifies the count
directly with the **original operator's geometric eigenspace dimension**,
using the same compact-resolvent witness as the exact-product interface.
Its spectral hypotheses are inherited from §§4.49, 4.51 and 4.62; the
positive-interaction construction in §4.62 supplies an instance on the
natural domain with an infinite ordered spectrum. No new operator gap,
self-adjointness, summability or enumeration assumption is hidden in the
analytic comparison. Finite/empty analytic zero sets are handled by §4.64;
no finite spectrum is padded into the infinite spectral construction.

These results supply the disk-counting step of §6.3. Sections 4.66–4.67
provide numerical data for a worked onsite example. Cofactor/radius
certificates for interacting geometric models and finite-patch
operator/resolvent errors remain to be supplied. Counting on noncircular
contours is outside this interface. The concrete full-product response is documented in §4.72.

### 4.66. Numerical tail rates and finite-factor lower certificates

[CanonicalProductNumericalBounds.lean](SpectralGeometry/CanonicalProductNumericalBounds.lean)
proves, from the explicit lower growth bound $q_n\ge n+1$,
```math
S=\sum_{n\ge0}q_n^{-2}\le2,\qquad
T_N=\sum_{k\ge0}q_{k+N}^{-2}\le\frac1N\quad(N\ge1).
```
`invSq_tail_le_of_linear_growth` uses a telescoping reciprocal comparison
for finite partial sums and passes to the summable limit.
`invSq_sum_le_two_of_linear_growth` adds the first term. The positive
cutoff restriction is explicit; the total series has its separate bound.
`canonicalProductApproximationError_le_linear_rate` then proves
```math
0\le A\le2,\quad N\ge2
\quad\Longrightarrow\quad E_N(A)\le\frac{324}{N}.
```
The constant is conservative: the proof bounds the exponential factors
using verified real inequalities. It does not use floating-point
approximations, an assumed rate, or an expansion of a long partial product.

`norm_tprod_one_add_ge_one_sub_tsum` proves
$|\prod_n(1+u_n)|\ge1-\sum_n|u_n|$ for a summable norm budget at most
one. `canonicalProduct_tail_norm_lower` specializes this to a tail with
inverse-square bound $T$ and $AT\le1$, obtaining modulus at least $1-AT$.
`canonicalProduct_eq_partial_mul_tail` gives the exact factorization even
at zeros of the prefix. `canonicalProduct_lower_of_prefix_tail` combines
a finite-prefix bound $L\le|P_N(z)|$ with that tail to obtain
$L(1-AT)\le|F(z)|$. These are reusable certificates; the bounds on the
finite factors and on the tail must still be proved in each application.

### 4.67. A numerical certificate for the complete linear onsite spectrum

[LinearOnsiteZeroCertificate.lean](SpectralGeometry/LinearOnsiteZeroCertificate.lean)
defines `linearOnsitePotential n = n + 1`. Positivity, inverse-square
summability and properness of all onsite sublevels are proved.
`linearOnsite_hasExactFullSpectralProduct` constructs the complete ordered
eigenbasis and invokes the existing natural-domain spectral bridge for
$H=M_V$ on $\ell^2(\mathbb N)$, with $B=0$. Thus the sequence used in the
certificate is the full spectrum with its geometric multiplicities,
not only a supplied list of point eigenvalues. The domain is $D(V)$;
the existing self-adjointness and compact-resolvent construction applies
with the now verified lower bound and properness. This is an infinite
onsite model, without a geometric tiling or a finite-patch interpretation.

`linearOnsiteCofactor` is the explicit entire function
```math
G(z)=-(z+1)\left(1-\frac{z^2}{4}\right)
       \prod_{k\ge0}\left(1-\frac{z^2}{(k+3)^2}\right).
```
`linearOnsiteCofactor_differentiable` and
`linearOnsite_cofactor_factorization` prove entire holomorphy and
$F(z)=(z-1)G(z)$ everywhere, including at $z=1$.
`linearOnsiteCofactor_norm_lower` proves $|G(z)|\ge1/5$ on the whole
closed disk of radius $1/4$. The proof bounds the two explicit factors
by $7/4$ and $39/64$, and the remaining product by $7/32$ using
$A=25/16$ and $T_2\le1/2$. The center is included in the cofactor bound;
no division by $z-1$ at the zero is used.

`linearOnsite_zero_control` packages radius $\rho=1/4$, constant $C=1/5$
and exact order $m=1$. It therefore isolates the reference zero through
the existing `LocalAnalyticZeroControl` interface.
`linearOnsite_partial_error` proves $|F-P_N|\le1/50$ on the entire
closed disk for every $N\ge16384$.
`linearOnsite_approximation_certificate` assumes only that $g$ is analytic
near this disk and $|g-P_N|\le1/100$ on its boundary, and proves
simultaneously:

- total analytic zero order $N_g(1,1/4)=1$;
- no zero on the circle $|z-1|=1/4$;
- every zero in the closed disk satisfies $|z-1|\le3/20$.

The total error budget is $3/100< C\rho=1/20$. The earlier Rouché and
location results supply these conclusions, with no zero-count assumption
on the approximant. The constants and cutoff are sufficient certificates,
not optimized numerical values.

`linearOnsitePlusNonneg_exists_numerical_tails` also constructs a complete
ordered eigenbasis for $M_V+B$ for every symmetric nonnegative bounded
$B$ on the same space. The existing variational comparison gives
$\lambda_n\ge n+1$; the new theorem then supplies summability,
$T_N\le1/N$ and $E_N(A)\le324/N$ with the same cutoff and coordinate
restrictions as §4.66. It does **not** transfer the explicit cofactor,
first-zero location or isolation radius of the $B=0$ example to arbitrary
interactions. Those data still need model-specific certificates.

### 4.68. An explicit octagonal cut-and-project vertex set

[AmmannBeenkerCutProject.lean](SpectralGeometry/AmmannBeenkerCutProject.lean)
defines lifts $n=(n_0,n_1,n_2,n_3)\in\mathbb Z^4$, with $\alpha=\sqrt2/2$,
and the two conjugate projections
```math
p(n)=(n_0+\alpha(n_1-n_3))+i(n_2+\alpha(n_1+n_3)),
\qquad
p^*(n)=(n_0-\alpha(n_1-n_3))+i(-n_2+\alpha(n_1+n_3)).
```
The accepted lifts satisfy the **open** centered octagonal window
```math
|u|,|v|<\tfrac12+\alpha,\qquad |u+v|,|u-v|<1+\alpha,
\qquad u+iv=p^*(n).
```
This fixes the boundary convention explicitly. These are the standard
conjugate eighth-root coordinates and unit-side octagon used for the
Ammann–Beenker vertex construction; see [Beenker's report](https://pure.tue.nl/ws/files/4269555/253166.pdf)
and the projection description in
[Topological densities of quasiperiodic structures](https://doi.org/10.1515/zkri-2025-0003).
The Lean definitions, rather than a picture or an assumed tiling predicate,
specify the set used below.

`physical_injective`, `internal_injective` and `position_injective`
prove uniqueness of the integer lift using irrationality of $\sqrt2$.
The origin and every signed standard basis lift are admitted; their
physical distances from the origin are one. `inflate` is an integer map
whose physical projection scales by $1+\sqrt2$ and whose internal
projection scales by $1-\sqrt2$. `admitted_inflate` and
`inflatedOriginNeighbor_injective` prove that the accepted vertex type is
infinite, rather than assuming infinitude.

`joint_norm_identity` identifies the sum of the squared projection norms
with $2\sum_i n_i^2$. It gives `coordinate_bound`: accepted lifts with
$|p(n)|\le R$, $R\ge0$, satisfy $|n_i|\le R+3$.
`finite_norm_sublevel` then proves finiteness of the actual vertices in
every radius sublevel, including empty sublevels. This proves local
finiteness and will supply properness. It is **not** a two-dimensional
counting rate or a uniform separation estimate. Polygonal coverage,
aperiodicity and global rotational-symmetry theorems are not asserted.

### 4.69. Exact neighbors, parity matchings and the concrete Laplacian

[AmmannBeenkerGraph.lean](SpectralGeometry/AmmannBeenkerGraph.lean)
defines adjacency independently of the matching operators: two admitted
lifts differ by $\pm e_i$. `adjacent_irrefl`, `adjacent_symm` and
`adjacent_unit_length` prove that these are undirected unit-length edges
without loops. The converse classification of all pairs at Euclidean
distance one is not claimed here.

Direction and parity of the corresponding integer coordinate define eight
colors. Each color exchanges the two endpoints of its admitted edge and
fixes a vertex when the proposed partner is absent.
`latticeMate_involutive` and `mate_involutive` prove the involutions;
`mate_adjacent`, `adjacent_exists_mate` and `mate_color_unique` prove
that their nontrivial edges are exactly the defined edges, each occurring
in one color. `neighbors_card_le` gives degree at most eight, and
`origin_neighbors_card` proves that the center has exactly eight distinct
neighbors, all at unit distance.

With weight $1/16$ for each color, `interaction_apply` proves the exact
coordinate formula
```math
(B\psi)(x)=\frac1{16}\sum_{y\sim x}(\psi(x)-\psi(y)).
```
`interaction_nonneg`, `interaction_symmetric` and `interaction_norm_le`
give nonnegative energy, symmetry and $\|B\|\le1$ on the full real
$\ell^2$ space. This uses the existing infinite matching operator API;
fixed points do not add a diagonal term or a fictitious edge.

### 4.70. A nonempty nine-level spectral response on the vertex graph

[AmmannBeenkerOperator.lean](SpectralGeometry/AmmannBeenkerOperator.lean)
sets $V(x)=1+|p(x)|^2$, $H=M_V+B$ on its natural domain $D(V)$, and
$S=\{x:|p(x)|\le2\}$. `potential_proper` and `potential_lower` prove
finite onsite sublevels and $V\ge1$; `sector` is proved finite and
`potential_outside_sector` gives $V\ge5$ off $S$.

`centralStar_card` proves that the center and its neighbors give nine
distinct sites. `centralStar_potential_le` bounds their onsite energies by
two. `ninth_onsite_le` places the ninth sorted onsite level below or at
two, by injecting these nine sites into any proposed initial segment.
The established variational comparison and $\|B\|\le1$ then give
$\lambda_8(H)\le3$; no nonempty spectral window is assumed.

The principal theorem `AmmannBeenker.exists_nine_level_response`
constructs complete monotone natural-domain eigenbases for $H$ and every
$H_\tau=H+\tau P_S$, $0\le\tau\le4$, and proves
```math
\lambda_n(H),\lambda_n(H_\tau)\ge1\quad(n\in\mathbb N),\qquad
\lambda_n(H)\le3\quad(0\le n<9),
```
```math
\frac\tau2\le\lambda_n(H_\tau)-\lambda_n(H)\le\tau
\quad(0\le n<9,\ 0\le\tau\le4).
```
Infinitude, properness, the central sites and the interaction bounds are
proved inputs from this explicit graph. The common-domain self-adjoint
and compact-shifted-resolvent existence package is reused, and the shift
may depend on $\tau$. Repeated levels are counted through complete
orthonormal eigenbases; simplicity is not assumed. The proof uses the
positive sector form bound and the verified min–max comparison.

This is the concrete spectral foundation for the stronger full-product
result of §4.72. Section 4.71 derives geometric inverse-square summability;
local finiteness or compact resolvent alone would not supply it. No
optimal sector, finite-patch error or new spectral technique is asserted.

### 4.71. Planar vertex counting and geometric inverse-square summability

[AmmannBeenkerSummability.lean](SpectralGeometry/AmmannBeenkerSummability.lean)
constructs an injective `planarCode` into
$(\mathbb Z^2)\times\{-2,-1,0,1,2\}^2$. The free coordinates are
$(n_1,n_3)$; the residues subtract the integer floors of
$\alpha(n_1-n_3)$ and $\alpha(n_1+n_3)$ from $n_0$ and $n_2$.
The window bounds each residue. No uniform-separation hypothesis is supplied.

`radius_count_le` proves for every $R\ge0$, with $N=\lceil R+3\rceil$,
```math
\#\{x:|p(x)|\le R\}\le25(2N+1)^2.
```
This is an explicit quadratic upper bound, not an asymptotic density law.
`planar_energy_bound` proves
$1+n_1^2+n_3^2\le5V(x)$. Hence
```math
\frac1{V(x)^2}\le
\frac{25}{(1+n_1^2)(1+n_3^2)}.
```
The product of two convergent integer series, together with the finite
residue code, gives `potential_invSq_summable`:
$\sum_{x\in\mathrm{Vertex}}V(x)^{-2}<\infty$. This is summability of
the actual geometric potential; it assumes neither a sorted enumeration
nor a spectral growth estimate. The bound is not optimized. A separate
uniform-separation estimate is not proved or needed for this argument.

### 4.72. Exact geometric full products and nine-level zero response

[AmmannBeenkerSpectralProducts.lean](SpectralGeometry/AmmannBeenkerSpectralProducts.lean)
proves `AmmannBeenker.exists_nine_level_fullProducts`.
For arbitrary fixed $c,d\in\mathbb C$ with $d\ne0$, it constructs
complete monotone natural-domain eigenbases for $H$ and $H_\tau=H+\tau P_S$,
with $V(x)=1+|p(x)|^2$, matching edge weight $1/16$ and $S=\{|p(x)|\le2\}$.
All baseline and perturbed levels are at least one; $\lambda_n(H)\le3$
for $n<9$. Both full spectra are inverse-square summable.

`HasExactFullSpectralProduct` is proved for each operator: its canonical
product is entire, its zeros are exactly the reflected full real
bounded-inverse spectrum, and its analytic orders are the geometric
eigenspace multiplicities of that same operator. In particular,
```math
D_\tau(s)=\prod_{n\ge0}\left(1-
\frac{(s-c)^2}{d^2\lambda_n(H_\tau)^2}\right),
\qquad z_n^\pm(\tau)=c\pm d\lambda_n(H_\tau).
```
For $0\le\tau\le4$ and $n<9$, the theorem retains the spectral bounds
$\tau/2\le\lambda_n(H_\tau)-\lambda_n(H)\le\tau$ and proves
```math
z_n^\pm(\tau)-z_n^\pm(0)
 =\pm d\bigl(\lambda_n(H_\tau)-\lambda_n(H)\bigr),
\qquad |d|\frac\tau2\le|z_n^\pm(\tau)-z_n^\pm(0)|\le|d|\tau.
```
The four indexed points are zeros of their own products, and both indexed
branches move for $\tau>0$. Repetitions and crossings are allowed: these
are nine multiplicity slots on each branch, not a claim of nine distinct
locations or disjoint zero sets at different parameters.

Only the affine data $c,d$ and $d\ne0$ are supplied. Infinitude, properness,
self-adjoint natural-domain construction, compact shifted resolvents,
positive gaps, spectral enumeration, geometric summability and the nonempty
window come from verified source results. The common domain and affine data
are unchanged along the interval; a resolvent shift may depend on $\tau$.
Normalization and reflected symmetry follow from the existing canonical
product theorems (§2.4). Uniform vertex separation, polygonal coverage,
aperiodicity, optimal constants, numerical cofactor/radius data, relative
determinants and finite-patch errors are not conclusions. Formal verification
is distinct from originality or research-interest assessment.

### 4.73. A radial gap and a stronger nine-level response

[AmmannBeenkerRadialGap.lean](SpectralGeometry/AmmannBeenkerRadialGap.lean)
proves that the internal window has squared radius less than two. The
joint norm identity reduces the small-radius classification to 81 integer
cases. Every admitted vertex with $|p|^2<3+2\sqrt2$ has $|p|\le2$.
Thus `potential_outside_sector_sharp` gives $V\ge4+2\sqrt2$ outside the
same radius-two sector $S$ used in §4.72.

`exists_nine_level_response_sharp` reuses the baseline nine-level theorem,
constructs the perturbed eigenbases, and proves
```math
(4\sqrt2-5)\tau\le\lambda_n(H+\tau P_S)-\lambda_n(H)\le\tau,
\qquad n<9,\quad 0\le\tau\le3+2\sqrt2.
```
The coefficient is approximately $0.65685$. This sharpens the spectral
estimate for the same operator, domain and sector. The full-product
statement of §4.72 retains its original constants and interval.

### 4.74. Compact eigenvectors on the infinite natural domain

[AmmannBeenkerCompactModes.lean](SpectralGeometry/AmmannBeenkerCompactModes.lean)
and [AmmannBeenkerCompactStates.lean](SpectralGeometry/AmmannBeenkerCompactStates.lean)
construct alternating states $a,b$ on the eight-point orbits of
$(1,0,0,0)$ and $(1,1,0,0)$ under
$(n_0,n_1,n_2,n_3)\mapsto(-n_3,n_0,n_1,n_2)$.
Their amplitudes alternate between $+1$ and $-1$, and vanish elsewhere.
Lean checks the window decisions, all matching actions and cancellation
outside the supports. The resulting natural-domain identities are
```math
Ha=\frac{35}{16}a,\qquad Hb=\left(\frac{13}{4}+\sqrt2\right)b,
\qquad \langle a,b\rangle=0,\quad \|a\|^2=\|b\|^2=8.
```
The vectors are explicitly proved nonzero and linearly independent.
These local patterns are known type-A and type-B states; their source is
recorded in the [development notes](docs/compact-mode-crossing.md).
The construction alone is not presented as a novelty claim.

### 4.75. A ring crossing and a single-edge change

[AmmannBeenkerCompactCrossing.lean](SpectralGeometry/AmmannBeenkerCompactCrossing.lean)
uses $A=\operatorname{neighbors}(0)$, the first compact ring, and $K_t=H+tP_A$.
This intervention differs from the radius-two sector $S$. For every real $t$,
```math
K_ta=(35/16+t)a,\qquad K_tb=E_*b,\qquad E_*=13/4+\sqrt2.
```
At $t_*=17/16+\sqrt2$, `compact_crossing` proves the two independent
eigenvector equations at $E_*$. These equations give multiplicity **at least two**. Section 4.78 proves
that it is exactly two; §4.79 certifies a real spectral isolation interval.

The endpoints in $u=\delta_{(1,0,0,0)}-\delta_{(1,1,0,0)}$ are proved
adjacent. Hence $K_{t_*}+\varepsilon|u\rangle\langle u|$ changes an actual
edge weight. For every real $\varepsilon$, `crossing_dark_eigenvector`
proves that the nonzero vector $a+b$ remains an eigenvector at $E_*$.
For the unit vector $q=(a-b)/4$, `crossingBright_energy_response` proves
```math
\langle q,(K_{t_*}+\varepsilon|u\rangle\langle u|)q\rangle=E_*+\varepsilon/4.
```
This is an exact Rayleigh quotient identity. By itself it does not establish
another eigenvalue's value, derivative or quadratic remainder. Section 4.79
provides isolation for the **unperturbed** $K_{t_*}$; the subsequent §§4.93–4.97
establish the genuine moving level, signed shift and quadratic remainder.

### 4.76. The exact central sector and its boundary

[AmmannBeenkerCentralPatch.lean](SpectralGeometry/AmmannBeenkerCentralPatch.lean)
proves that the radius-two sector $S$ is exactly the origin together with
the two eight-site compact rings of §4.74. `sector_eq_centralPatch` gives
an explicit indexing by `Fin 17`, and `sector_card` proves $\#S=17$.
The reverse inclusion uses the joint physical/internal norm identity to
bound the integer lift, followed by exhaustive Lean arithmetic checks.

Write the cyclic ring vertices as $A_i,B_i$, with $i\in\mathbb Z/8\mathbb Z$,
in the rotation order of §4.74. The origin is adjacent to all $A_i$ and
to no $B_i$. Neither ring has edges within itself, and
```math
A_i\sim B_j\quad\Longleftrightarrow\quad j=i\ \text{or}\ j+1=i.
```
All neighbors of the origin and of the first ring lie in $S$.
The compact-state equations recover the full graph degrees:
`firstRing_degree` gives three, and `secondRing_degree` gives four.
Each $B_i$ has exactly two neighbors inside $S$, namely $A_i,A_{i+1}$,
and exactly two outside. `mem_centralBoundaryEdges` identifies the
complete set of boundary edges, oriented from $S$ to its complement;
`centralBoundaryEdges_card` proves that this set has sixteen elements.
This counts edges, not distinct exterior vertices.

These results describe the central block and its coupling locations using
the previously proved compact states and radial barrier. Section 4.78 uses them to exclude additional eigenvectors at $E_*$.
Section 4.79 subsequently bounds the exterior-to-central coupling in norm
and proves an explicit real spectral exclusion window.

### 4.77. The central crossing kernel and centrally supported eigenvectors

[AmmannBeenkerCentralKernel.lean](SpectralGeometry/AmmannBeenkerCentralKernel.lean)
defines the principal block of $K_{t_*}-E_*$ on the exact sector from §4.76.
Its diagonal uses the **full graph degree**, including the contribution
of edges to the exterior. The shifted diagonal is $3/2-E_*$ at the origin
and zero on both rings. The off-diagonal entries come from the actual
coordinate-step adjacency, with weight $-1/16$.

`centralCrossingBlock_kernel_iff` identifies every null
vector in the central indexing as
```math
(0,a,-a,a,-a,a,-a,a,-a,b,-b,b,-b,b,-b,b,-b).
```
The parameters are its coordinates 1 and 9. Lean also checks
that this parametrization is injective, that every such vector is in the
kernel, and that its two coordinate directions are the restrictions of
the previously constructed compact states.

`centralCrossingBlock_restriction` relates this finite block to the actual
infinite natural-domain operator for vectors that vanish outside $S$.
`crossing_eigenvector_of_central_support` then gives the explicit conclusion
```math
K_{t_*}x=E_*x,\qquad x|_{S^c}=0
\quad\Longrightarrow\quad
x=x(A_0)a+x(B_0)b,
```
where $a,b$ on the right denote the compact states of §4.74. The finite
calculation uses the second-ring equations to force alternating first-ring
amplitudes; the origin equation forces its amplitude to vanish; the
first-ring equations then force alternation on the second ring.

The support condition is a hypothesis of this lemma. Section 4.78 derives
it for every crossing eigenvector on the infinite domain.
Neither a gap nor a quantitative splitting estimate follows from this
finite-block calculation alone. The gap is established separately in
§4.79, while the one-edge splitting was subsequently established in §§4.93–4.97.

### 4.78. Central support and exact multiplicity of the infinite crossing

[AmmannBeenkerCrossingMultiplicity.lean](SpectralGeometry/AmmannBeenkerCrossingMultiplicity.lean)
removes the support hypothesis in §4.77. For an arbitrary
natural-domain eigenvector $x$ at $E_*$, write
$L=K_{t_*}-E_*$, $p=P_Sx$ and $q=x-p$. Finite coordinate projection preserves
the natural domain, so every operator evaluation below has its domain witness.

All neighbors of a first-ring vertex lie in $S$, hence $Lq$ vanishes on
that ring. Since $Lx=0$, $Lp$ also vanishes there. The finite central-form
identity and symmetry give
```math
\langle q,Lq\rangle=\langle p,Lp\rangle
  =(3/2-E_*)|p(0)|^2\le0.
```
The previously proved exterior potential barrier and positivity of the
interaction, including the first-ring intervention, supply
```math
(3/4+\sqrt2)\|q\|^2\le\langle q,Lq\rangle.
```
The strictly positive coefficient forces $q=0$. The theorem
`crossing_eigenvector_central_support` therefore derives central support
from the full infinite eigenvector equation. `crossing_eigenvector_representation`
then reuses §4.77 to express every eigenvector in the two compact directions.

`crossingEigenspaceCoordinates` constructs a linear equivalence between
the actual eigenspace inside the natural domain and $\mathbb R^2$, using
the amplitudes at $A_0=(1,0,0,0)$ and $B_0=(1,1,0,0)$ in lift coordinates.
Together the representation and dimension theorems give
```math
\ker(K_{t_*}-E_* I)=\operatorname{span}_{\mathbb R}\{a,b\},
\qquad \dim_{\mathbb R}\ker(K_{t_*}-E_* I)=2,
```
where domain vectors are identified with their images in real $\ell^2$.
The span description uses `crossing_eigenvector_representation` together
with the eigenvector equations of §4.75; `crossingEigenspace_finrank` gives the
dimension. The exterior lower bound above is a form estimate on the
exterior component. This §4.78 argument alone gives no numerical distance
to every other spectral level; §4.79 establishes that distance conservatively.
Quantitative motion of the second level after an edge change is established separately in §§4.93–4.97.

**Palomar registration:** The exact-multiplicity result in this section, represented
by the Comparator-selected `crossingEigenspace_finrank` and
`crossing_eigenvector_representation` statements, was registered as
**PALOMAR-2026-11-06-000012 (version 1)** on 2026-11-06. The separate
spectral-gap theorems of §4.79 are not Comparator-selected statements.


### 4.79. A conservative quantitative real spectral gap at the crossing

[AmmannBeenkerCrossingGapCycle.lean](SpectralGeometry/AmmannBeenkerCrossingGapCycle.lean),
[AmmannBeenkerCrossingGapFinite.lean](SpectralGeometry/AmmannBeenkerCrossingGapFinite.lean)
and
[AmmannBeenkerCrossingGapOrthogonality.lean](SpectralGeometry/AmmannBeenkerCrossingGapOrthogonality.lean)
upgrade the exact crossing of §§4.75–4.78 to a **quantitatively isolated
point of the full real spectrum**. The operator and its domain are unchanged:
$K_t=H+tP_A$ on $D(V)$, with
$t_*=17/16+\sqrt2$ and $E_*=13/4+\sqrt2$.

For a genuine eigenvector at $E\ne E_*$, set $r=|E-E_*|$ and decompose
$x=u+q$, where $u=P_Sx$ is supported on the exact 17-vertex central
sector and $q=x-u$ is exterior. Orthogonality to the two compact
crossing modes eliminates the alternating-ring kernel directions.
`crossingCentralBlock_norm_sq_lower` then gives the central finite-block
squared singular-value bound $1/576$, equivalent to a norm factor $1/24$.
The sixteen oriented boundary edges and the mixed-term estimate yield
`crossingResidual_exterior_projected_norm_le`, controlling the entire
exterior-to-central projected residual with coefficient $1/4$.

The resulting natural-domain inequalities, proved as
`crossingCentralEnergy_off_crossing_bound` and
`crossingExteriorEnergy_off_crossing_linear_bound`, are
```math
\left(\frac1{24}-r\right)\|u\|\le\frac14\|q\|,
\qquad
\left(\frac34+\sqrt2-r\right)\|q\|\le\frac14\|u\|.
```
The strict Schur margin in `crossingGapCandidate_block_no_solution`
forces both norms to vanish for $0\le r\le1/128$. Thus
`crossingGapCandidate_no_other_full_eigenvector` excludes every
nonzero full-domain eigenvector at a different energy in that window.

Crucially, the result does **not** stop at the point spectrum.
`crossingRealSpectrum_iff_full_eigenvector` applies the established
compact-resolvent real spectral-mapping theorem (§§4.21 and 4.32)
to the concrete potential, using its proved lower bound and finite
onsite sublevels. Hence `crossingGapCandidate_no_other_realSpectrum`
and `crossingGapCandidate_realSpectrum_isolated` certify
```math
\sigma_{\mathbb R}(K_{t_*})\cap
\left[E_*-\frac1{128},\,E_*+\frac1{128}\right]=\{E_*\}.
```
Here $\sigma_{\mathbb R}$ is the **real bounded-inverse spectrum on
the natural domain**, not a newly formalized complex-spectrum API.
The inclusion of $E_*$ follows from the nonzero compact-state
eigenvectors (§4.75); the exclusion of all other points follows from
§4.79. The closed interval, including its endpoints, is covered.

The value $g=1/128$ is a **certified conservative lower bound on
the isolation radius**, not the exact spectral spacing or an optimal
constant. This theorem does not assert stability of the twofold
crossing under arbitrary perturbations, identify the moving eigenvalue
after the one-edge change, or provide a derivative, remainder or
finite-patch zero certificate. The **historical first Palomar registration** selected the
exact-multiplicity statements of §4.78. The gap theorems are not
selected as separate statements in any of the three Palomar registrations (§§4.78, 4.98), but remain included
in the full Lean/Mathlib source build.

### 4.80. First exact algebraic results for controlling the two compact modes

This new step connects the crossing (§§4.75, 4.78), its certified spectral
isolation (§4.79), and the proposed coherent-control problem (§6.4).
The modules
[`AmmannBeenkerEdgeControl.lean`](SpectralGeometry/AmmannBeenkerEdgeControl.lean)
and
[`AmmannBeenkerTwoControlAlgebra.lean`](SpectralGeometry/AmmannBeenkerTwoControlAlgebra.lean)
extend the previously proved natural-domain equations. Both modules are
imported by the main Lean library and checked in the full CI proof build.
The statements here are exact static identities, not yet a dynamical
control or state-preparation theorem.

Let `a` and `b` be the original compact modes (each of squared norm
eight), let `W` be the actual one-edge Laplacian perturbation, and write
`D = (a + b)/4` for their **unit** equal-amplitude combination.
The edge has an exact nonzero cross-mode matrix element. More generally,
its bilinear form on two combinations is

```math
\langle r a+s b,\,W(u a+v b)\rangle=(r-s)(u-v).
```

This is an exact statement about the full infinite Hilbert space, **not**
a claim that the two-dimensional mode plane is invariant under `W`.
The new lemmas also show that `D` has unit norm and `W D=0`.
Building on `crossing_dark_eigenvector` (§4.75), they express its
stationarity as a **normalized, natural-domain eigenvector theorem**:
for every real edge change `ε`, the full perturbed operator still has
`D` at the original crossing energy.

The second module proves that the compact-mode plane stays exactly
invariant under any detuning and adds the energy response for `t=t_*+δ`:

```math
K_{t_*+\delta}a=(E_*+\delta)a,\qquad
K_{t_*+\delta}b=E_*b.
```

When the two controls are allowed together, the operator acts on the
dark state by the exact identity

```math
(K_{t_*+\delta}+\varepsilon W)D
=E_*D+\frac{\delta}{4}a.
```

Thus the edge alone leaves the dark direction fixed, while detuning
`t` changes it within the compact-mode plane. Neither identity asserts
a controlled quantum evolution. The crucial open work is to establish a
complex unitary dynamics and bound the excitation of the rest of the
infinite spectrum under a finite edge pulse.

See [the edge-control research note](docs/edge-control-reachability.md) for
the proposed two-pulse strategy, the predicted obstruction to edge-only
universal preparation, and its currently unproved dynamical requirements.
This new work is **not** part of the previous Palomar-registered theorem.

### 4.81. Exact qubit/leakage bookkeeping after a temporary pulse

The control goal has three phases: prepare an initial compact mode at the
crossing, apply a temporary edge pulse (and optionally detune `t`), and
restore both controls. Restoring the original operator restores the original
eigenvalues, eigenspaces and certified gap. **It does not restore the
initial state**: any amplitude transferred to unwanted modes can remain.

The new
[`AmmannBeenkerQubitLeakage.lean`](SpectralGeometry/AmmannBeenkerQubitLeakage.lean)
imports §4.80 and defines a decomposition for *every* state `x` in
the **full real infinite-graph Hilbert space**. Using the original
orthogonal compact eigenvectors `a,b`, each of squared norm eight, put

```math
r=\langle a,x\rangle/8,\quad s=\langle b,x\rangle/8,
\qquad p=ra+sb,\quad\chi=x-p.
```

The new source proves `⟨a,χ⟩=⟨b,χ⟩=0`; thus `p` is
the true orthogonal two-mode component, and `χ` captures **all**
other modes, not only a hypothetical third one. Its exact norm identity is

```math
\|x\|^2=8(r^2+s^2)+\|\chi\|^2.
```

For unit-norm `x`, if `‖χ‖²≤η`, the total weight in
the compact-mode plane is at least `1-η`. The proof makes **no**
assumption that the transient edge operator preserves this plane.
It also does not prove that the *individual* amplitudes have the
requested values. The §4.81 declarations have now passed the full Lean CI verification.

A second theorem records what *is* guaranteed by restoring the
original operator `K_*` after the pulse:

```math
K_*p=E_*p.
```

This is a genuine natural-domain eigenvector equation for the compact
part of any final state; it is **not** a claim that `χ=0` or that
switching the pulse off erases the leakage.

**Exact static obstruction to an ideal two-level edge action.** The
same Lean module now computes the full-space edge response of the
original compact mode `a`. It proves

```math
\|Wa\|^2=2,\quad
\|PWa\|^2=\tfrac14,\quad
\|(I-P)Wa\|^2=\tfrac74>0,
```

where `P` is the orthogonal projection onto `span{a,b}`. For the
normalized mode `A=a/√8`, the corresponding external response is

```math
\|(I-P)WA\|^2=\tfrac7{32}.
```

More generally, the same source computes the off-plane response of
**every real combination** of the unnormalized compact modes:

```math
\|(I-P)W(ra+sb)\|^2=\tfrac74(r-s)^2.
```

In particular, the direct edge-induced off-plane response vanishes
for equal amplitudes `r=s` (the protected dark direction), but is
strictly positive whenever `r≠s`. The control cannot be modeled
as a closed exact two-level interaction on the entire qubit plane.

Thus the single-edge perturbation **really does couple A to modes
outside the qubit plane**. This is much stronger than merely saying
that leakage is possible: it is an exact nonzero numerical certificate
in the complete infinite graph, not a truncated finite model. The
exact calculation has passed Lean CI verification.

**Full two-control response.** The latest Lean extension also
treats the complete natural-domain action of both available controls,
`K_(t_*+δ)+εW`. For any real compact-mode input `ra+sb`,
the off-plane response has the exact squared norm

```math
\|(I-P)(K_{t_*+\delta}+\varepsilon W)(ra+sb)\|^2
=\tfrac74\,\varepsilon^2(r-s)^2.
```

The detuning `δ` disappears *exactly*: changing `t`
does not directly excite external modes, whereas the connecting
edge does whenever `r≠s`. These are static natural-domain
identities, **not** bounds on the leakage after a finite pulse.
This two-control result belongs to the latest Lean-verified extension.

**Careful distinction:** this number measures the *off-plane
component of the perturbation vector*, not leakage probability
after any particular pulse. Under a future complex unitary
Schrödinger model, it predicts a short-time leakage probability
`(7/32) ε² τ² + o(τ²)` for a constant edge pulse from A. That
short-time asymptotic is **not yet formalized in Lean**.
It does **not** rule out cancellation of external amplitudes at
a specially chosen final time, nor does it establish a universal
lower bound on final pulse leakage.

**Next stage: complex quantum dynamics.** Complexify the Hilbert space,
normalize the modes as `A=a/√8, B=b/√8`, and define orthogonal
projections `P` onto their two-dimensional span and `Q=I-P`.
For normalized quantum states the corresponding probability budget is

```math
|\langle A,\psi\rangle|^2+
|\langle B,\psi\rangle|^2+\|Q\psi\|^2=1.
```

Construct the restored self-adjoint Hamiltonian's unitary evolution
`U_0(τ)` and prove `P U_0(τ)=U_0(τ)P`. It would then follow that
`‖Q U_0(τ)ψ‖²=‖Qψ‖²`: **leakage already present
when the pulse is switched off persists**, while the two-mode part
only acquires a common phase. These time-evolution results are not
yet in the Lean library.

Finally construct the piecewise-constant edge/`t` pulse propagators
and seek a bound, up to a physically irrelevant global phase,

```math
\inf_{\theta\in\mathbb R}
\|U_{\mathrm{pulse}} A-e^{i\theta}(\alpha A+\beta B)\|
\le\eta,\qquad |\alpha|^2+|\beta|^2=1.
```

This **full-state error** would imply `‖Q U_pulse A‖≤η`
and hence leakage probability at most `η²`, while also
certifying the desired complex amplitudes and relative phase.
The existing real spectral gap is a possible input for such an
estimate, not proof of it. See §6.4 and
[the research note](docs/edge-control-reachability.md).

### 4.82. Uniform leakage estimate conditional on a nearby invariant spectral plane

The most useful next analytical step is not merely to make an edge
pulse *short*: to produce a significant mixing of A and B using a
weak edge weight, its duration may have to grow as the weight shrinks.
A naive time-integrated bound proportional to `|ε| T` is
therefore insufficient.

The new
[`QubitLeakagePulseBound.lean`](SpectralGeometry/QubitLeakagePulseBound.lean)
formalizes a **generic, conditional, time-uniform estimate** in a real
normed space. It assumes three bounded linear maps:

- `P`, the desired compact-mode projection;
- `S`, a projection onto a nearby *invariant* (perturbed) plane;
- `U`, a norm-preserving evolution map that commutes with `S`.

Assume the initial vector `x` is entirely in the desired plane
(`Px=x`), and the projections are quantitatively close:

```math
\|(P-S)y\|\le d\,\|y\|\quad\text{for every }y.
```

The Lean lemma derives **without assuming an evolution duration**
that

```math
\|Ux-PUx\|\le 2d\,\|x\|.
```

For `‖x‖=1` and `d≥0`, the squared-norm leakage is at
most `4d²`. The proof is only the triangle inequality: compare
the final state with the invariant perturbed plane and account for
the initial and final differences between `P` and `S`.
The result is **fully conditional on the displayed hypotheses**,
and is not yet instantiated with the Ammann–Beenker Hamiltonian or
a complex Schrödinger propagator. It does not prove that a useful
qubit rotation can be reached.

**Graph-specific goals still open.** The existing full crossing gap
`g=1/128` suggests constructing a two-dimensional perturbed
spectral projector `P_ε` for a sufficiently weak fixed edge
perturbation and proving an operator-norm estimate
`‖P_ε-P‖≤d(ε)`, with `d(ε)→0` as `ε→0`. One must
then construct the complex unitary pulse propagator, prove it
commutes with `P_ε`, and instantiate the abstract lemma. This
would give uniformly small **final leakage for a long but weak
pulse**, independently of pulse duration. Finally one must
separately prove that the same pulse yields the intended relative
amplitudes/phase; a leakage bound alone does not prepare an
arbitrary target.

This sequence distinguishes three different assertions:
the exact static off-plane response (§4.81), the **conditional**
time-uniform estimate (this section), and the still-unproved
full infinite-graph coherent-control protocol (§6.4).

### 4.83. From the certified 1/128 gap to a quantitative bound on nearby eigenvectors

The next theorem now has a **concrete numerical target**. In
[`AmmannBeenkerQubitLeakage.lean`](SpectralGeometry/AmmannBeenkerQubitLeakage.lean),
the rank-one edge operator `W` is shown to have **exact operator norm
`‖W‖=2`**, not merely a finite-dimensional compression. Hence

```math
\|\varepsilon W x\|\le 2|\varepsilon|\,\|x\|.
```

The new
[`AmmannBeenkerNearCrossingEigenvectors.lean`](SpectralGeometry/AmmannBeenkerNearCrossingEigenvectors.lean)
then sets up an exact full-natural-domain eigenvector comparison. Let
`K_*` be the crossing Hamiltonian, `P` the orthogonal projection
onto its two compact modes, `Q=I-P`, `E_*` its crossing energy, and
`g=1/128`. A perturbed eigenvector `x` satisfying

```math
(K_*+\varepsilon W)x=\lambda x
```

obeys the **unconditional residual identity**

```math
(K_*-E_*)x=(\lambda-E_*)x-\varepsilon Wx.
```

To turn this into a bound on the *external component* `Qx`, we
use the **reduced-gap residual estimate**

```math
g\,\|Qy\|\le\|(K_*-E_*)y\|
\qquad(y\in\operatorname{Dom}K_*).
```

In a complete self-adjoint spectral decomposition this is the
quantitative form of spectral isolation: every component outside
the `E_*` eigenspace has spectral distance at least `g`.
The graph's real spectral exclusion within radius `g` is already
certified (§4.79). The latest new lemma
`crossingReducedGapResidualEstimate_full` now also derives
this norm inequality from the previously proved full eigenbasis
existence and operator symmetry (§4.84); **these graph-specific declarations passed Lean CI before the new §4.85 extension**.

**Quantitative theorem, with the gap hypothesis now discharged
in source:** the latest declaration derives

```math
g\,\|Qx\|\le
\bigl(|\lambda-E_*|+2|\varepsilon|\bigr)\|x\|.
```

If the perturbed eigenvalue is also known to satisfy the usual
bounded-perturbation window `|λ-E_*|≤2|ε|`, this yields an explicit
numerical **one-sided eigenvector estimate**

```math
\boxed{\|Qx\|\le512|\varepsilon|\,\|x\|.}
```

For eigenvectors satisfying that energy-window hypothesis,
decreasing `|ε|` makes the proposed upper bound tend to zero.
This is precisely how the isolated gap can protect the two-mode
state against weak edge coupling.

**Two important boundaries:** the graph-specific residual inequality
has now been derived in source from complete-basis and gap theorems,
Lean-verified. The **perturbed eigenvalue-shift window** remains
an explicit hypothesis of this particular estimate; §§4.93–4.97 later establish the requisite window for the actual moving level. Also, an inequality on individual perturbed
eigenvectors is **not yet** an operator-norm estimate
`‖P_ε-P‖` for the whole perturbed two-dimensional spectral
projection. The latter requires constructing and identifying that
cluster, including its dimension, before §4.82's duration-independent
pulse estimate can be applied. This is *not* a proof of arbitrary
state preparation.

The full graph-specific gap-to-residual instantiation is **already
Lean-verified** (§4.84). Sections 4.85–4.88 also obtain a
**different**, conditional graph-specific leakage bound uniform
in pulse duration directly from residual conservation, without a
perturbed spectral projector. The isolated simple point-spectrum pair is now
established in §§4.93–4.97; constructing its spectral projector and proving
the operator-norm projector estimate of §4.82 remain open as a separate,
potentially sharper route; the
physical complex quantum propagator and nontrivial rotation
also remain open.

### 4.84. Why spectral isolation yields a residual bound: infinite-dimensional Parseval

The following link in the proof is represented by two
Lean-verified theorem packages.

**Generic complete-basis theorem.** The new
[`DomainEigenbasisGapResidual.lean`](SpectralGeometry/DomainEigenbasisGapResidual.lean)
starts with a genuine complete real *domain eigenbasis* `b_i`
of a symmetric (possibly unbounded) operator `K`, with energies
`E_i`. Suppose every energy other than `E_*` has distance at
least `g>0` from `E_*`. For every natural-domain vector `y`
having zero coefficient in all eigendirections with `E_i=E_*`,
Parseval and the eigenvector equation give

```math
g\,\|y\|\le\|(K-E_*)y\|.
```

This does not assume finite dimension or a bounded Hamiltonian.
In words: if an off-qubit vector has significant size, its
`(K-E_*)` residual cannot be tiny, because *every* frequency
participating in it is separated from `E_*`.

**Specialization to the real Ammann–Beenker crossing.**
The new `crossingReducedGapResidualEstimate_of_domainEigenbasis`
in
[`AmmannBeenkerNearCrossingEigenvectors.lean`](SpectralGeometry/AmmannBeenkerNearCrossingEigenvectors.lean)
uses the previously established theorem that the **entire**
`E_*` eigenspace is `span{a,b}`, plus the explicit
`1/128` exclusion of every other eigenvalue. It derives the
missing residual estimate of §4.83 from **a supplied complete
domain eigenbasis and a symmetry proof for the original crossing
operator**:

```math
\tfrac1{128}\|(I-P)x\|\le\|(K_*-E_*)x\|.
```

The new `crossingReducedGapResidualEstimate_full` declaration
goes a step further: it **constructs the required complete crossing
eigenbasis** by invoking the repository's earlier
`onsitePlusBounded_exists_orderedEigenbasis` theorem for the proper
onsite potential, and supplies symmetry via
`finiteSectorCorrection_symmetric`. Hence the full reduced-gap
inequality is an **unconditional Lean-verified theorem for the
actual infinite graph**, not merely a supplied hypothesis.
**The gap-to-residual Lean code has passed CI.**

Consequently, the latest `crossingEdge_perturbed_eigenvector_gap_bound_full`
states without any *additional* gap assumption that

```math
\tfrac1{128}\|(I-P)x\|\le
\bigl(|\lambda-E_*|+2|\varepsilon|\bigr)\|x\|
```

for **every real perturbed full-domain eigenvector** at `λ`.
The related `crossingEdge_nearby_eigenvector_leakage_le_full`
gives `‖(I-P)x‖≤512|ε|‖x‖` whenever the
energy-window hypothesis `|λ-E_*|≤2|ε|` holds. These are
Lean-verified mathematical statements, *not* a spectral
projector or time-evolution result.

Even that eigenvector estimate does not yet prove
`‖P_ε-P‖→0`. The two simple eigenvalues in the relevant point-spectrum
window were subsequently certified in §§4.93–4.97. The corresponding
orthogonal spectral projector, its norm estimate and the
full complex unitary evolution are still needed to invoke the time-uniform pulse
bound of §4.82.

### 4.85. Uniform post-pulse leakage without a perturbed spectral projector

The verified §4.84 reduced-gap inequality gives a more direct route
to controlling **all** external modes during a constant-strength
connecting-edge pulse, without first constructing the perturbed
two-dimensional spectral projector.

The new
[`AmmannBeenkerPulseResidualBound.lean`](SpectralGeometry/AmmannBeenkerPulseResidualBound.lean)
introduces the *shifted perturbed-Hamiltonian residual*

```math
R_\varepsilon(x)=(K_*+\varepsilon W-E_*)x.
```

Let `x` be an exact initial crossing eigenvector
(`K_*x=E_*x`) and `y` a possible state after the pulse,
both in the original infinite-graph natural domain.
If the final state satisfies the two explicit conservation laws

```math
\|y\|=\|x\|,\qquad
\|R_\varepsilon(y)\|=\|R_\varepsilon(x)\|,
```

then the new Lean theorem aims to certify

```math
\boxed{\|(I-P)y\|\le512|\varepsilon|\,\|x\|.}
```

For normalized initial states, this yields the corresponding
**squared-norm** bound `‖(I-P)y‖²≤(512|ε|)²`.
The proof combines the exact edge norm `‖W‖=2` and
the established infinite-graph reduced gap `g=1/128`:

```math
g\,\|(I-P)y\|
\le\|(K_*-E_*)y\|
\le\|R_\varepsilon(y)\|+2|\varepsilon|\,\|y\|
\le4|\varepsilon|\,\|x\|.
```

Crucially, **there is no factor depending on the elapsed pulse
time**. For a genuine unitary propagator of the *fixed*
self-adjoint Hamiltonian `K_*+εW`, the two conservation laws
follow from norm preservation, invariance of the natural domain,
and commutation with its own generator. The real-space Lean
statement deliberately assumes exactly these consequences:
**it does not yet construct a complex Schrödinger propagator**.

This bound sidesteps the need for a perturbed spectral projector
when the only goal is small external leakage from a constant
edge pulse. It does **not** assert that the pulse transfers the
requested amplitudes between A and B, controls their complex
relative phase, or achieves arbitrary-state preparation.
A protocol with changing `t` and/or piecewise-constant `ε`
also needs segment-by-segment analysis; conservation of
`R_ε` applies only during a segment with a fixed Hamiltonian.

**Lean status:** §§4.85–4.89, including the intertwining and switch-off
statements, are Lean-verified. The earlier unsubmitted Palomar candidate
is documented in §4.92 and the later registered L5 selection in §4.98.
### 4.86. Residual conservation follows from Hamiltonian intertwining

Section 4.85 established a time-uniform edge-pulse leakage inequality
under **two conservation hypotheses** for the full graph. The next
formal step removes the *independent* shifted-residual-conservation
assumption: it is a consequence of the operator intertwining identity.

The new
[`AmmannBeenkerPulseIntertwining.lean`](SpectralGeometry/AmmannBeenkerPulseIntertwining.lean)
takes a continuous real-linear map `U` on the full infinite-graph
Hilbert space and requires:

- **Isometry:** `‖Uz‖ = ‖z‖` for every full-space vector `z`.
- **Natural-domain invariance:** `Ux` lies in the onsite domain
  whenever `x` does.
- **Hamiltonian intertwining on that domain:**

  ```math
  (K_*+\varepsilon W)Ux=U(K_*+\varepsilon W)x.
  ```

The new lemma `crossingPulseResidual_intertwines` proves, by
linearity and commutation, the **exact vector identity**

```math
R_\varepsilon(Ux)=U R_\varepsilon(x),
\quad R_\varepsilon=K_*+\varepsilon W-E_*.
```

Therefore `crossingPulseResidual_norm_conserved` proves
`‖R_ε(Ux)‖=‖R_ε(x)‖` from isometry; it is **no longer
a separate assumption**. Applying the §4.85 graph-specific
gap estimate gives, for every initial crossing eigenvector,
the Lean-verified theorem

```math
\boxed{\|(I-P)Ux\|\le512|\varepsilon|\,\|x\|.}
```

The same module also proves the statement for a supplied family
`U_ε(τ)` for **all real `τ`**, plus the squared-norm bound
`‖(I-P)U_ε(τ)x‖²≤(512|ε|)²` when `‖x‖=1`.
There is no elapsed-time factor and no perturbed spectral
projection in these statements. The graph and the selected
connecting edge remain unchanged.

**Crucial remaining distinction:** the family `U_ε(τ)` is
supplied as a hypothesis. This new real-Hilbert-space result
does *not* construct the physical complex Schrödinger unitary
`e^{-iτ(K_*+εW)}`, establish its generator or domain
invariance, or demonstrate a useful A/B rotation. Nor does
it assert a group law or continuity in time for the supplied
family. It simply proves that these concrete operator-theoretic
properties are **sufficient** for the previously certified
leakage conclusion.

**Lean status:** this intertwining module and its root import
have passed the full Lean verification. The statement remains
conditional on the supplied real isometry and domain/commutation
hypotheses; it does not certify state preparation.

### 4.87. The actual selected-edge pulse Hamiltonian is self-adjoint on its natural real domain

The next step specializes the existing genuine Mathlib
`LinearPMap` self-adjointness theorem to the **same physical
selected edge** used throughout §§4.80–4.86.

The new
[`AmmannBeenkerPulseSelfAdjoint.lean`](SpectralGeometry/AmmannBeenkerPulseSelfAdjoint.lean)
defines the full unbounded partial operator `crossingEdgePulsePMap ε`
on the real infinite-graph Hilbert space. Its exact domain
is `infiniteOnsiteDomain potential`; for every real `ε`,
its action there is

```math
K_\varepsilon x=(K_*+\varepsilon W)x.
```

The source derives self-adjointness by using a zero-color
matching family, the known self-adjointness machinery for a
proper natural onsite domain, the symmetry of the original
bounded ring interaction, and the exact symmetry of the
rank-one selected-edge perturbation:

```math
\langle Wx,y\rangle=\langle x,Wy\rangle.
```

The Lean-verified theorem

```lean
crossingEdgePulsePMap_isSelfAdjoint (ε : ℝ) :
  IsSelfAdjoint (crossingEdgePulsePMap ε)
```

has **no small-ε restriction**: the perturbed operator
is self-adjoint for any real edge weight on its original
natural domain. The self-adjointness and exact-domain
statements concern the **full infinite operator**, not
an effective 2×2 matrix or a finite graph.

**Limitations:** this is self-adjointness over **ℝ**
in Mathlib's partial-linear-map API. Constructing the
physical complex Hilbert-space counterpart and its
strongly continuous unitary Schrödinger propagator,
including `U_ε(τ)D(K_ε)⊆D(K_ε)` and
`K_εU_ε(τ)=U_ε(τ)K_ε`, is still a separate task.
The §4.86 implication from these conditions to
residual conservation and the leakage estimate does
not by itself supply that physical evolution.

**Lean status:** this full-graph real self-adjointness theorem
and §4.86 have passed the full Lean verification. At that checkpoint, the original Palomar selection and its
Challenge/Comparator files were unchanged. The later
generator-response candidate is archived in §4.92, and the
later registered L5 selection is in §4.98. The first
registration remains immutable.

### 4.88. A controlled pulse followed by free evolution after switching the edge off

The new
[`AmmannBeenkerPostpulseSwitchOff.lean`](SpectralGeometry/AmmannBeenkerPostpulseSwitchOff.lean)
formalizes an ON/OFF protocol using the **same selected edge**.

The pulse changes the Hamiltonian from `K_*` to
`K_ε=K_*+εW`; switching the edge off returns it to
`K_*`. These two different fixed Hamiltonians have
**different shifted-residual conservation laws**.
We therefore track

```math
R_\varepsilon(\psi)=(K_*+\varepsilon W-E_*)\psi,\qquad
R_0(\psi)=(K_*-E_*)\psi.
```

Suppose the initial vector `x` lies in the original
two-dimensional crossing eigenspace. After the active
pulse, let `y` be a full natural-domain state satisfying

```math
\|y\|=\|x\|,\qquad
\|R_\varepsilon(y)\|=\|R_\varepsilon(x)\|.
```

When the edge is switched off, the actual unperturbed
residual at the switching instant is bounded:

```math
\boxed{\|R_0(y)\|\le4|\varepsilon|\,\|x\|.}
```

This follows from `R_0(y)=R_ε(y)-εWy`,
`‖W‖=2`, and `R_ε(x)=εWx`. It does not
assume that the pulse leaves the qubit plane invariant.

Now let `z` be any final state of a free segment whose
**unperturbed** residual is conserved:

```math
\|R_0(z)\|=\|R_0(y)\|.
```

The full infinite-graph reduced-gap theorem yields

```math
\boxed{\|(I-P)z\|\le512|\varepsilon|\,\|x\|.}
```

The new module also proves the same result for any
supplied family of norm-preserving, domain-preserving
real-linear maps intertwining `K_*`, and then for a
**two-family ON/OFF protocol**: the first intertwines
`K_ε`, the second intertwines `K_*`. The leakage
bound is uniform over **both** elapsed times. There is
no approximation that treats the unperturbed and
perturbed residuals as if they were identical.

**What remains open:** these real-linear intertwining
families are supplied as assumptions. We have not yet
constructed a complex Schrödinger propagator or
demonstrated nontrivial A/B rotations. This result
certifies the consequences of the two segment-wise
conservation laws, **not** the existence of the
physical dynamics.

**Lean status:** §4.88 and its root import have passed the
full Lean verification, along with §§4.85–4.87.

### 4.89. An exact complex-phase Schrödinger trajectory for the dark mode

The selected edge has an exceptional *exact* eigenvector:
the normalized equal-amplitude combination
`crossingDark=(compactA+compactB)/4` is an eigenvector at
`E_*` for **every** real selected-edge strength `ε`;
the rank-one edge acts as zero on this vector.

The new
[`AmmannBeenkerDarkSchrodinger.lean`](SpectralGeometry/AmmannBeenkerDarkSchrodinger.lean)
constructs an explicit time-dependent solution, for every
real `τ`, in the full graph's natural domain:

```math
\psi_\varepsilon(\tau)=
e^{-i E_*\tau}\,\mathrm{dark}
=\underbrace{\cos(E_*\tau)\,\mathrm{dark}}_{\operatorname{Re}\psi}
-i\underbrace{\sin(E_*\tau)\,\mathrm{dark}}_{-\operatorname{Im}\psi}.
```

The source works with its real and imaginary parts as
**two full real Hilbert-space vectors**, each with an
explicit natural-domain lift. This representation avoids
assuming a yet-unconstructed complex infinite-graph
Hamiltonian. Using Mathlib's trigonometric derivative
lemmas and the **full** eigenvector identity, it verifies
the real and imaginary Schrödinger equations:

```math
\frac{d}{d\tau}\operatorname{Re}\psi
=(K_*+\varepsilon W)\operatorname{Im}\psi,
\qquad
\frac{d}{d\tau}\operatorname{Im}\psi
=-(K_*+\varepsilon W)\operatorname{Re}\psi.
```

Together these say `i∂_τψ=K_εψ` for this particular
phase trajectory. The module additionally establishes

```math
\operatorname{Re}\psi(0)=\mathrm{dark},
\quad \operatorname{Im}\psi(0)=0,
\quad
\|\operatorname{Re}\psi(\tau)\|^2+
\|\operatorname{Im}\psi(\tau)\|^2=1,
```

and zero leakage from **both** components for all times.
There is no small-`ε` restriction: the dark state
remains completely decoupled from this one edge at any
strength.

**Important limitation:** this verifies a *single explicit*
solution of the Schrödinger equation. It is not a
construction of the general complex unitary propagator,
does not prove its uniqueness or group law, and does not
show a nontrivial `A\leftrightarrow B` rotation. The
imaginary/real pair is a representation of this complex
trajectory, not yet a complete complex Hilbert-space
construction or generic dynamics theorem.

**Lean status:** this dark-state Schrödinger module and all prior
§§4.80–4.88 control declarations are Lean-verified.

### 4.90. Consolidated verified control checkpoint and outstanding dynamics

This section consolidates **previously proved and CI-checked** facts.
It does not introduce an additional Lean theorem and does not
replace §§4.75–4.89 or any earlier spectral-product results.

**Exact infinite-graph geometry and spectrum (§§4.74–4.79).**
At `t_*=17/16+√2`, two orthogonal eight-site compact
modes `a,b` have squared norm `8` and common energy
`E_*=13/4+√2`. They span the **entire real eigenspace**
at that energy, of dimension exactly two. The complete
real spectrum has no other point within the closed radius
`g=1/128` around `E_*`. These are properties of the
**full infinite graph**, not a finite truncation.

**One fixed control edge (§§4.80–4.83).**
We retain the actual adjacent lattice vertices
`u=(1,0,0,0)` and `v=(1,1,0,0)`; the bounded rank-one
edge operator is `W=|δ_u-δ_v⟩⟨δ_u-δ_v|` with
exact full-space norm `‖W‖=2`.
The normalized modes `A=a/√8` and `B=b/√8`
define the orthogonal projection `P` onto their span,
with leakage projection `Q=I-P`. The edge has
a nonzero A/B coupling and a **nonzero external
response**, so the two-mode plane is not asserted
to be invariant while the edge is on. The normalized
dark vector `D=(A+B)/√2=(a+b)/4` satisfies
`WD=0` and is an exact full-domain eigenvector of
`K_*+εW` at `E_*` for **all real ε**.

**Gap, perturbed eigenvectors and duration-independent
conditional pulse bounds (§§4.83–4.88).**
The complete eigenbasis and certified gap imply, for
every `x∈Dom K_*`,

```math
\frac1{128}\|Qx\|\le\|(K_*-E_*)x\|.
```

For any perturbed eigenvector of `K_*+εW` at `λ`,
the full graph obeys

```math
\frac1{128}\|Qx\|\le
  (|\lambda-E_*|+2|\varepsilon|)\|x\|.
```

In particular, the additional **eigenvalue-window**
assumption `|λ-E_*|≤2|ε|` gives
`‖Qx‖≤512|ε|‖x‖`. This does not by itself
construct a nearby perturbed rank-two projector.

For an initial crossing eigenvector `x`, if
a constant-strength pulse has a final state `y`
with `‖y‖=‖x‖` and with its **perturbed**
residual norm `‖(K_*+εW-E_*)y‖` conserved,
then `‖Qy‖≤512|ε|‖x‖`. If the edge is then
switched **off** and the following free segment
conserves the **unperturbed** residual norm, the
same bound holds at every such final state `z`:

```math
\boxed{\|Qz\|\le512|\varepsilon|\,\|x\|.}
```

The results also derive these residual conservation
laws for **supplied real-linear isometries** that
preserve the original natural domain and intertwine
the corresponding fixed generator. Both segment
durations are arbitrary. The full real unbounded
pulse operator is separately proved self-adjoint on
that domain for every `ε∈ℝ`. These are **conditional
evolution estimates**; no actual general complex
unitary propagator has yet been constructed.

**One exact complex-phase dark trajectory (§4.89).**
Writing the complex wavefunction as a pair of real
Hilbert vectors, Lean verifies the full-domain
solution

```math
\psi_D(\tau)=e^{-iE_*\tau}D,
\qquad
\frac{d}{d\tau}\operatorname{Re}\psi_D
 =(K_*+\varepsilon W)\operatorname{Im}\psi_D,
\qquad
\frac{d}{d\tau}\operatorname{Im}\psi_D
 =-(K_*+\varepsilon W)\operatorname{Re}\psi_D.
```

It has complex squared norm one and **zero leakage**
at every time, for any real selected-edge strength.
This is **one explicit Schrödinger solution**,
not a full complex unitary group, and contains no
bright-mode rotation.

**Open obligations.** Construct the complexified
self-adjoint Hamiltonian and its strongly continuous
unitary Schrödinger group, prove domain invariance
and generator commutation, integrate the now-exact bright-mode
response against a justified dynamic leakage estimate, and then determine
which `αA+βB` targets are reachable using the
same edge and the existing `t` detuning.
The static dark eigenstate indicates an edge-only
reachability obstruction, but the general
time-dependent quantum no-go theorem and a complete
two-control preparation protocol are **not yet
Lean-certified**. The original relative-product and
finite-patch objectives (§§6.5–6.6) remain separate
and open.
**Historical scientific checkpoint.** The §§4.80–4.89 results were
verified before the bright generator identities in §§4.91–4.92.
The original Palomar registration remains unchanged. This section
is retained as a summary of those earlier results.

### 4.91. Verified bright-amplitude generator identity with explicit leakage forcing

**Verification.** The original fourteen theorems in
[`AmmannBeenkerBrightAmplitude.lean`](SpectralGeometry/AmmannBeenkerBrightAmplitude.lean)
are Lean-verified. The source also includes the combined candidate theorem
described in §4.92.

For the same selected lattice edge, write
`H_ε=K_*+εW`, let `P` be the exact orthogonal projection onto
the normalized compact-mode plane, and let `Q=I-P`.
For every **real** state `x` in the full natural onsite domain,
the proved Lean theorem gives the **exact** bright matrix element:

```math
\langle F,H_\varepsilon x\rangle
=\left(E_*+\frac{\varepsilon}{4}\right)\langle F,x\rangle
 +\varepsilon\langle F,WQx\rangle.
```

The term `ε⟨F,WQx⟩` is the *feedback from the entire orthogonal
complement*. In particular, this is **not** the eigenvalue equation
`H_ε F=(E_*+ε/4)F`; that assertion would be false for nonzero ε
because the edge excites external modes. The module's certified
quantitative bound, using the previously certified exact edge norm, is

```math
\left|\langle F,H_\varepsilon x\rangle
-\left(E_*+\frac{\varepsilon}{4}\right)\langle F,x\rangle\right|
\le 2|\varepsilon|\,\|Qx\|.
```

The corresponding dark identity is simpler and exact:

```math
\langle D,H_\varepsilon x\rangle
=E_*\langle D,x\rangle.
```

**Dynamical interpretation and limits.** Once a general complex
Schrödinger evolution on the common domain is constructed, these
matrix elements yield equations for the bright and dark amplitudes.
The forcing term can then be integrated against a proven leakage
bound to estimate phase error. This section **does not yet** construct
a propagator, integrate the amplitude equations, assert adiabatic
following, prove final return to the compact plane, or transfer
constant-pulse bounds to a smooth ramp. At ε=0 the original
twofold dark/bright degeneracy is preserved; no nondegenerate
adiabatic theorem is being invoked.

The fourteen generator-level declarations are Lean-verified.
Their combined conjunction was prepared as a separate, unsubmitted Palomar
candidate for independent statement comparison (§4.92). The prior
registered theorem remains unchanged.

### 4.92. Earlier, unsubmitted Palomar candidate: exact dark protection and bright feedback

**Earlier unsubmitted candidate, not the later L5 registration; preserved for historical reference.** The declaration
`SpectralGeometry.AmmannBeenker.crossingOneEdgeDarkBrightResponse`
in [AmmannBeenkerBrightAmplitude.lean](SpectralGeometry/AmmannBeenkerBrightAmplitude.lean)
combines previously established conclusions into **one** mathematical
statement on the full real infinite graph. Let
`H_ε=K_*+εW` on `D(V)`, `D=(a+b)/4`, `F=(a-b)/4`,
and `Qx=x-Px` for the orthogonal projection onto `span{a,b}`.
It states, for all `ε∈ℝ` and `x∈D(V)`,

```math
H_\varepsilon D=E_*D,\qquad
\langle F,H_\varepsilon x\rangle
=\left(E_*+\frac{\varepsilon}{4}\right)\langle F,x\rangle
 +\varepsilon\langle F,WQx\rangle,
```

```math
\left|\langle F,H_\varepsilon x\rangle
-\left(E_*+\frac{\varepsilon}{4}\right)\langle F,x\rangle\right|
\le 2|\varepsilon|\,\|Qx\|.
```

The first clause is a **full-operator eigenstate**, not merely a
two-dimensional compression. The second exposes the **nonzero possible
coupling to the infinite exterior**. The third controls the error in
the projected bright generator, without pretending that the bright
vector itself is a perturbed eigenvector. These clauses do not
assert an actual complex time evolution, a dynamic leakage bound
without hypotheses, or a perturbative splitting formula.

**Potential contribution.** The compact ring patterns and rank-one
edge techniques are not claimed as new by themselves. The candidate
offers an exact, quantitative protected-versus-coupled description
for one **explicitly defined, infinite, confined** Ammann–Beenker
operator with a genuine inter-ring edge. Its value is the full-space
scope and the rigorous separation of an invariant dark direction
from unavoidable bright-to-exterior feedback, rather than a claim
that a finite effective qubit model is exactly closed.

**Possible scientific readership.** These earlier exact
protected-versus-coupled identities may be relevant to mathematicians
studying finite-rank perturbations and localized states on infinite
graphs, and to theorists studying dark and bright modes in quasiperiodic
or coupled-resonator systems. They provide algebraic context for the
later genuine spectral-splitting result (§4.97), rather than a separate
claim of controlled dynamics. Relevant antecedents are Oktel,
[Phys. Rev. B 104, 014204 (2021)](https://doi.org/10.1103/PhysRevB.104.014204),
and Röntgen–Morfonios–Schmelcher,
[Phys. Rev. B 97, 035161 (2018)](https://doi.org/10.1103/PhysRevB.97.035161).
These are literature references, not endorsements or evidence of novelty;
see also [scientific audience and possible relevance](#scientific-audience-and-possible-relevance).

**Archived independent Challenge.** The historical
[`Challenge.lean`](palomar/dark-bright/Challenge.lean) states this earlier scientific theorem
without importing SpectralGeometry proofs. Six additional selected
propositions are **technical model witnesses** needed to define the
origin, graph matchings, compact-domain vectors and edge endpoints.
All model definitions must be compared transitively, with
`definition_names=[]`; these witnesses are not six more proposed
discoveries. The Challenge is kept below 300 lines if possible, but
that earlier independently explicit model required 531 physical
lines, well below Palomar's hard 1,000-line/100-KiB limit.
Its [historical per-theorem Comparator](palomar/dark-bright/comparator.json)
and root-file snapshots are preserved unchanged. The stronger final spectral theorem was registered separately in §4.98.
The active Comparator now selects the exact preparation theorem (§4.105);
all three registrations and the earlier unsubmitted candidate remain historically intact.

### 4.93. Verified dark simplicity and a distinct perturbed spectral level

This is a **subsequent, Lean-verified spectral result**, separate from the
generator-level Palomar candidate of §4.92 and from the immutable first
Palomar registration (§4.78). It concerns the **true infinite graph
operator on its original natural domain**, not a finite-patch truncation
or an energy expectation in the two-mode plane.

Write `H₀ = onsitePlusBounded potential (ringInteraction crossingParameter)`,
`Hε = onsitePlusBounded potential (ringInteraction crossingParameter + ε • crossingEdge)`,
`E_* = crossingEnergy`, and `D = (a+b)/4`, `F = (a-b)/4`.
The selected edge `W = crossingEdge` has `‖W‖ = 2`.
The following **distinct** milestones have passed the full Lean build:

- **L1 — exact dark simplicity.** The two theorems
  `crossingEdge_zero_of_perturbed_crossing_eigen` and
  `crossingPerturbedEnergy_dark_only` in
  [AmmannBeenkerNearCrossingEigenvectors.lean](SpectralGeometry/AmmannBeenkerNearCrossingEigenvectors.lean)
  show that for every real `ε ≠ 0`, every natural-domain eigenvector
  of `Hε` at `E_*` is a scalar multiple of `D`. Together with the
  exact, normalized dark eigenvector for all `ε`, the eigenspace is
  **exactly one-dimensional**, as verified in Lean.
- **L2a — ordered spectral stability and exterior force.** The theorem
  `crossingEdge_exists_ordered_eigenbases_and_stability` constructs
  complete, monotone natural-domain eigenbases for `H₀` and `Hε`
  and supplies `∀ n, |μ n - λ n| ≤ 2|ε|`. The theorem
  `crossingBright_external_edge_norm_sq` proves the **exact**
  infinite-space coupling `‖QWF‖² = 7/16`. Both are in
  [AmmannBeenkerBrightSpectralSplitting.lean](SpectralGeometry/AmmannBeenkerBrightSpectralSplitting.lean)
  and are Lean-verified.
- **L2b — multiplicity-faithful consecutive spectral slots.**
  `crossing_exists_ordered_eigenbasis_exact_double` constructs an
  ordered complete eigenbasis in which `levelMultiplicity` at `E_*`
  is precisely two.
  `ordered_levelMultiplicity_two_consecutive` in
  [OrderedLevelMultiplicityTwo.lean](SpectralGeometry/OrderedLevelMultiplicityTwo.lean)
  and `crossing_exists_ordered_eigenbasis_consecutive_pair` then
  certify indices `n, n+1` with
  `λ_n = λ_(n+1) = E_*`, and no other crossing occurrence.
  Both passed full Lean and independent Comparator checks.
- **L2c — existence of a *genuinely distinct* perturbed level.**
  `crossing_exists_distinct_perturbed_level_near` in the bright
  splitting module proves, **for every real ε ≠ 0**, the proposition
  `∃ E_b ∈ ℝ, ∃ x ∈ D(V)`, with `x ≠ 0`, such that

  ```math
  H_\varepsilon x=E_b x,\qquad
  E_b\ne E_*,\qquad
  |E_b-E_*|\le 2|\varepsilon|.
  ```

  It identifies the ordered counting basis with the stability basis
  through `DomainEigenbasis.ordered_levels_unique`, then combines
  dark-only eigenspace rigidity with orthonormality: **both** perturbed
  crossing slots cannot still equal `E_*`.
  This is a genuine full-operator eigenpair, not the compressed
  bright expectation `E_*+ε/4`. The source and independent Comparator
  passed verification.

**What remained after L2c.** The L2c theorem did **not**
identify the moving eigenvector quantitatively with the original
bright direction, assert its simplicity, or exhaust the perturbed
crossing window. These latter two issues are addressed separately
in §4.94; they were **not** part of the L2c proof. For
`0 < |ε| ≤ 1/1024`, the
target second-order law was (at that stage)

```math
\bigl|E_b(\varepsilon)-(E_*+\varepsilon/4)\bigr|
\le 112\,\varepsilon^2,
```

together with the proposed exterior-component control
`‖Qx‖ ≤ 256|ε| |c| ‖QWF‖` for `x=cF+Qx` orthogonal to `D`.
These were **future L3–L5 obligations at the L2c stage**, not
consequences of L2c itself. The exterior bound was subsequently
proved in §4.95 and the quadratic energy law in §4.96.
No new Palomar candidature or registration has been
created from this intermediate milestone.

### 4.94. Two simple eigenvalues in a certified perturbed window

This **L2d** milestone strengthens the genuine L2c eigenpair existence
without replacing any older result. It applies to the full confined
infinite Ammann–Beenker graph and the **actual natural-domain**
Hamiltonian `Hε` of §4.93, for

```math
0<|\varepsilon|\le\frac1{1024}.
```

The theorem
`SpectralGeometry.AmmannBeenker.crossing_perturbed_isolated_pair_simple`
in
[AmmannBeenkerBrightSpectralSplitting.lean](SpectralGeometry/AmmannBeenkerBrightSpectralSplitting.lean)
exhibits a nonzero natural-domain eigenvector `x_b` and energy
`E_b≠E_*` with `Hε x_b=E_b x_b` and

```math
|E_b-E_*|\le2|\varepsilon|.
```

Moreover every **nonzero natural-domain eigenvector** `y` of `Hε`
at any energy `t` satisfying `|t-E_*|≤1/256` has either
`t=E_*` or `t=E_b`. Every eigenvector at the moving
energy is a scalar multiple of `x_b`, so its geometric
eigenspace is **one-dimensional**. Independently, the already
proved dark-only result (L1) identifies the entire eigenspace at
`E_*` with the **one-dimensional** dark line.

**Why the proof is not a two-level approximation.** The complete,
multiplicity-faithful Hilbert eigenbases for both true unbounded
operators have indexwise stability `|μ_n−λ_n|≤2|ε|`. In the
unperturbed sequence, only the two consecutive crossing indices
have value `E_*`. Every other baseline eigenvector must lie
**strictly beyond the certified gap** `1/128` by the existing
no-other-eigenvector theorem. The norm bound `2|ε|` then keeps
all other perturbed ordered positions outside `1/256`.
A general Hilbert-basis argument shows that every genuine
nonzero eigenvector's energy occurs among those ordered positions.
L1 supplies the dark position and L2c the distinct moving position;
these exhaust the two slots. A unique spectral index also yields the
exact one-dimensional eigenvector representation. The support lemmas
`DomainEigenbasis.eigenvalue_occurs` and
`DomainEigenbasis.eigenvector_eq_smul_of_unique_level`
make these completeness and simplicity inferences explicit in Lean.

**Scope of the result.** This is an exhaustive description of
**natural-domain real eigenvalues in the specified window**. It is
not, by itself, a new statement about an independently defined
resolvent or complex spectrum; it also does not establish the sign
of the shift, the target `112ε²` remainder, or quantitative
external eigenvector leakage. These are limitations of L2d **alone**:
the external eigenvector estimate was subsequently proved in §4.95
and the energy remainder in §4.96. The signed-shift corollary and
final consolidated statement are established separately in §4.97.

**Verification.** The L2d theorem and its generic Hilbert-basis
support passed full Lean and independent Comparator checks.

### 4.95. Bright amplitude and quantitative exterior leakage

The L3 results concern the **actual moving natural-domain eigenvector**
of the unbounded infinite Ammann–Beenker operator, rather than a
two-mode compression. Let `D=(a+b)/4` and `F=(a-b)/4`
be the normalized dark and bright vectors, `Q` the exact
orthogonal projection onto the complement of their span,
and `v=QWF` the selected edge's external bright force.
The already certified identity is `‖v‖²=7/16`.

For `0<|ε|≤1/1024`, take the unique simple moving
real eigenvalue `E_b≠E_*` from §4.94 and a nonzero
natural-domain eigenvector `x` satisfying
`Hε x=E_b x`. Theorems
`crossing_moving_eigenvector_dark_orthogonal`,
`crossingQubitPart_eq_bright_smul_of_dark_orthogonal`
and `crossing_moving_eigenvector_bright_nonzero`
prove the *exact* decomposition

```math
\langle D,x\rangle=0,\qquad
x=cF+q,\qquad c=\langle F,x\rangle\ne0,\quad q=Qx.
```

The sharper L3 theorem
`crossing_moving_eigenvector_sharp_leakage`
establishes the **full infinite-operator leakage estimate**

```math
\boxed{\|q\|\le256\,|\varepsilon|\,|c|\,\|v\|}.
```

The existential corollary
`crossing_exists_moving_bright_sharp_leakage`
packages this bound with a genuine eigenpair and
`|E_b-E_*|≤2|ε|`. The preceding theorem
`crossing_exists_moving_eigenvector_bright_and_leakage`
also certifies `‖Qx‖≤512|ε|‖x‖`.

**Proof mechanism.** Symmetry forces the baseline
residual `Rx=(H₀-E_*)x` into the original
crossing-plane orthogonal complement. The exact
projected eigen-equation is

```math
Rx=(E_b-E_*)q-\varepsilon(cv+QWq).
```

The proved gap inequality `(1/128)‖q‖≤‖Rx‖`,
nonexpansiveness of `Q`, and `‖W‖=2` imply

```math
(1/128-|E_b-E_*|-2|\varepsilon|)\|q\|
\le|\varepsilon|\,|c|\,\|v\|.
```

The left coefficient is at least `1/256`
because `|E_b-E_*|≤2|ε|` and
`|ε|≤1/1024`. No assumed spectral projector,
finite patch or two-state truncation is used.

**Scope and subsequent progress.** L3 itself controls the
eigenvector rather than the energy shift. The true quadratic
spectral bound is established separately in §4.96; the formal signed-shift
corollary and consolidated theorem are established in §4.97.
Quantum state preparation is a separate downstream problem.

**Verification.** The preliminary and sharp L3 estimates and existential
corollary passed full Lean and independent Comparator checks.

### 4.96. A sharp quadratic law for the actual moving level

**L4 — true spectral-level estimate, not a Rayleigh quotient.**
The new source declarations in
[AmmannBeenkerBrightSpectralSplitting.lean](SpectralGeometry/AmmannBeenkerBrightSpectralSplitting.lean)
connect the **genuine** moving natural-domain eigenvector of
§§4.94–4.95 with its eigenvalue. For every real perturbation satisfying

```math
0<|\varepsilon|\le\frac1{1024},
```

the theorem `crossing_exists_moving_level_quadratic_bound`
exhibits a nonzero full-operator eigenvector `x` at a
distinct moving real energy `E_b`, with
`|E_b-E_*|≤2|ε|` and the exact quantitative estimate

```math
\boxed{\left|E_b-\left(E_*+\frac{\varepsilon}{4}\right)\right|
\le112\,\varepsilon^2}.
```

The level is the **unique simple non-dark energy** in the
closed radius-`1/256` point-spectrum window, by the
independently proved L2d theorem; L4 uses that actual
eigenpair rather than asserting a new eigenpair
solely from an expectation value.

**Exact mechanism.** With the normalized crossing
bright state `F`, set
`c=⟨F,x⟩≠0`, `q=Qx`,
`v=QWF`, where `Q` is the original crossing-plane
orthogonal projection. The exact generator identity
`crossingBright_pulse_amplitude`, together with
`crossingBright_edge_leakage_inner`, gives the true
eigenvalue equation projected against bright:

```math
\left(E_b-E_*-\frac{\varepsilon}{4}\right)c
=\varepsilon\langle v,q\rangle.
```

The real Hilbert-space Cauchy–Schwarz lemma
`crossing_abs_inner_le_norm_mul` and the verified
sharp L3 external estimate give

```math
\begin{aligned}
\left|E_b-E_*-\frac{\varepsilon}{4}\right||c|
&\le|\varepsilon|\,\|v\|\,\|q\|\\
&\le256\,\varepsilon^2\,|c|\,\|v\|^2\\
&=112\,\varepsilon^2\,|c|,
\end{aligned}
```

because the squared full-graph force is exactly
`‖v‖²=7/16`. The previously established
`c≠0` justifies cancelling the coefficient.
The result is thus a theorem about the actual
**infinite natural-domain eigenvalue**, not a
two-level compression or finite-patch approximation.

The reusable parametric theorem
`crossing_moving_energy_quadratic_bound` requires only a genuine
near-crossing eigenvector, its nonzero bright coefficient
and the stated smallness hypothesis;
`crossing_exists_moving_level_quadratic_bound`
attaches it to the verified moving level.

**Scope and subsequent progress.** L4 alone establishes the
quadratic energy law, not a signed-shift corollary or one
consolidated final theorem. Those later conclusions are separately
proved in §4.97, without changing the historical L4 proof.
General complex time evolution and preparation of arbitrary
two-mode states remain outside this static spectral result.

**Verification.** Full Lean/Mathlib and independent Comparator checks passed.

### 4.97. Signed shift and consolidated infinite-operator splitting

**L5 — the consolidated real point-spectrum theorem for the
selected-edge perturbation.** The full Lean source
[AmmannBeenkerBrightSpectralSplitting.lean](SpectralGeometry/AmmannBeenkerBrightSpectralSplitting.lean)
now includes `crossing_moving_energy_shift_sign` and
`crossing_final_signed_bright_spectral_splitting`. They
combine the existing L1–L4 results without assuming a
new two-level approximation or perturbative projector.

Let `Hε=H₀+εW` denote the genuine **infinite**
Hamiltonian on its natural onsite domain, with original
crossing energy `E_*`, normalized dark mode `D`,
normalized bright mode `F` and orthogonal projection `Q`
onto the complement of their original two-dimensional plane.
For every real `ε` with `0<|ε|≤1/1024`, the new theorem
constructs a real energy `E_b` and a nonzero
natural-domain eigenvector `x` satisfying

```math
H_\varepsilon x=E_bx,\quad E_b\ne E_*,
\quad |E_b-E_*|\le2|\varepsilon|.
```

It verifies the **actual moving energy's quadratic law**

```math
\boxed{\left|E_b-\left(E_*+\frac{\varepsilon}{4}\right)\right|
\le112\,\varepsilon^2}
```

and its **strict signed displacement**

```math
\varepsilon>0\Longrightarrow E_b>E_*,
\qquad
\varepsilon<0\Longrightarrow E_b<E_*.
```

The sign follows numerically from the proven L4 error:

```math
112\varepsilon^2\le\frac7{64}|\varepsilon|
<\frac14|\varepsilon|
\quad(\varepsilon\ne0).
```

The consolidated theorem additionally states that
**every nonzero natural-domain eigenvector** with real
eigenvalue in the closed radius-`1/256` window has energy
either `E_*` or `E_b`. Both geometric eigenspaces
are simple: the dark eigenspace is exactly the line
`ℝD` and the moving eigenspace exactly the line `ℝx`.

Writing `c=⟨F,x⟩≠0`, the moving eigenvector is
orthogonal to dark and has the exact full-space
decomposition and quantitative leakage bound

```math
x=cF+Qx,\qquad
\boxed{\|Qx\|\le256|\varepsilon|\,|c|\,\|QWF\|},
\qquad \|QWF\|^2=\frac7{16}.
```

The proof assembles genuine natural-domain eigenpairs,
the ordered gap/exhaustion arguments, exact dark
rigidity, nonzero bright amplitude, the sharp
full-exterior L3 bound, and L4's true eigenvalue
estimate, all in one statement with common parameter
hypotheses. It does **not** claim a separate
classification of complex spectrum, construction of
the general quantum propagator, target-state preparation,
or the remaining analytic-product certificates.

**Verification.** Both the complete Lean 4/Mathlib build and the
independent Comparator passed.

<a id="498-palomar-candidate-signed-bright-splitting"></a>

### 4.98. Palomar registration: signed bright splitting

**Second Palomar registration, with preparation and editorial history.** The
package selects the fully proved L5 statement
`SpectralGeometry.AmmannBeenker.crossing_final_signed_bright_spectral_splitting`
from [AmmannBeenkerBrightSpectralSplitting.lean](SpectralGeometry/AmmannBeenkerBrightSpectralSplitting.lean).
Unlike the earlier generator-response candidate (§4.92), this
theorem concerns a **genuine moving eigenvalue of the full infinite
operator**, not just a matrix element calculated on the original
two-dimensional plane.

**Plain-language theorem.** If we slightly change one edge
in the specified infinite octagonal network, one simple
nearby energy level stays fixed and a second simple level
moves up when the edge is strengthened or down when it is
weakened. There are no other real eigenvector energies in
the stated narrow window. The moving energy is within a
proved quadratic error of a first-order prediction, and
the theorem bounds the part of its wave pattern outside
the original two localized states. The result concerns the
entire infinite network and its natural domain; it is
not a time-evolution or experimental-control result.

**Independent registered package.** The L5 [Challenge](palomar/signed-bright-splitting/Challenge.lean) imports only Mathlib and reconstructs the necessary concrete model without source proofs. Its seven selected propositions consist of six technical model witnesses and one scientific conclusion. All definitions are concrete. Its [Solution](palomar/signed-bright-splitting/Solution.lean) imports the verified proof module and never Challenge. Its [Comparator](palomar/signed-bright-splitting/comparator.json) and [formalization metadata](palomar/signed-bright-splitting/formalization.yaml) are preserved with those root-file snapshots. The earlier unsubmitted [generator-response package](palomar/dark-bright/) is also preserved. The active root files now describe the distinct third registered result (§4.105). Each Comparator remains in its own directory; there is no root Comparator.

**Verification and registration.** The L5 mathematical source and
independently assembled package passed full Lean and independent kernel
comparison (NanoDa and con-ron). The automated editorial review requested
that the selected theorem explicitly assert the **nonzero dark eigenvector**
and its fixed-energy eigenvalue equation. The corrected scientific theorem
and Mathlib-only Challenge include both `crossingDark ≠ 0` and the full
natural-domain equation `Hε domainCrossingDark = E_* • crossingDark`.
The revised package passed verification and was registered separately as
[PALOMAR-2026-11-23-000017 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-23-000017&version=1)
on 23 November 2026. The original registration
`PALOMAR-2026-11-06-000012` remains unchanged.
Originality and significance still require independent assessment.

### 4.99. Coordinated eight-edge matching and exact dark cancellation

[`AmmannBeenkerCoordinatedRingControl.lean`](SpectralGeometry/AmmannBeenkerCoordinatedRingControl.lean)
starts L7a on the complete infinite real Ammann–Beenker Hilbert space.
It retains the existing graph, compact modes and single-edge results;
the coordinated perturbation is a different finite local intervention.

**Geometry and bounded correction.** For each `i : Fin 8`, pair the actual
vertices `firstRingVertex i` and `secondRingVertex i`. The pairs are
genuine adjacent edges, distinct, and have no shared endpoints. Write
`u_i` for their infinite edge vector (the difference of the two unit site
vectors), and define the bounded real continuous linear operators

```math
M=\sum_{i=0}^{7} W_i,\qquad W_i x=\langle u_i,x\rangle u_i.
```

Each term uses the same unit-increment Laplacian convention as
`crossingEdge`. The eight-edge sum is symmetric on the entire Hilbert
space. Its range is contained in the span of the eight edge vectors by
the displayed definition; the new module does not separately certify
a rank or operator-norm formula.

**Exact dark cancellation.** The matched amplitudes obey

```math
a(A_i)=b(B_i),\qquad a(B_i)=b(A_i)=0.
```

Thus for the normalized dark state `D=(a+b)/4`, every edge has zero
endpoint difference, so `W_i D=0` and `M D=0`. These equations hold on
the full infinite Hilbert space, not just after compression onto the
two-mode plane.

**New definitions:** `coordinatedRingPair`, `coordinatedRingEdge`,
`coordinatedRingControl`.

| Lean theorem | Verified content |
| --- | --- |
| `coordinatedRingPair_adjacent` | Every matched pair is adjacent in the actual graph |
| `coordinatedRingPair_injective` | The eight indexed pairs are distinct |
| `coordinatedRing_disjoint` | First- and second-ring vertices never coincide |
| `coordinatedRing_matching` | Distinct pairs have no common endpoint |
| `coordinatedRingEdge_apply` | Exact full-space action of each rank-one correction |
| `coordinatedRingControl_apply` | Exact full-space sum action |
| `coordinatedRing_amplitudes` | Equal corresponding amplitudes and zero cross-ring values |
| `coordinatedRingEdge_dark_zero` | Each individual edge annihilates dark |
| `coordinatedRingControl_dark_zero` | The coordinated sum annihilates dark |
| `coordinatedRingEdge_symmetric` | Each term is symmetric on the full real space |
| `coordinatedRingControl_symmetric` | The sum is symmetric on the full real space |

**Verification and subsequent result.** All eleven theorems and three
definitions are Lean-verified. Dark cancellation alone does not prove
invariance of the two-mode plane; the subsequent §4.100 establishes
that stronger result. The single-edge approximate-control route remains
a distinct research direction. Neither new module was selected in the historical L5 Comparator.
The third registered package includes the local-edge certificates from this module.

<a id="4100-proposed-invariant-plane-and-pauli-algebra-proofs-ci-pending"></a>

### 4.100. Exact invariant-plane control and Pauli generator algebra

**Plain-English result.** A change to one connecting edge generally
pushes part of the bright wave into the rest of the infinite network.
Changing all eight matched edges by the same amount is different:
the contributions combine exactly to preserve the two original
localized patterns as a space. The dark wave is unchanged by this
coordinated correction, while the bright wave receives twice the
edge-strength change in energy. No exterior component is produced by
the operator acting on any mixture of the two patterns. Combining this
correction with first-ring detuning still preserves that same space.
The statement holds for arbitrary real control strengths, not merely
small perturbations, and uses the full infinite operator.

**L7a — exact full-space invariance.** The module
[`AmmannBeenkerCoordinatedInvariantPlane.lean`](SpectralGeometry/AmmannBeenkerCoordinatedInvariantPlane.lean)
proves the following identities for the already defined unnormalized
compact modes `a,b`, normalized modes `D=(a+b)/4`, `F=(a-b)/4`,
and orthogonal components `P,Q=I-P`:

```math
Ma=a-b,\qquad Mb=b-a,\qquad MD=0,\qquad MF=2F,\qquad QMP=0.
```

The proof evaluates the sum of local edge corrections at every vertex.
On either ring exactly one matched edge contributes; away from both
rings all eight contributions and both compact modes vanish. This
proves an identity in the infinite Hilbert space, not merely in a
finite central block or a projected matrix.

For real detuning `δ`, coordinated strength `η` and real coefficients
`r,s`, the natural-domain Hamiltonian
`H(δ,η)=onsitePlusBounded potential (ringInteraction (crossingParameter+δ)+η M)`
acts exactly as

```math
H(\delta,\eta)(ra+sb)
=\big[(E_*+\delta+\eta)r-\eta s\big]a
+\big[(E_*+\eta)s-\eta r\big]b.
```

The left-hand side uses the natural-domain lifts of the compact modes.
The output belongs to the same compact plane and to the natural domain.
Its orthogonal exterior component is zero.

**L7b — exact effective matrix.** In the ordered normalized basis
`(D,F)`, the full-operator action therefore has the exact matrix

```math
H_{\mathrm{eff}}=\begin{pmatrix}
E_*+\delta/2&\delta/2\\
\delta/2&E_*+\delta/2+2\eta
\end{pmatrix}
=(E_*+\delta/2+\eta)I+(\delta/2)\sigma_x-\eta\sigma_z.
```

The scalar multiple of the identity affects only a common phase in
the corresponding Schrödinger model. The detuning and coordinated-edge
controls act along two different Pauli directions, so their order
matters. The module
[`AmmannBeenkerCoordinatedLieAlgebra.lean`](SpectralGeometry/AmmannBeenkerCoordinatedLieAlgebra.lean)
defines the complex matrices `X=iσ_x`, `Y=iσ_y`, `Z=iσ_z`
and proves, with `[A,B]=AB-BA`,

```math
[X,Z]=2Y,\qquad [Z,Y]=2X,\qquad [Y,X]=2Z.
```

It also proves noncommutation and the explicit real-coordinate
parametrization of the three generator directions. These are the
algebraic ingredients of the standard two-state rotation algebra.
The subsequent §4.101 establishes equality of the generated Lie algebra
with all of `su(2)` and constructive reachability by a three-rotation
matrix product. Its realization by actual infinite-system pulses remains open.

| Lean theorem | Meaning |
| --- | --- |
| `coordinatedRingControl_compactA`, `coordinatedRingControl_compactB` | Exact action on both compact modes |
| `coordinatedRingControl_bright`, `coordinatedRingControl_pair` | Bright response and arbitrary real compact combination |
| `coordinatedRingControl_offplane_zero` | Zero exterior component of the coordinated correction on the plane |
| `coordinatedControls_compact_action` | Exact full natural-domain action of both controls |
| `coordinatedControls_offplane_zero`, `coordinatedControls_domain_invariant` | Plane and domain invariance |
| `coordinatedControls_dark_bright_action` | Exact action in normalized dark/bright coordinates |
| `coordinatedEffectiveMatrix_pauli` | Pauli decomposition of the real matrix |
| `coordinatedLie_XZ`, `coordinatedLie_ZY`, `coordinatedLie_YX` | Three complex commutator identities |
| `coordinatedLie_noncommuting` | The two control directions do not commute |
| `coordinatedLie_coordinates` | Explicit real-coordinate parametrization |

**Status and limits.** All fifteen public theorems, five private
coordinate-evaluation lemmas and four new definitions are Lean-verified.
L7a is complete; this section supplies the matrix and generator-algebra
foundation of L7b, completed at the algebraic level in §4.101.
The subsequent §4.102 establishes exact single-axis Schrödinger trajectories
with zero leakage at every time. Section 4.103 identifies their rotation
matrices including the common phase; §4.104 proves their continuous
three-pulse composition with exact zero leakage throughout. Section 4.105
proves arbitrary normalized target preparation from dark up to global phase.
The registered L7 package selects the final preparation theorem and supporting locality certificates (§4.105).
The original single-edge L1–L6 route and Track A remain distinct.


### 4.101. Full Lie generation and constructive two-state rotations

**Plain-English result.** The two available controls are enough to
generate every infinitesimal rotation of a two-state quantum system,
after a common energy shift is removed. Moreover, one can explicitly
choose three rotation angles that transform the dark coordinate into
any normalized pair of complex amplitudes. This is a theorem about
exact matrices, not yet a construction of the time evolution of the
infinite Ammann–Beenker graph.

**Full Lie generation.** In
[§4.100](#4100-exact-invariant-plane-control-and-pauli-generator-algebra)
the two independent traceless generator directions were identified
as X = iσ_x and Z = iσ_z, with [X,Z] = 2Y and Y = iσ_y.
The new module
[`AmmannBeenkerCoordinatedLieGeneration.lean`](SpectralGeometry/AmmannBeenkerCoordinatedLieGeneration.lean)
defines the real vector space

```math
\mathfrak{su}(2)=\{A\in M_2(\mathbb C): A^\dagger=-A,\ 
\operatorname{tr}A=0\}.
```

It proves that this space is closed under matrix commutators, contains
X and Z, and that each of its elements is a real linear combination
of X, Y and Z. Specifically,

```math
A=\operatorname{Im}(A_{01})X+\operatorname{Re}(A_{01})Y+
\operatorname{Im}(A_{00})Z.
```

Any real linear subspace closed under commutators and containing X
and Z must also contain Y, since Y = [X,Z]/2. Consequently it must
contain every element of su(2). Together with closure of su(2) itself,
this proves that it is exactly the smallest such subspace. This is
a concrete, two-sided Lie-generation theorem rather than just a
calculation of three commutators.

**Constructive Euler state reachability.** In
[`AmmannBeenkerCoordinatedEuler.lean`](SpectralGeometry/AmmannBeenkerCoordinatedEuler.lean)
the two matrix rotations are defined by

```math
R_x(t)=\begin{pmatrix}\cos t&i\sin t\\i\sin t&\cos t\end{pmatrix},
\qquad
R_z(t)=\begin{pmatrix}e^{it}&0\\0&e^{-it}\end{pmatrix}.
```

The parameters here are half-angles in the Bloch-sphere convention.
For any real p, t, q the first column of the product is exactly

```math
R_z(q)R_x(t)R_z(p)\binom{1}{0}
=\binom{\cos t\,e^{i(p+q)}}{i\sin t\,e^{i(p-q)}}.
```

Given arbitrary complex amplitudes α and β with
|α|² + |β|² = 1, the proof constructs

```math
u=\arg(\alpha),\quad v=\arg(-i\beta),\quad
t=\arccos|\alpha|,\quad p=(u+v)/2,\quad q=(u-v)/2.
```

Then 0 ≤ t ≤ π/2 and the displayed product is exactly (α,β),
including the cases in which one amplitude is zero. The theorem
states existence of the three real angles; the proof gives these
explicit witnesses. It reaches the exact complex pair in the
rotation-matrix model, not merely its magnitudes.

In the full-operator restriction the scalar energy
E_* + δ/2 + η contributes a common phase. After removing it, the
Schrödinger generator has the two independently selectable
coefficients

```math
G(\delta,\eta)=-\frac{\delta}{2}X+\eta Z.
```

Lean proves G(-2t,0)=tX and G(0,t)=tZ for every real t.
Thus a unit-duration segment with signed detuning -2t or signed
coordinated edge strength t has the required algebraic generator
coefficient. This identifies the settings for the idealized
three-segment protocol, assuming independently tunable arbitrary
real control strengths. No nonnegativity restriction on the physical
edge weights or bounded-strength hardware constraint is imposed by
this theorem. The equality between these rotations and the actual single-axis
natural-domain trajectories, including the common phase, is proved in
§4.103. The continuous switched protocol is proved in §4.104;
its arbitrary-target endpoint theorem is proved in §4.105. A general
complex full-space propagator remains separate.

| Lean theorem | Meaning |
| --- | --- |
| `coordinatedSu2_commutator` | Closure under matrix commutators |
| `coordinatedSu2_X`, `coordinatedSu2_Z` | Both control directions belong to su(2) |
| `coordinatedSu2_coordinates` | Every traceless skew-Hermitian matrix has three real Pauli coordinates |
| `coordinatedSu2_le_of_controls` | Every commutator-closed real subspace containing X and Z contains su(2) |
| `coordinatedSu2_generated_iff` | Exact generated-algebra characterization in both directions |
| `coordinatedPhase_add`, `coordinatedPhase_norm` | Phase multiplication and unit modulus |
| `coordinatedEuler_dark_column` | Explicit dark-state column of the Z–X–Z product |
| `coordinatedEuler_reaches_from_dark` | Every normalized complex pair is reached by the rotation product |
| `coordinatedReducedGenerator_X`, `coordinatedReducedGenerator_Z` | Independent signed generator coefficients |

**Status and limits.** The twelve public theorems and five definitions
are Lean-verified. L7b is complete at the algebraic level. The formal
result is state reachability from the dark coordinate in a
two-by-two matrix model; it does not assert a full SU(2) group
factorization theorem or arbitrary initial-state dynamics.
Section 4.102 constructs the exact single-axis full-graph Schrödinger
trajectories in real and imaginary components, with zero exterior component
throughout each segment. Section 4.103 proves the exact phase-weighted
rotation identification, and §4.104 proves continuous pulse composition
with zero leakage at every time. Section 4.105 proves the final arbitrary
target preparation theorem from dark. A general complex full-space propagator
remains open. The third registered package selects supporting locality statements and the final
preparation theorem; it does not independently select the Lie-algebra results. The original single-edge L6 goal and the
analytic spectral-geometry program remain separate.


### 4.102. Exact natural-domain Schrödinger trajectories for both control axes

**Plain-English result.** The coordinated controls preserve the two
localized waves not only when the Hamiltonian acts on them, but also
during explicit time-dependent solutions. For either control used
alone, every complex combination of the two waves evolves with
exactly conserved total squared amplitude. Neither its real part nor
its imaginary part ever develops a component outside the original
two-state space. This is a dynamical theorem for the actual infinite
graph, not a calculation on a truncated graph or an assumption about
a supplied propagator.

**General two-eigenmode construction.** The module
[`AmmannBeenkerCoordinatedPairDynamics.lean`](SpectralGeometry/AmmannBeenkerCoordinatedPairDynamics.lean)
takes any two real eigenvectors x,y on the original natural onsite
domain, with respective real eigenvalues E,F for the same
onsite-plus-bounded operator H. For arbitrary complex coefficients a,b
it defines

```math
c(\tau)=a e^{-iE\tau},\qquad d(\tau)=b e^{-iF\tau},
\qquad
u(\tau)=\operatorname{Re}c(\tau)x+\operatorname{Re}d(\tau)y,\quad
v(\tau)=\operatorname{Im}c(\tau)x+\operatorname{Im}d(\tau)y.
```

The pair (u,v) represents the complex state u+iv. Both components
have explicit lifts to the natural domain for every real time. Their
initial values are the real and imaginary parts of the given
superposition. Differentiating the actual Hilbert-space vectors yields

```math
u'(\tau)=Hv(\tau),\qquad v'(\tau)=-Hu(\tau).
```

These are precisely the real and imaginary equations of
iψ'=Hψ for the componentwise complexification. The Hamiltonian
on the right is the full infinite operator applied to the
natural-domain lifts. The proof requires neither a finite-volume
approximation nor a pre-existing time-evolution map.

If x and y are orthogonal, the squared complex norm is conserved:

```math
\|u(\tau)\|^2+\|v(\tau)\|^2
=|a|^2\|x\|^2+|b|^2\|y\|^2.
```

If both eigenvectors have zero original-plane leakage, the two
components have zero leakage at every time. This follows from
linearity and is independent of the pulse strength or duration.

**Application to the two actual controls.** The module
[`AmmannBeenkerCoordinatedAxisDynamics.lean`](SpectralGeometry/AmmannBeenkerCoordinatedAxisDynamics.lean)
uses the following exact eigenpairs, without a spectral truncation.
Write a_0=compactA, b_0=compactB and D,F for the normalized dark
and bright modes.

| Control | Eigenvectors used | Exact energies |
| --- | --- | --- |
| First-ring detuning, η=0 | a_0, b_0 | E_*+δ, E_* |
| Eight coordinated edges, δ=0 | D,F | E_*, E_*+2η |

For the detuning control the compact eigenvectors are orthogonal
and each has squared norm eight; the conserved squared complex
norm is therefore 8(|a|²+|b|²) for their coefficients.
For the coordinated edge control the normalized dark and bright
vectors are orthogonal and the corresponding conserved norm
is |a|²+|b|². Both exact trajectories have zero leakage in both
components at every real time and for arbitrary real strengths.
Both bases span the original compact-mode plane.

**Self-adjointness on the full real space.** The bounded correction
is ringInteraction(crossingParameter+δ)+ηM. Lean proves symmetry
of this correction, identifies the associated unbounded real
partial linear operator with the full natural-domain Hamiltonian,
and proves self-adjointness for all real δ,η, including their
simultaneous use. This strengthens the earlier selected-edge
self-adjointness result. It does not by itself construct a complex
unitary group.

| Lean theorem | Meaning |
| --- | --- |
| `coordinatedEigenCoeff_initial`, `coordinatedEigenCoeff_norm` | Initial coefficient and exact constant modulus |
| `coordinatedEigenCoeff_re`, `coordinatedEigenCoeff_im` | Real trigonometric expressions for the phase |
| `coordinatedEigenCoeff_re_deriv`, `coordinatedEigenCoeff_im_deriv` | Exact scalar derivative identities |
| `coordinatedPair_domain_coe`, `coordinatedPair_initial` | Natural-domain lifts and initial conditions |
| `coordinatedPair_Schrodinger` | Both Hilbert-space Schrödinger derivative equations |
| `coordinatedPair_norm_sq`, `coordinatedPair_leakage_zero` | Conserved squared complex norm and exact zero leakage under the stated hypotheses |
| `coordinatedCorrection_symmetric` | Symmetry of the complete bounded correction |
| `coordinatedHamiltonianPMap_domain`, `coordinatedHamiltonianPMap_apply`, `coordinatedHamiltonianPMap_isSelfAdjoint` | Natural domain, full action and real self-adjointness |
| `coordinatedXAxis_eigenA`, `coordinatedXAxis_eigenB` | Exact compact eigenpairs under detuning |
| `coordinatedZAxis_eigenDark`, `coordinatedZAxis_eigenBright` | Exact dark/bright eigenpairs under coordinated edges |
| `coordinatedDarkBright_orthogonal`, `coordinatedBright_leakage_zero` | Orthogonality and bright confinement |
| `coordinatedXAxis_Schrodinger`, `coordinatedZAxis_Schrodinger` | Exact full-graph trajectory equations for each axis |
| `coordinatedXAxis_norm_sq`, `coordinatedZAxis_norm_sq` | Exact conserved squared complex norm on each axis |
| `coordinatedXAxis_leakage_zero`, `coordinatedZAxis_leakage_zero` | Zero exterior component of both real and imaginary parts at every time |

**Status and limits.** Twenty-seven public theorems, two private
supporting lemmas and seven definitions are Lean-verified.
L7c.1 is complete. These solutions use a real/imaginary representation
on the full graph with initial data in the compact plane. They are
not a general complex-Hilbert-space propagator for arbitrary initial
data. Section 4.103 (L7c.2) identifies the exact coefficient action
with the rotations of §4.101, including the scalar phases. Section 4.104
(L7c.3) joins the segments with matching initial and final states and
zero leakage throughout. Section 4.105 (L7c.4) proves arbitrary normalized
target preparation from dark up to global phase with zero leakage throughout. A general
complex unitary group remains a separate outstanding objective.
The final L7 preparation theorem is selected for the independently verified registered package (§4.105); the intermediate trajectory results are not separate submissions. The separate L6 and Track A goals are preserved.


### 4.103. Exact identification of physical pulses with Pauli rotations

**Plain-English result.** The rotations used to select a desired mixture
of the dark and bright waves are now proved to be the actual coefficient
evolution of the corresponding single-axis full-graph Schrödinger
trajectories. This identification retains the common complex phase,
rather than discarding it before comparing consecutive pulses. It
holds for every complex initial coefficient pair and every real
control strength and time.

The module
[`AmmannBeenkerCoordinatedRotationDynamics.lean`](SpectralGeometry/AmmannBeenkerCoordinatedRotationDynamics.lean)
defines the action of a two-by-two complex matrix on a pair of
coefficients, and the embeddings of their real and imaginary parts
into the full real graph Hilbert space:

```math
\mathcal E_{\mathrm{Re}}(a,b)=\operatorname{Re}(a)D+
\operatorname{Re}(b)F,\qquad
\mathcal E_{\mathrm{Im}}(a,b)=\operatorname{Im}(a)D+
\operatorname{Im}(b)F.
```

Here D and F are the original normalized dark and bright modes,
and E_* is their crossing energy. For the pure detuning pulse
of strength δ, write p=exp(-i(E_*+δ)τ) and q=exp(-iE_*τ).
The eigenmode phases in the original compact A/B basis give
the following exact matrix in the dark/bright basis:

```math
U_X(\delta,\tau)=
\frac12\begin{pmatrix}p+q&p-q\\p-q&p+q\end{pmatrix}
=e^{-i(E_*+\delta/2)\tau}R_X(-\delta\tau/2).
```

For the coordinated eight-edge pulse of strength η, the
dark/bright basis already consists of eigenvectors. Consequently,

```math
U_Z(\eta,\tau)=
\begin{pmatrix}e^{-iE_*\tau}&0\\0&e^{-i(E_*+2\eta)\tau}\end{pmatrix}
=e^{-i(E_*+\eta)\tau}R_Z(\eta\tau).
```

The rotation conventions are those of §4.101:
R_X(t)=cos(t)I+i sin(t)σ_x, and
R_Z(t)=diag(exp(it),exp(-it)).
The scalar phase in each identity has modulus one, and the
half-angle parameter is fixed by the corresponding energy difference.

**Connection to the infinite natural-domain trajectories.**
For input aD+bF the compact A/B coefficients are (a+b)/4 and
(a-b)/4, because D=(compactA+compactB)/4 and
F=(compactA-compactB)/4. Lean proves the coefficient conversion
and the full Hilbert-space identities for both components:
the detuning trajectory of §4.102 equals the real and imaginary
embeddings of U_X(a,b), and the coordinated-edge trajectory equals
those of U_Z(a,b). The same identities hold with the phase-weighted
rotation expressions substituted for the matrices. This connects
the matrix expressions directly to the previously proved
Schrödinger equations, natural-domain lifts, norm conservation
and zero leakage for each individual pulse. No full-space
propagator is assumed.

The two matrices equal the identity at time zero. The module
also establishes compatibility of the matrix action with
matrix multiplication, scalar multiplication of matrices and
common scaling of the input coefficients, and identifies
the first column as the action on the initial dark pair (1,0).
These facts are used in the exact composition of the three pulses in §4.104.

| Lean theorem | Meaning |
| --- | --- |
| `coordinatedApplyPair_mul` | Successive matrix actions equal the product action |
| `coordinatedApplyPair_smul`, `coordinatedApplyPair_scale_input` | Common scalar phases pass through matrix action |
| `coordinatedApplyPair_dark` | Dark input selects the first matrix column |
| `coordinatedPhase_trig` | Euler's formula for the phase convention |
| `coordinatedXAxisMatrix_rotation`, `coordinatedZAxisMatrix_rotation` | Exact phase-weighted rotation identities |
| `coordinatedXAxisMatrix_coefficients`, `coordinatedZAxisMatrix_coefficients` | Physical eigenmode coefficients in dark/bright coordinates |
| `coordinatedXAxis_trajectory_matrix`, `coordinatedZAxis_trajectory_matrix` | Equality with both full-graph trajectory components |
| `coordinatedXAxis_trajectory_rotation`, `coordinatedZAxis_trajectory_rotation` | Direct identification with phase-weighted rotations |
| `coordinatedXAxisMatrix_initial`, `coordinatedZAxisMatrix_initial` | Identity at zero time |

**Status and limits.** Fifteen public theorems, three private
supporting lemmas and five definitions are Lean-verified. L7c.2
is complete. For unit-duration pulses the X parameter t requires
δ=-2t and the Z parameter p requires η=p. The Z–X–Z protocol
uses independently tunable signed real strengths. Its composition
with matched endpoints and piecewise Schrödinger equations is
proved in §4.104 (L7c.3); its arbitrary-target theorem is proved in §4.105 (L7c.4).
A general unitary propagator on the full complex infinite Hilbert
space is not constructed by these results. The third registered package selects the final preparation theorem and supporting
locality statements; other intermediate results are not separate submissions. The original L6 approximate
control problem and Track A remain separate.


### 4.104. Continuous three-pulse protocol with exact zero leakage

**Plain-English result.** The separate pulses of §4.103 can now be
joined into a single continuous trajectory on the actual infinite
Ammann–Beenker graph. No amplitude or phase is reset at a switch.
Each pulse starts exactly where the preceding pulse ends. The
state remains in the original two-mode plane throughout the
protocol, including both switching times. Its squared complex
norm is conserved, and both real and imaginary parts satisfy
the full natural-domain Schrödinger equations during each open
pulse interval.

The module
[`AmmannBeenkerCoordinatedPulseComposition.lean`](SpectralGeometry/AmmannBeenkerCoordinatedPulseComposition.lean)
uses the exact physical coefficient matrices U_X and U_Z of
§4.103, including their common scalar phases. Let w=(a,b) be
any initial complex dark/bright coefficient pair. For arbitrary
real parameters p,t,q, use the following unit-duration controls:

| Time interval | Detuning δ | Coordinated edge strength η |
| --- | --- | --- |
| [0,1] | 0 | p |
| [1,2] | -2t | 0 |
| [2,3] | 0 | q |

The entries at a shared endpoint describe the left and right
control values; the state itself has a unique value there.
Define a continuous saturated clock

```math
c(s)=\min(\max(s,0),1).
```

It is zero before its interval, equals the local time inside it,
and is one afterwards. The coefficient trajectory is

```math
W(\tau)=U_Z(q,c(\tau-2))\,
U_X(-2t,c(\tau-1))\,
U_Z(p,c(\tau))\,w.
```

All three matrices retain their physical energy phases. The
identity-at-zero property gives W(0)=w and exact segment
matching. In particular,

```math
W(3)=U_Z(q,1)U_X(-2t,1)U_Z(p,1)w.
```

Lean proves the three closed-interval formulas and the two
switch identities. Continuity of the phase, each pulse with
respect to time and continuous input, and the saturated clock
gives continuity of W for every real time. The real and imaginary
full-space embeddings are continuous as well.

**Full-domain dynamics and conservation.** Write
u(τ)=E_Re(W(τ)), v(τ)=E_Im(W(τ)) with the embeddings of §4.103.
The module provides their explicit lifts to the original natural
onsite domain for every τ. On the open intervals (0,1), (1,2)
and (2,3) respectively, Lean proves

```math
u'(\tau)=H_{\delta,\eta}v(\tau),\qquad
v'(\tau)=-H_{\delta,\eta}u(\tau),
```

using the full infinite-graph Hamiltonian with the indicated
control strengths. The proof first identifies the single-pulse
equations in the common coordinates and then transfers them to
the global trajectory by time translation and local equality.
It does not impose differentiability at the control switches,
where the Hamiltonian can jump. Continuity and domain membership
hold there nonetheless. The saturated extension is constant
outside [0,3]; no physical evolution equation outside the
three open pulse intervals is asserted.

For every real τ the exact identities are

```math
\|u(\tau)\|^2+\|v(\tau)\|^2=|a|^2+|b|^2,\qquad
Qu(\tau)=Qv(\tau)=0.
```

Here Q is the exterior component of the original compact-plane
decomposition. Thus the squared complex exterior norm is exactly
zero, including at the switches and endpoints. For normalized
initial coefficients the total squared complex norm is one.
These statements do not use a perturbative small-strength
estimate, a finite graph truncation or a supplied propagator.

| Lean theorem | Meaning |
| --- | --- |
| `coordinatedApplyPair_one`, `coordinatedPulseX_initial`, `coordinatedPulseZ_initial` | Zero-time identity actions |
| `coordinatedState_domain`, `coordinatedState_leakage_zero` | Explicit natural-domain lifts and confinement of each embedded pair |
| `coordinatedStateWeight_eq`, `coordinatedPulseX_weight`, `coordinatedPulseZ_weight` | Squared complex norm and its single-pulse conservation |
| `coordinatedPhase_continuous`, `coordinatedPulseX_continuous`, `coordinatedPulseZ_continuous` | Continuity of phases and pulse actions |
| `coordinatedClock_zero`, `coordinatedClock_one`, `coordinatedClock_inside`, `coordinatedClock_continuous` | Saturated local-time clock |
| `coordinatedProtocol_first`, `coordinatedProtocol_second`, `coordinatedProtocol_third` | Exact closed-interval segment formulas |
| `coordinatedProtocol_initial`, `coordinatedProtocol_join_one`, `coordinatedProtocol_join_two`, `coordinatedProtocol_final` | Initial state, exact switch matching and final composition |
| `coordinatedProtocol_continuous`, `coordinatedProtocol_state_continuous` | Continuous coefficient path and both full-space components |
| `coordinatedProtocol_weight`, `coordinatedProtocol_leakage_zero`, `coordinatedProtocol_domain` | Conserved norm, zero leakage and natural-domain membership at all times |
| `coordinatedPulseX_solvesAt`, `coordinatedPulseZ_solvesAt` | Full natural-domain equations in common coordinates |
| `coordinatedSolvesAt_shift`, `coordinatedSolvesAt_congr` | Time translation and local equality of Schrödinger solutions |
| `coordinatedProtocol_solves_first`, `coordinatedProtocol_solves_second`, `coordinatedProtocol_solves_third` | Full switched trajectory solves the equations on each open interval |

**Status and limits.** Thirty-four public theorems and ten
definitions are Lean-verified. L7c.3 is complete. The construction
works for arbitrary initial coefficient pairs in the compact
plane and arbitrary real p,t,q. It supplies an actual continuous
piecewise differentiable full-graph trajectory in the real/imaginary
representation, not just a product of endpoint matrices.
Section 4.105 (L7c.4) combines the final coefficient product with the
constructive Euler reachability theorem of §4.101 to choose the
parameters for every normalized target from dark, retaining the
common scalar phase. The general complex Hilbert-space unitary
propagator for arbitrary infinite-space initial data remains a
separate objective. No experimental feasibility or minimal number
of controlled edges is claimed. The third registered package selects the final preparation theorem and locality
statements; the intermediate composition results are not separate submissions. L6 and Track A
remain preserved.


### 4.105. Exact arbitrary target preparation from dark without leakage

**Plain-English result.** Any normalized mixture of the two original
localized waves can be prepared from the dark wave by three consecutive
local control pulses on the actual infinite Ammann–Beenker graph.
The final state differs from the chosen target only by a common phase.
During the whole protocol no amplitude escapes the original two-mode
plane, the norm remains one, and the state is continuous. The two
real Hilbert-space components satisfy the exact natural-domain
Schrödinger equations on the open pulse intervals. This completes
the central L7 preparation objective without assuming a general
propagator or making a small-perturbation approximation.

The module
[`AmmannBeenkerCoordinatedExactPreparation.lean`](SpectralGeometry/AmmannBeenkerCoordinatedExactPreparation.lean)
combines the constructive matrix reachability of §4.101 with the
actual phase-retaining trajectories of §§4.102–4.104.

**Exact final phase.** Let E_* be the crossing energy and D,F the
normalized dark and bright modes. The three unit-duration controls
are (δ,η)=(0,p),(-2t,0),(0,q). The physical endpoint matrix is

```math
U_Z(q,1)U_X(-2t,1)U_Z(p,1)
=e^{i\theta}R_Z(q)R_X(t)R_Z(p),
\qquad \theta=-3E_*+t-p-q.
```

The scalar factor has modulus one. This identity holds for arbitrary
real p,t,q, including when applied to any initial coefficient pair.
In particular the final coefficients starting from dark are

```math
e^{i\theta}\left(\cos(t)e^{i(p+q)},
i\sin(t)e^{i(p-q)}\right).
```

For a chosen complex pair (α,β) with |α|²+|β|²=1, the earlier
constructive Euler proof chooses t=arccos|α|, with
0≤t≤π/2, and p=(u+v)/2, q=(u−v)/2, where u=arg(α)
and v=arg(−iβ). Its phase identities also cover zero coefficients.
Thus there exist p,t,q for which the physical endpoint is exactly
e^{iθ}(α,β). The phase is not removed between pulses.

**Bundled full-graph theorem.** The theorem
`coordinatedProtocol_exact_preparation` proves the existence
of those parameters and all of the following properties for
the same trajectory f=coordinatedProtocolPair p t q (1,0).
Writing u and v for its real and imaginary full-space embeddings,
the initial state is u(0)=D, v(0)=0, and the final components are

```math
u(3)=\operatorname{Re}(e^{i\theta}\alpha)D+
      \operatorname{Re}(e^{i\theta}\beta)F,\qquad
v(3)=\operatorname{Im}(e^{i\theta}\alpha)D+
      \operatorname{Im}(e^{i\theta}\beta)F.
```

The coefficient path and both graph components are continuous.
For every real time both components belong to the original
natural onsite domain, and

```math
\|u(\tau)\|^2+\|v(\tau)\|^2=1,\qquad
Qu(\tau)=Qv(\tau)=0.
```

On the three open intervals (0,1), (1,2), (2,3), respectively,
the components satisfy u'=H_{δ,η}v and v'=−H_{δ,η}u
for the actual full Hamiltonian at the stated strengths.
The norm and zero-leakage identities include all switching times
and endpoints; differentiability across a control jump is not
required. The constant extension outside the protocol is not
asserted to solve a physical evolution equation there.

| Lean theorem | Meaning |
| --- | --- |
| `coordinatedProtocolAngle_eq`, `coordinatedProtocolPhase_norm` | Exact accumulated scalar phase and its unit modulus |
| `coordinatedProtocolMatrix_rotation` | Exact physical three-pulse matrix equals the phase-weighted Euler product |
| `coordinatedProtocol_final_rotation` | Physical endpoint for arbitrary initial coefficient pairs |
| `coordinatedProtocol_final_dark` | Explicit endpoint coefficients starting from dark |
| `coordinatedProtocol_reaches_from_dark` | Existence of parameters reaching every normalized complex target up to the stated phase |
| `coordinatedState_dark_initial`, `coordinatedProtocol_dark_weight` | Exact dark initial state and unit squared complex norm |
| `coordinatedProtocol_exact_preparation` | Combined endpoint, continuity, domain, norm, zero leakage and full piecewise Schrödinger equations |

**Status and limits.** The ten public theorems, one private
supporting lemma and one definition are Lean-verified. L7a–L7c.4
complete the exact dark-to-arbitrary-target preparation objective.
The state is represented by real and imaginary vectors of the full
infinite graph. A separate construction of a general complex
Hilbert-space unitary propagator for arbitrary initial data is
still open. The theorem starts from dark; arbitrary initial-to-target
control as a separately formalized result, exact phase-sensitive
preparation without quotienting by global phase, constraints on
physical edge strengths, experimental feasibility, and minimal
control resources are not claimed. The two independently tunable
controls are those defined in §§4.99–4.100; this is not the original
single-edge L6 preparation theorem. L7 has passed independent comparison and was registered separately on 25 November 2026 as [PALOMAR-2026-11-25-000001 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-25-000001&version=1). The earlier registrations
and all Track A objectives remain unchanged.

**Independent preparation package.** The [Mathlib-only Challenge](Challenge.lean)
contains 687 lines, five model witnesses, three local-edge certificates
and the single scientific preparation theorem. All definitions are concrete.
The [Solution](Solution.lean) imports the verified source, and the
[Comparator](palomar/exact-leakage-free-preparation/comparator.json) is kept
in the third registered package directory. Full Lean verification and independent
statement comparison with NanoDa and con-ron have passed. Palomar's mechanical and renderability checks passed, and its automated editorial review identified no blocking problem.


## 5. Building and verification

The canonical import list is maintained in [`SpectralGeometry.lean`](SpectralGeometry.lean). It imports **116 Lean modules**: eleven analytic and window modules, four finite-dimensional geometry modules, and one hundred and one infinite geometry/operator/spectral modules (including domain-generic interfaces). The full library is Lean-verified. The original fourteen bright generator lemmas and the fifteenth bundled theorem are distinct from the later spectral-level results in §4.93.

- **Analytic core, indexed points and certified windows (11):**
  - [`CanonicalProduct.lean`](SpectralGeometry/CanonicalProduct.lean)
  - [`CanonicalProductAnalytic.lean`](SpectralGeometry/CanonicalProductAnalytic.lean)
  - [`CanonicalProductZeroOrder.lean`](SpectralGeometry/CanonicalProductZeroOrder.lean)
  - [`IndexedSpectralPoints.lean`](SpectralGeometry/IndexedSpectralPoints.lean)
  - [`OrderedSpectralWindow.lean`](SpectralGeometry/OrderedSpectralWindow.lean)
  - [`CanonicalProductClusterCount.lean`](SpectralGeometry/CanonicalProductClusterCount.lean)
  - [`AnalyticZeroLocalization.lean`](SpectralGeometry/AnalyticZeroLocalization.lean)
  - [`CanonicalProductApproximation.lean`](SpectralGeometry/CanonicalProductApproximation.lean)
  - [`AnalyticDiskZeroCount.lean`](SpectralGeometry/AnalyticDiskZeroCount.lean)
  - [`AnalyticRouche.lean`](SpectralGeometry/AnalyticRouche.lean)
  - [`CanonicalProductNumericalBounds.lean`](SpectralGeometry/CanonicalProductNumericalBounds.lean)
- **Finite-dimensional geometry (4):**
  - [`FinitePerturbation.lean`](SpectralGeometry/FinitePerturbation.lean)
  - [`FinitePositiveEnergy.lean`](SpectralGeometry/FinitePositiveEnergy.lean)
  - [`FiniteGeometricEnergy.lean`](SpectralGeometry/FiniteGeometricEnergy.lean)
  - [`FiniteStrictPositivity.lean`](SpectralGeometry/FiniteStrictPositivity.lean)
- **Onsite foundations, growth and summability (6):**
  - [`InfiniteOnsite.lean`](SpectralGeometry/InfiniteOnsite.lean)
  - [`InfiniteOnsiteDensity.lean`](SpectralGeometry/InfiniteOnsiteDensity.lean)
  - [`InfiniteOnsiteEigenvalues.lean`](SpectralGeometry/InfiniteOnsiteEigenvalues.lean)
  - [`InfiniteOnsiteSummability.lean`](SpectralGeometry/InfiniteOnsiteSummability.lean)
  - [`InfiniteOnsitePowerGrowth.lean`](SpectralGeometry/InfiniteOnsitePowerGrowth.lean)
  - [`InfiniteOnsiteOrderedEnumeration.lean`](SpectralGeometry/InfiniteOnsiteOrderedEnumeration.lean)
- **Infinite interactions and local-operator estimates (11):**
  - [`InfiniteFiniteEdgeInteraction.lean`](SpectralGeometry/InfiniteFiniteEdgeInteraction.lean)
  - [`InfiniteBoundedPerturbation.lean`](SpectralGeometry/InfiniteBoundedPerturbation.lean)
  - [`InfiniteSummableEdgeInteraction.lean`](SpectralGeometry/InfiniteSummableEdgeInteraction.lean)
  - [`InfiniteLocalMatching.lean`](SpectralGeometry/InfiniteLocalMatching.lean)
  - [`InfiniteLocalBoundedDegree.lean`](SpectralGeometry/InfiniteLocalBoundedDegree.lean)
  - [`InfiniteLocalEigenvalueBounds.lean`](SpectralGeometry/InfiniteLocalEigenvalueBounds.lean)
  - [`InfiniteLocalSignedPerturbationGap.lean`](SpectralGeometry/InfiniteLocalSignedPerturbationGap.lean)
  - [`InfiniteLocalCoerciveGap.lean`](SpectralGeometry/InfiniteLocalCoerciveGap.lean)
  - [`InfiniteLocalGraphNorm.lean`](SpectralGeometry/InfiniteLocalGraphNorm.lean)
  - [`InfiniteLocalClosedGraph.lean`](SpectralGeometry/InfiniteLocalClosedGraph.lean)
  - [`InfiniteLocalAdjointCharacterization.lean`](SpectralGeometry/InfiniteLocalAdjointCharacterization.lean)
- **Onsite resolvents and compactness (4):**
  - [`InfiniteOnsiteResolvent.lean`](SpectralGeometry/InfiniteOnsiteResolvent.lean)
  - [`InfiniteOnsiteFiniteLowEnergy.lean`](SpectralGeometry/InfiniteOnsiteFiniteLowEnergy.lean)
  - [`InfiniteOnsiteCompactResolvent.lean`](SpectralGeometry/InfiniteOnsiteCompactResolvent.lean)
  - [`InfiniteOnsiteResolventIdentity.lean`](SpectralGeometry/InfiniteOnsiteResolventIdentity.lean)
- **Interacting resolvents and spectral results (21):**
  - [`InfiniteLocalCompactResolvent.lean`](SpectralGeometry/InfiniteLocalCompactResolvent.lean)
  - [`InfiniteLocalCompactResolventBounds.lean`](SpectralGeometry/InfiniteLocalCompactResolventBounds.lean)
  - [`InfiniteLocalSelfAdjointPMap.lean`](SpectralGeometry/InfiniteLocalSelfAdjointPMap.lean)
  - [`InfiniteLocalResolventSpectrum.lean`](SpectralGeometry/InfiniteLocalResolventSpectrum.lean)
  - [`InfiniteLocalEigenpairCorrespondence.lean`](SpectralGeometry/InfiniteLocalEigenpairCorrespondence.lean)
  - [`InfiniteLocalFullEigenspaces.lean`](SpectralGeometry/InfiniteLocalFullEigenspaces.lean)
  - [`InfiniteLocalFredholmSpectralExhaustion.lean`](SpectralGeometry/InfiniteLocalFredholmSpectralExhaustion.lean)
  - [`InfiniteLocalFullEigenvectorsComplete.lean`](SpectralGeometry/InfiniteLocalFullEigenvectorsComplete.lean)
  - [`InfiniteLocalResolventNormGap.lean`](SpectralGeometry/InfiniteLocalResolventNormGap.lean)
  - [`InfiniteLocalResolventSpectralIsolation.lean`](SpectralGeometry/InfiniteLocalResolventSpectralIsolation.lean)
  - [`InfiniteLocalFullEigenvalueIsolation.lean`](SpectralGeometry/InfiniteLocalFullEigenvalueIsolation.lean)
  - [`InfiniteLocalFullEigenvalueEnumeration.lean`](SpectralGeometry/InfiniteLocalFullEigenvalueEnumeration.lean)
  - [`InfiniteLocalFullRealResolvent.lean`](SpectralGeometry/InfiniteLocalFullRealResolvent.lean)
  - [`InfiniteLocalFullEigenvalueMultiplicity.lean`](SpectralGeometry/InfiniteLocalFullEigenvalueMultiplicity.lean)
  - [`InfiniteLocalFullEigenvalueMultiplicityCoverage.lean`](SpectralGeometry/InfiniteLocalFullEigenvalueMultiplicityCoverage.lean)
  - [`InfiniteLocalFullRealSpectralCompleteness.lean`](SpectralGeometry/InfiniteLocalFullRealSpectralCompleteness.lean)
  - [`InfiniteLocalFullOrderedMultiplicityWindows.lean`](SpectralGeometry/InfiniteLocalFullOrderedMultiplicityWindows.lean)
  - [`InfiniteLocalFullGlobalOrderedEnumeration.lean`](SpectralGeometry/InfiniteLocalFullGlobalOrderedEnumeration.lean)
  - [`InfiniteLocalFullOrderedEigenvalueDivergence.lean`](SpectralGeometry/InfiniteLocalFullOrderedEigenvalueDivergence.lean)
  - [`InfiniteLocalFullVariationalComparison.lean`](SpectralGeometry/InfiniteLocalFullVariationalComparison.lean)
  - [`InfiniteLocalFullLowEnergyCounting.lean`](SpectralGeometry/InfiniteLocalFullLowEnergyCounting.lean)

- **Simultaneous observation, variational control and full summability (12):**
  - [`DomainSpectralSubspace.lean`](SpectralGeometry/DomainSpectralSubspace.lean)
  - [`InfiniteLowEnergyObservation.lean`](SpectralGeometry/InfiniteLowEnergyObservation.lean)
  - [`InfiniteLowEnergyCounting.lean`](SpectralGeometry/InfiniteLowEnergyCounting.lean)
  - [`InfiniteLocalFullSpectralObservation.lean`](SpectralGeometry/InfiniteLocalFullSpectralObservation.lean)
  - [`DomainEigenbasis.lean`](SpectralGeometry/DomainEigenbasis.lean)
  - [`InfiniteLocalFullEigenbasis.lean`](SpectralGeometry/InfiniteLocalFullEigenbasis.lean)
  - [`OrderedVariationalPrinciple.lean`](SpectralGeometry/OrderedVariationalPrinciple.lean)
  - [`OrderedLevelMultiplicityTwo.lean`](SpectralGeometry/OrderedLevelMultiplicityTwo.lean)
  - [`InfiniteOrderedSpectralControl.lean`](SpectralGeometry/InfiniteOrderedSpectralControl.lean)
  - [`InfiniteOrderedSpectralExistence.lean`](SpectralGeometry/InfiniteOrderedSpectralExistence.lean)
  - [`InfiniteFullSpectralSummability.lean`](SpectralGeometry/InfiniteFullSpectralSummability.lean)
  - [`InfinitePositiveSpectralControl.lean`](SpectralGeometry/InfinitePositiveSpectralControl.lean)

- **Full spectral products and analytic zero response (7):**
  - [`InfiniteFullSpectralProduct.lean`](SpectralGeometry/InfiniteFullSpectralProduct.lean)
  - [`OrderedSpectralProductBridge.lean`](SpectralGeometry/OrderedSpectralProductBridge.lean)
  - [`FiniteSectorZeroResponse.lean`](SpectralGeometry/FiniteSectorZeroResponse.lean)
  - [`PositiveFiniteSectorZeroResponse.lean`](SpectralGeometry/PositiveFiniteSectorZeroResponse.lean)
  - [`FullSpectralZeroLocalization.lean`](SpectralGeometry/FullSpectralZeroLocalization.lean)
  - [`FullSpectralZeroCounts.lean`](SpectralGeometry/FullSpectralZeroCounts.lean)
  - [`LinearOnsiteZeroCertificate.lean`](SpectralGeometry/LinearOnsiteZeroCertificate.lean)

- **Explicit octagonal geometry, operator and spectral products (38):**
  - [`AmmannBeenkerCutProject.lean`](SpectralGeometry/AmmannBeenkerCutProject.lean)
  - [`AmmannBeenkerGraph.lean`](SpectralGeometry/AmmannBeenkerGraph.lean)
  - [`AmmannBeenkerOperator.lean`](SpectralGeometry/AmmannBeenkerOperator.lean)
  - [`AmmannBeenkerSummability.lean`](SpectralGeometry/AmmannBeenkerSummability.lean)
  - [`AmmannBeenkerSpectralProducts.lean`](SpectralGeometry/AmmannBeenkerSpectralProducts.lean)
  - [`AmmannBeenkerRadialGap.lean`](SpectralGeometry/AmmannBeenkerRadialGap.lean)
  - [`AmmannBeenkerCompactModes.lean`](SpectralGeometry/AmmannBeenkerCompactModes.lean)
  - [`AmmannBeenkerCompactStates.lean`](SpectralGeometry/AmmannBeenkerCompactStates.lean)
  - [`AmmannBeenkerCompactCrossing.lean`](SpectralGeometry/AmmannBeenkerCompactCrossing.lean)
  - [`AmmannBeenkerEdgeControl.lean`](SpectralGeometry/AmmannBeenkerEdgeControl.lean)
  - [`AmmannBeenkerTwoControlAlgebra.lean`](SpectralGeometry/AmmannBeenkerTwoControlAlgebra.lean)
  - [`AmmannBeenkerQubitLeakage.lean`](SpectralGeometry/AmmannBeenkerQubitLeakage.lean)
  - [`QubitLeakagePulseBound.lean`](SpectralGeometry/QubitLeakagePulseBound.lean)
  - [`DomainEigenbasisGapResidual.lean`](SpectralGeometry/DomainEigenbasisGapResidual.lean)
  - [`AmmannBeenkerNearCrossingEigenvectors.lean`](SpectralGeometry/AmmannBeenkerNearCrossingEigenvectors.lean)
  - [`AmmannBeenkerPulseResidualBound.lean`](SpectralGeometry/AmmannBeenkerPulseResidualBound.lean)
  - [`AmmannBeenkerPulseIntertwining.lean`](SpectralGeometry/AmmannBeenkerPulseIntertwining.lean)
  - [`AmmannBeenkerPulseSelfAdjoint.lean`](SpectralGeometry/AmmannBeenkerPulseSelfAdjoint.lean)
  - [`AmmannBeenkerPostpulseSwitchOff.lean`](SpectralGeometry/AmmannBeenkerPostpulseSwitchOff.lean)
  - [`AmmannBeenkerDarkSchrodinger.lean`](SpectralGeometry/AmmannBeenkerDarkSchrodinger.lean)
  - [`AmmannBeenkerBrightAmplitude.lean`](SpectralGeometry/AmmannBeenkerBrightAmplitude.lean) *(14 original generator theorems and one combined Palomar-candidate theorem)*
  - [`AmmannBeenkerBrightSpectralSplitting.lean`](SpectralGeometry/AmmannBeenkerBrightSpectralSplitting.lean) *(Lean-verified L1–L5, including the signed splitting, simple pair and quantitative exterior/energy bounds; §§4.93–4.98)*
  - [`AmmannBeenkerCoordinatedRingControl.lean`](SpectralGeometry/AmmannBeenkerCoordinatedRingControl.lean) *(eleven L7a theorems: matched edges, exact dark cancellation and full-space symmetry; §4.99)*
  - [`AmmannBeenkerCoordinatedInvariantPlane.lean`](SpectralGeometry/AmmannBeenkerCoordinatedInvariantPlane.lean) *(verified L7a completion and exact dark/bright action; §4.100)*
  - [`AmmannBeenkerCoordinatedLieAlgebra.lean`](SpectralGeometry/AmmannBeenkerCoordinatedLieAlgebra.lean) *(verified L7b Pauli decomposition and commutators; §4.100)*
  - [`AmmannBeenkerCoordinatedLieGeneration.lean`](SpectralGeometry/AmmannBeenkerCoordinatedLieGeneration.lean) *(full real su(2) generation; §4.101)*
  - [`AmmannBeenkerCoordinatedEuler.lean`](SpectralGeometry/AmmannBeenkerCoordinatedEuler.lean) *(constructive normalized-pair Euler rotations and independent signed generator coefficients; §4.101)*
  - [`AmmannBeenkerCoordinatedPairDynamics.lean`](SpectralGeometry/AmmannBeenkerCoordinatedPairDynamics.lean) *(exact natural-domain complex-component eigenpair trajectories; §4.102)*
  - [`AmmannBeenkerCoordinatedAxisDynamics.lean`](SpectralGeometry/AmmannBeenkerCoordinatedAxisDynamics.lean) *(single-axis Schrödinger equations, norm conservation, zero leakage and full real self-adjointness; §4.102)*
  - [`AmmannBeenkerCoordinatedRotationDynamics.lean`](SpectralGeometry/AmmannBeenkerCoordinatedRotationDynamics.lean) *(exact phase-weighted rotation action and embedding into full natural-domain trajectories; §4.103)*
  - [`AmmannBeenkerCoordinatedPulseComposition.lean`](SpectralGeometry/AmmannBeenkerCoordinatedPulseComposition.lean) *(continuous three-pulse trajectory, switch matching, full-domain equations, conserved norm and zero leakage; §4.104)*
  - [`AmmannBeenkerCoordinatedExactPreparation.lean`](SpectralGeometry/AmmannBeenkerCoordinatedExactPreparation.lean) *(exact arbitrary normalized target preparation from dark up to global phase with continuous full-domain zero-leakage dynamics; §4.105)*
  - [`AmmannBeenkerCentralPatch.lean`](SpectralGeometry/AmmannBeenkerCentralPatch.lean)
  - [`AmmannBeenkerCentralKernel.lean`](SpectralGeometry/AmmannBeenkerCentralKernel.lean)
  - [`AmmannBeenkerCrossingMultiplicity.lean`](SpectralGeometry/AmmannBeenkerCrossingMultiplicity.lean)
  - [`AmmannBeenkerCrossingGapCycle.lean`](SpectralGeometry/AmmannBeenkerCrossingGapCycle.lean)
  - [`AmmannBeenkerCrossingGapFinite.lean`](SpectralGeometry/AmmannBeenkerCrossingGapFinite.lean)
  - [`AmmannBeenkerCrossingGapOrthogonality.lean`](SpectralGeometry/AmmannBeenkerCrossingGapOrthogonality.lean)

- **Bounded spectral errors and full zero-cluster certificates (2):**
  - [`InfiniteBoundedSpectralStability.lean`](SpectralGeometry/InfiniteBoundedSpectralStability.lean)
  - [`InfiniteFullSpectralCluster.lean`](SpectralGeometry/InfiniteFullSpectralCluster.lean)

The project uses Lean 4 `v4.35.0` with its corresponding Mathlib version. Every module listed above is imported by the root entry point.

```bash
lake exe cache get
lake build SpectralGeometry Challenge Solution
```

The Lean and Mathlib versions are pinned by `lean-toolchain` and
`lake-manifest.json`. Run `lake update` only when intentionally updating
dependencies, not as part of routine verification. `Challenge.lean`
contains deliberate statement placeholders (`sorry`), and is judged
against the substantive proof modules by Comparator rather than being
treated as an independently proved library.

**Palomar / independent statement verification.** The active root
[Challenge](Challenge.lean), [Solution](Solution.lean) and
[formalization metadata](formalization.yaml) describe the third result:
Exact Leakage-Free Quantum State Preparation on an Infinite Ammann–Beenker Graph (§4.105).
The selected scientific conclusion is
`SpectralGeometry.AmmannBeenker.coordinatedProtocol_exact_preparation`.
Five supporting model witnesses and three locality certificates are
selected alongside it. The Mathlib-only Challenge contains concrete
definitions and nine deliberate proposition proof placeholders; no
definition holes are selected. The Solution imports the substantive
preparation proof module, not Challenge.

The active [theorem-specific Comparator](palomar/exact-leakage-free-preparation/comparator.json)
and matching package snapshots reside in
[`palomar/exact-leakage-free-preparation/`](palomar/exact-leakage-free-preparation/).
The complete 116-module substantive library is Lean-verified with no
proof holes. The third independent comparison has passed, including
NanoDa and con-ron. The third result is registered as [PALOMAR-2026-11-25-000001 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-25-000001&version=1).

The first registered exact-multiplicity theorem remains attached to
its original immutable revision. The second registered signed-splitting
package, with [Comparator](palomar/signed-bright-splitting/comparator.json),
Challenge, Solution and metadata snapshots, is preserved in
[`palomar/signed-bright-splitting/`](palomar/signed-bright-splitting/).
It retains [PALOMAR-2026-11-23-000017 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-23-000017&version=1).
The unsubmitted generator-response package remains archived under
[`palomar/dark-bright/`](palomar/dark-bright/).
No root `comparator.json` exists. The local packaging and verification
checks select the third registered package's Comparator explicitly.

Challenge mirrors the source module boundaries when generating auxiliary
proof names: only Lean's module-local auxiliary-proof cache is reset between
blocks. Kernel declarations and the full definition comparison are unchanged.

**Human direction and AI-generated mathematics:** Alessandro Odasso
conceived and directs the project. He is **not a mathematician**; his
motivation is to investigate the scientific capabilities of large language
models. According to his account, **AI generated the theorem statements,
mathematical proof development and Lean formalizations** under his research
direction. This is intentionally a stronger and more transparent description
than calling the work merely "AI-assisted". It does not imply that Odasso
independently authored the formal mathematics, or that AI-generated claims
were accepted without checking: substantive Lean proofs are verified by
the Lean kernel, and the independently specified Palomar selection requires
its own Comparator verification. Formal correctness does not by itself
establish mathematical novelty or scientific importance. See §4.92 and
[formalization.yaml](formalization.yaml) for the mathematical scope, research
provenance, and intended audiences.

To run the independent statement comparison on a supported Linux runner
with Bubblewrap configured, execute:

```bash
python3 scripts/check-unified-comparator.py
bash scripts/verify-comparator.sh
```

The automated verification workflow first checks the complete Lean library
and then performs packaging, metadata and independent Lean, NanoDa and
con-ron comparison of the **selected** Challenge statements.
Cached pinned dependencies and compiled artifacts speed up verification
without replacing the full build or independent comparison. The workflow
configuration documents the operational details.

## 6. Roadmap: proof status and next steps

**The original goal remains unchanged:** obtain quantitative response
theorems for zeros of canonical products associated with explicitly
specified geometric interventions on infinite operators. The finite-site
observation theorem (§4.40), abstract response results, full spectral
products and the confined Ammann–Beenker application establish much
of its formal infrastructure.

**Two complementary lines of work are now tracked explicitly:**

1. **Track A — spectral geometry and analytic zeros.** The verified
   foundations and product-response work are recorded in §§6.1–6.4;
   the main remaining goals are numerical cofactor/isolation
   certificates for the interacting geometric product (§6.3),
   finite-rank relative determinants (§6.5), certified finite-patch
   approximations (§6.6), and optional exploratory zero statistics
   (§6.7). Their validity and priority do not depend on solving
   quantum control.
2. **Track B — localized dark/bright modes and control.** The full
   infinite-graph crossing and isolation (§§4.78–4.79) and
   quantitative L1–L5 splitting (§§4.93–4.97) are verified.
   **L7a is verified (§§4.99–4.100):** the eight matched edges
   preserve the entire original dark–bright plane exactly under both
   controls. **L7b is complete algebraically (§§4.100–4.101):** full
   su(2) generation and constructive matrix reachability from dark.
   L7c.1–4 verify exact single-axis trajectories, phase-weighted rotations,
   continuous three-pulse dynamics and arbitrary normalized target preparation
   from dark with zero leakage (§§4.102–4.105). General complex unitary
   evolution remains open. **L6 remains the deferred original
   single-edge approximate-control program**, not a cancelled goal.
   The [detailed control roadmap](docs/bright-spectral-splitting-roadmap.md)
   separates these tasks and their proof obligations.

**Research status and verification.** L5 is registered as described in §4.98.
L7a, L7b and L7c.1–4 are Lean-verified (§§4.99–4.105); the final preparation theorem and supporting locality certificates have passed independent statement comparison and are registered as [PALOMAR-2026-11-25-000001 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-25-000001&version=1).
The L7 exact zero-leakage preparation theorem from dark is proved.
A general complex quantum propagator and the distinct L6 reachability
theorem remain open. Earlier conditional time-uniform leakage bounds
retain their separate scope.

A checked item below denotes an actual substantive Lean result
under its stated hypotheses; an unchecked item is an open task.
P2, P3 and P4 are research phases, not numbered new theorems.
All historical verified results and the complete §5 Lean-module
catalogue are retained.

### 6.1. P2 — Spectral foundations and the complex-resolvent interface

**Formalized foundations**

- [x] Define the natural onsite domain, prove its density and establish
  closedness and adjoint characterizations for the relevant operators
  (§§4.1–4.2, 4.13–4.15).
- [x] Construct bounded infinite matching interactions and their energy and
  norm bounds (§§4.6–4.12).
- [x] Prove self-adjointness in Mathlib's partial-operator API and compact
  shifted resolvents under the explicit properness, gap, symmetry and
  bounded-correction hypotheses (§§4.16–4.22).
- [x] Connect full-operator eigenvectors with compact-resolvent eigenspaces;
  prove finite geometric multiplicity, orthogonality and completeness in
  the self-adjoint setting (§§4.23–4.27).
- [x] Identify the real bounded-inverse spectrum with genuine real
  eigenvalues, with isolation, local finiteness and countability
  (§§4.28–4.32).
- [x] Prove positive multiplicity, exact multiplicity-tagged coverage and
  completeness indexed by real spectral levels (§§4.33–4.35).
- [x] Construct sorted finite spectral windows and a globally ordered,
  exact, injective infinite tag enumeration; prove qualitative divergence
  under the stated lower-bound and infinitude hypotheses (§§4.36–4.38).

**Open complex-resolvent interface for relative products (§6.5)**

- [ ] Construct the required complexification and complex shifted inverse
  on the natural domain, and relate it to the verified real spectral data.
- [ ] Prove the resolvent identities, analyticity and compression facts
  needed to define $G_S(z)$. The real completeness theorem is not by
  itself this complex-resolvent interface.
- [x] Establish infinitude and a positive lower bound before invoking the
  infinite enumeration for the explicit octagonal vertex graph (§§4.68–4.70).
  Finite and empty models continue to use the separate existing interfaces.

### 6.2. P2 — Quantitative observation and control of low-energy levels

**Formalized inputs**

- [x] Bound the full quadratic form relative to onsite multiplication by
  $\|B\|\|\psi\|^2$, and obtain a positive real-spectrum gap under the
  explicit hypotheses of §4.39.
- [x] Prove finite-coordinate detection and an injective restriction on
  each complete low-energy eigenspace, yielding its geometric
  multiplicity bound (§4.40).
- [x] Establish inverse-square summability for suitable linearly or
  power-law growing onsite-only levels (§§4.4–4.5).

**Verified simultaneous observation and spectral comparison (§§4.41–4.46)**

Assume the self-adjoint compact-resolvent setting, $V(t)\ge v_0$,
$C=\|B\|$, $R>v_0$, and $E<R-C$. Set
```math
F_R=\{t:V(t)\le R\},
\qquad
\kappa=\frac{R-C-E}{R-v_0}>0.
```

- [x] Strengthen the existing eigenspace restriction theorem to the
  quantitative estimate
  ```math
  \|P_{F_R}\psi\|^2\ge\kappa\|\psi\|^2
  ```
  for the entire spectral subspace below or at $E$, including linear
  combinations from distinct levels. Verify the domain, finite-dimensional
  and spectral-subspace hypotheses explicitly.
- [x] Derive the multiplicity-aware counting bound
  ```math
  \sum_{\substack{\lambda\in\sigma_{\mathrm{real}}(H)\\
                   \lambda<R-\|B\|}}m_H(\lambda)
  \le\#\{t:V(t)\le R\}.
  ```
  The separate bounds on individual eigenspaces in §4.40 cannot simply be
  summed to obtain it.
- [x] Connect the exact ordered enumeration to a variational/counting
  principle and prove
  ```math
  v_n-\|B\|\le\lambda_n(H)\le v_n+\|B\|,
  ```
  for onsite levels $v_n$ and full levels ordered with the same
  multiplicity convention. Exploit a nonnegative Laplacian to sharpen
  the lower bound where applicable.

**Verified finite-sector response and sufficient summability (§§4.46–4.48)**

- [x] For $H_\tau=H+\tau P_{F_R}$, prove
  ```math
  \kappa\tau
  \le\lambda_n(H_\tau)-\lambda_n(H)
  \le\tau,
  \qquad
  \lambda_n(H)\le E,\quad 0\le\tau\le R-v_0.
  ```
  The proof controls ordered levels with multiplicities and does not
  assume simple eigenvalues. The verified form-comparison route establishes
  ```math
  H\ge(R-C)I-(R-v_0)P_{F_R}
  ```
  on the natural domain and applies the proved variational comparison.
- [x] Transfer sufficient quantitative onsite growth to the ordered full
  eigenvalues and prove full-spectrum inverse-square summability.
  Positivity must also be verified; compact resolvent alone is insufficient.
- [x] Preserve the required positive gap and summability for nonnegative
  finite-sector perturbations, and prove existence of the ordered spectra
  throughout the response interval. Self-adjointness and compact shifted
  inverses are supplied by §§4.47–4.48; the resolvent shift may vary with the
  parameter.

**Verified signed-error extension, onsite ordering and positive interactions**

- [x] Preserve a supplied positive gap and inverse-square summability for
  symmetric bounded perturbations of either sign with $\|K\|<\gamma$,
  where $\gamma$ is the baseline gap (§4.55). Section 4.56 derives complete
  perturbed spectra and exact products under its sufficient onsite
  hypotheses. This includes small signed finite-support interventions;
  it does not cover errors exceeding the verified gap.
- [x] Derive a sorted onsite site bijection from finite onsite sublevel
  sets on an infinite site type (§4.57), including repeated onsite energies.
  Existing comparison/transfer APIs may still accept the bijection as an
  input; the existence obligation is now proved. The construction is
  noncomputable and does not enumerate finite or empty types by $\mathbb N$.
- [x] Package the sharper positive-interaction comparison with its gap and
  summability argument (§4.58). For symmetric nonnegative bounded $B$,
  $V\ge v_0>0$, properness and onsite inverse-square summability give the
  gap $v_0$ and summability of the full spectrum, without $v_0>\|B\|$.
  The matching-Laplacian corollary constructs the ordered spectrum under
  the existing involution and nonnegative-weight hypotheses.
- [x] Prove the stronger sector form bound and response for nonnegative
  interactions:
  ```math
  H\ge R I-(R-v_0)P_F,\qquad
  \frac{R-E}{R-v_0}\,\tau
  \le\lambda_n(H+\tau P_F)-\lambda_n(H)\le\tau.
  ```
  Here $R>v_0$, $\lambda_n(H)\le E<R$, $0\le\tau\le R-v_0$, and
  $V\ge R$ outside the finite sector. The positive-interaction family
  preserves its gap and summability for all $\tau\ge0$; the quantitative
  response retains the stated interval. Section 4.59 transfers this
  stronger estimate to the actual indexed full-product zeros.

**Scope of the verified statements.** The norm comparison and growth transfer
use a sorted bijection of the onsite sites, now supplied by §4.57 under
properness and infinitude. Ordered full levels
come from complete domain eigenbases; §4.44 connects the original exact tags,
and §4.47 derives their existence for infinite site types, proper lower-bounded
$V$ and symmetric bounded corrections. The sufficient positive-summability
package of §4.48 uses $v_0>\|B\|$ and summable onsite inverse squares (or the
proved power-growth criterion). The positive-interaction alternative in
§4.58 only requires the positive onsite lower bound $v_0>0$, together with
properness and onsite summability. Finite/empty cases are covered by observation, counting
and tag bases; the $\mathbb N$-sequence statements explicitly address the
infinite case.

This phase now supplies a proved abstract consequence of finite observation:
a finite onsite intervention has a controlled effect on every selected low
ordered level. Sections 4.52 and 4.59 transfer the respective norm-penalty and
positive-interaction responses to the indexed zeros of both full spectral
products. All the listed abstract obligations of this subsection are proved
under their stated hypotheses. Sections 4.68–4.70 now establish an explicit
vertex graph and a nonempty nine-level window for §6.4. Sections 4.71–4.72
now prove geometric summability and exact full-product zero response. Local scalar analytic
certificates and exact disk counts are now available in §6.3, together
with a numerical worked onsite certificate and quantitative tails for its
nonnegative interacting family (§§4.66–4.67). Interacting geometric
cofactor/radius data and finite-patch approximation certificates remain
open in §§6.3 and 6.6; noncircular contours are not covered by the disk theorem.
The concrete full-product theorem of §4.72 uses this spectral infrastructure;
analytic-product consequences have their own hypotheses.

### 6.3. P3 — Full spectral products and their exact zero divisors

**Verified analytic package**

- [x] Construct entire normalized paired products from positive levels
  with summable inverse squares; identify all zeros and their exact
  geometric spectral multiplicities, with fixed $c,d$, $d\ne0$
  (§§2.4, 4.49, 4.51). The prescribed line is part of the definition.
- [x] Transfer finite-sector response to indexed full-product zeros,
  including repeated levels and the positive-interaction coefficient
  $(R-E)/(R-v_0)$ (§§4.50–4.52, 4.59). The abstract theorem remains
  conditional on the selected baseline level being below $E$.
- [x] Certify separated zero windows under independently bounded operator
  errors, preserving total multiplicity with boundary exclusion
  (§§4.53–4.56), including empty windows and repeated levels.
- [x] Prove scalar truncation-error bounds, local cofactor-based location
  estimates and exact disk counts for analytic approximants
  (§§4.60–4.65). Rouché gives count $m$ under
  $\varepsilon<C\rho^m$; sufficiently long exact partial products qualify.
  The disk case includes zero-free disks and several or repeated zeros.
- [x] Supply the numerical onsite certificate and linear-growth tail rates
  of §§4.66–4.67: radius $1/4$, cofactor bound $1/5$, sufficient cutoff
  $16384$, truncation error $1/50$, additional boundary budget $1/100$,
  and zero distance at most $3/20$. The tail rates also hold for that
  linear onsite potential with symmetric nonnegative bounded interactions.

**Application-dependent work**

- [x] Instantiate the full-product theorem for the explicit graph of
  §6.4, with geometric summability and a nine-level zero-response
  conclusion derived in §§4.71–4.72.
- [ ] Derive numerical cofactor and isolation-radius certificates for
  this interacting geometric product. The linear onsite constants cannot
  be transferred unchanged to it.
- [ ] Extend counting to noncircular contours if an application needs
  them. This does not block §6.4. Finite-patch error certificates remain
  the separate task of §6.6.

### 6.4. P4 — A confined Ammann–Beenker model and a finite intervention

**Relationship to the two research tracks.** This section retains
the full original geometric and spectral-product objectives (Track A),
followed by the newer compact-mode control direction (Track B).
The L7 central control objective is now **verified** (§4.105): arbitrary normalized target preparation from dark up to an explicit global phase with zero leakage throughout. General complex full-space propagation, stronger control theorems, and the distinct L6 program remain open.
The earlier single-edge preparation narrative and its open tasks
remain here as the **preserved, deferred L6 program**; they are not
the present priority and are not already proved.

The application uses the **explicit centered octagonal cut-and-project
vertex graph** of §§4.68–4.70. The lattice projections, open-window
boundary convention and coordinate-step adjacency are defined in Lean.
The relation to the standard Ammann–Beenker construction is documented in
§4.68; a polygonal covering or aperiodicity theorem is not silently assumed.

**Completed geometric and spectral construction**

- [x] Define the accepted integer lifts, injective physical embedding and
  undirected unit-length coordinate edges. Prove infinitude by silver-unit
  inflation and finiteness within every bounded physical radius (§4.68).
- [x] Verify the central star with exactly eight unit-distance neighbors,
  degree at most eight everywhere, and the exact eight-color involutive
  matching representation, with no repeated nontrivial edges (§4.69).
- [x] Construct the full interaction and verify its coordinate formula,
  positivity, symmetry and norm at most one:
  ```math
  (H\psi)(x)=(1+|p(x)|^2)\psi(x)
    +\frac1{16}\sum_{y\sim x}(\psi(x)-\psi(y)).
  ```
- [x] Prove $V\ge1$, properness, finiteness of
  $S=\{x:|p(x)|\le2\}$ and $V\ge5$ outside it. Use the existing
  natural-domain, self-adjoint compact-resolvent construction to obtain
  the ordered full eigenbases (§4.70).
- [x] Prove that the nine central sites have onsite energy at most two;
  the variational comparison gives $\lambda_8(H)\le3$. Construct the
  spectra for $H_\tau=H+\tau P_S$, preserve the lower bound one, and prove
  ```math
  \frac\tau2\le\lambda_n(H_\tau)-\lambda_n(H)\le\tau,
  \qquad n<9,\quad 0\le\tau\le4.
  ```
  This counts multiplicities and supplies a genuinely nonempty window.

**Completed planar counting, summability and full-product application**

- [x] Prove an injective finite-residue planar code and the explicit
  bound $\#\{|p(x)|\le R\}\le25(2\lceil R+3\rceil+1)^2$ for $R\ge0$.
  This supplies the required planar growth bound without assuming or
  proving uniform separation (§4.71).
- [x] Prove $\sum_x(1+|p(x)|^2)^{-2}<\infty$ and transfer it to the
  positive complete interacting spectra throughout $0\le\tau\le4$,
  retaining the lower bound one (§§4.71–4.72).
- [x] Construct entire full products with exact operator-specific
  geometric zero orders and prove indexed displacements between
  $|d|\tau/2$ and $|d|\tau$ for nine slots on each reflected branch,
  including both interval endpoints (§4.72).

**Established ingredients for the next steps**

- [x] Strengthen the existing nine-level response to coefficient
  $4\sqrt2-5$ on $0\le\tau\le3+2\sqrt2$ using the next-shell barrier (§4.73).
- [x] Prove the two compact-state equations, orthogonality and exact
  ring-induced crossing on the infinite natural domain (§§4.74–4.75).
- [x] Prove the stationary state under a one-edge change and the exact
  Rayleigh response of the affected unit direction (§4.75).
- [x] Identify the radius-two sector as exactly the origin and the two
  compact rings; prove its internal adjacency, the ring degrees three and
  four, and the exact count of sixteen edges to the exterior (§4.76).
- [x] Validate the central-block kernel classification and its transfer
  to centrally supported natural-domain eigenvectors (§4.77).
- [x] Derive central support for every crossing eigenvector and prove
  that its two seed amplitudes parametrize the entire natural-domain
  eigenspace, of real dimension exactly two (§4.78).
- [x] Certify the closed real spectral isolation window
  $|E-E_*|\le1/128$ around the exact multiplicity-two crossing, with no
  other point of the full real bounded-inverse spectrum (§4.79).
  This is a conservative bound, not the exact nearest-level spacing.

**Near-term result: quantitative dark/bright spectral splitting (L1–L5 verified)**

The real natural-domain splitting progressed from eigenpair
existence (L2c) to unique simple levels in an isolated window
(L2d), then a full-exterior eigenvector estimate (L3),
a quadratic energy law with constant `112` (L4),
and finally a **strict signed shift** and a single
consolidated full-operator theorem (L5). The remaining
questions concern scientific assessment and separate
dynamical, geometric, and analytic-product research goals.
See the [research roadmap](docs/bright-spectral-splitting-roadmap.md).

- [x] **L1 — Dark simplicity (Lean verified).** For ε ≠ 0 the
  perturbed eigenspace at E_* is exactly the dark line.

- [x] **L2a — Ordered complete eigenbases and norm stability.**
  The true infinite-operator levels obey
  |μₙ − λₙ| ≤ 2|ε| for every index.
- [x] **L2b — Exactly double, consecutive unperturbed crossing.**
  The counting theorem, consecutive-slot lemma and concrete corollary
  establish the exact multiplicity and consecutive positions.
- [x] **L2c — Actual distinct perturbed eigenvalue exists.**
  For every ε ≠ 0 there is a nonzero natural-domain eigenvector
  with energy E_b ≠ E_* and |E_b − E_*| ≤ 2|ε|.
- [x] **L2d — Isolated simple point-spectrum pair.**
  For `0 < |ε| ≤ 1/1024`, the closed `1/256` window contains
  exactly the simple dark energy and one distinct simple moving
  eigenvalue, with `|E_b-E_*| ≤ 2|ε|` (§4.94). This is a
  statement about all genuine natural-domain eigenvectors,
  not an unproved claim about an alternate spectrum definition.
- [x] **L3 — Quantitative bright eigenvector (§4.95).**
  The true moving eigenspace is dark-orthogonal, has a
  nonzero bright amplitude `c`, and satisfies the exact
  full-exterior estimate `‖Qx‖≤256|ε||c|‖QWF‖`
  for `0<|ε|≤1/1024`.
- [x] **L4 — True bright energy law (§4.96).**
  The full-graph bright amplitude identity, exact exterior
  coupling and sharp L3 estimate prove
  `|E_b(ε) − (E_* + ε/4)| ≤ 112 ε²` for
  `0 < |ε| ≤ 1/1024`, for the genuine moving
  natural-domain eigenvalue.
- [x] **L5 — Signed shift and consolidated theorem (§4.97).**
  The true moving eigenvalue shifts upward for positive ε
  and downward for negative ε. A single theorem packages
  the natural-domain eigenpair, the two simple eigenspaces,
  the point-spectrum window count, the `112ε²` quadratic
  energy law and the bright/exterior leakage estimate.
  The selected theorem is Lean- and Comparator-verified; independent
  scientific assessment remains separate.

**Verified L7 objective — exact zero-leakage two-mode preparation**

L7a uses the eight-edge *coordinated local perturbation* `M`. The following
static, algebraic and switched dynamical results are Lean-verified in §§4.99–4.105.

- [x] Construct eight genuine, distinct, mutually disjoint adjacent pairs.
- [x] Define the bounded symmetric finite sum and certify matching amplitudes.
- [x] Prove `M D=0` and `M F=2F`, with `M a=a-b` and `M b=b-a`.
- [x] Establish `Q M P=0` and natural-domain invariance under both controls.
- [x] **L7b (first part):** derive the exact dark/bright matrix, its Pauli
  decomposition and the three complex generator commutators.
- [x] **L7b (completion):** prove full real su(2) generation and constructive
  three-rotation reachability from dark for every normalized complex pair,
  with independent signed real generator coefficients.
- [x] **L7c.1:** exact single-axis real/imaginary Schrödinger trajectories,
  conserved norm, natural-domain lifts and zero leakage at every time;
  full real self-adjointness for both controls together.
- [x] **L7c.2:** identify the single-axis trajectories with Euler rotations
  including the common scalar phases, and certify identity at zero time
  and compatibility with matrix multiplication.
- [x] **L7c.3:** compose the three pulses with matching endpoint states,
  continuous full-space components, natural-domain membership, exact
  piecewise Schrödinger equations, norm conservation and zero leakage at
  every time, including the switches.
- [x] **L7c.4:** prove arbitrary normalized target preparation from dark up
  to the explicit global phase with `‖Qψ(t)‖=0` at every time, continuous
  natural-domain trajectories and full piecewise Schrödinger equations.
- [ ] Construct a general full complex Hilbert-space unitary propagator.

Static invariance and Lie generation alone would not suffice for a
preparation theorem; the explicit natural-domain trajectories and endpoint
proof now supply it. See the [verified L7 and preserved L6 roadmap](docs/bright-spectral-splitting-roadmap.md#6-l7--exact-two-mode-preparation-without-leakage-verified).

**Deferred original research direction: L6 — single-edge approximate control (PRESERVED, OPEN)**

The original two-control plan remains a separate future target:
use only the single selected inter-ring edge `W` and the
eight-site parameter `t`, while proving an explicit small-leakage
and reachability budget for general complex Schrödinger dynamics.
Because `‖QWF‖²=7/16`, this one-edge correction does not preserve
the original dark–bright plane exactly. Verified conditional
uniform leakage estimates and static control identities remain
useful ingredients; no complete L6 target-state theorem is claimed.
The following original research narrative and
[edge-control note](docs/edge-control-reachability.md) are retained
for later investigation. Its original compact-mode discussion uses the
`a/b` basis; in the `D/F` basis, detuning `t` does mix dark and bright.

The eight-site parameter `t` already gives a simple, exact energy response:
moving `t` away from `t_*` shifts one compact mode's energy and leaves the
other unchanged. Under a time-dependent quantum interpretation, this could
change the relative phase of a **pre-existing** coherent superposition; the
phase difference would remain after returning to `t_*`. Because the same two
modes remain eigenvectors for every `t`, changing `t` alone cannot create
the missing mode amplitude when starting in only one mode. Quantum time
evolution and phase control are not yet formalized in this real Lean model.

A change to the weight of the single edge between the two rings is a more
promising candidate for mixing the amplitudes. The original code already
proves that one combination remains an exact eigenstate after this edge
change, and that the complementary direction has an exact energy
expectation. The [edge-control research note](docs/edge-control-reachability.md)
explains the nonzero coupling and a further constraint: in unitary dynamics
with only this edge varied, the common eigenstate's occupation is conserved.
Thus an edge-only pulse cannot reach every superposition from a single
initial mode. Two new Lean modules
[`AmmannBeenkerEdgeControl.lean`](SpectralGeometry/AmmannBeenkerEdgeControl.lean)
and
[`AmmannBeenkerTwoControlAlgebra.lean`](SpectralGeometry/AmmannBeenkerTwoControlAlgebra.lean)
build directly on the crossing equations, adding the exact coupling,
the normalized dark eigenstate and the response to detuning (§4.80).
Their exact operator identities have passed the full Lean build; the
dynamic single-edge no-go theorem and the L6 preparation protocol remain open. The separate coordinated L7 preparation protocol is now proved in §4.105.
Sections 4.81–4.91 now add an exact qubit/leakage decomposition,
the reduced-gap and exact-edge norm, quantitative **conditional**
time-uniform bounds for a selected-edge pulse and subsequent
free evolution, real pulse-Hamiltonian self-adjointness, and
one exact dark-state Schrödinger trajectory and the exact bright
forcing identity with external feedback. What remains
open is construction of the general **complex** unitary
propagator and a quantitative **target-state preparation**
theorem, not the conditional pulse-error bounds themselves.

- [x] **Finish the quantitative bright spectral splitting (§4.97).**
  The genuine moving level exists (L2c), is uniquely
  simple within the isolated window (L2d), has certified
  bright/exterior eigenvector control (L3), satisfies
  the `112ε²` energy law (L4), and has a signed
  shift and consolidated full-domain theorem (L5).
  The compressed energy expectation alone is not the theorem.
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
  See [the research note](docs/edge-control-reachability.md) for the
  proposed protocol and its limitations.
- [x] **Certify full real-space qubit/leakage and conditional ON/OFF
  pulse bounds (§§4.81–4.88).** The orthogonal decomposition,
  certified gap and edge norm, exact-domain real self-adjointness,
  residual-conservation implications and duration-uniform
  `512|ε|` leakage estimate (under the explicit evolution
  hypotheses) have all passed Lean CI.
- [x] **Verify one exact complex-phase Schrödinger trajectory (§4.89).**
  The normalized dark mode has a real/imaginary solution of the
  coupled Schrödinger equations with norm one and zero leakage
  at every time for any real strength of the selected edge.
  This is **one solution**, not a constructed complex
  propagator on the full space.
- [x] **Verify the bright-amplitude forcing bridge (§4.91).**
  The fourteen bright generator declarations are Lean-verified. The exact
  forcing term and bound are static, full-infinite-graph identities, not
  integrated dynamical control.
- [x] **Verify the existing static dark/bright identities (§4.92).**
  The established combined theorem and source dependencies passed full Lean
  and independent statement checks.
  Those identities by themselves do not assert a moving level;
  that **later existence theorem** is independently proved in §4.93.
- [ ] **General complex dynamics and L6 controlled A/B preparation (open).** Build the genuine complex-Hilbert-space
  unitary evolution with natural-domain invariance and generator
  commutation, apply the proved leakage bounds to it, and then
  certify nontrivial bright-mode mixing, target amplitudes,
  relative phase and reachability limitations.

This is intended as a self-contained result with a possible physical
interpretation, **not** a claim that a laboratory implementation exists.
The spectral-product program below remains the project's long-term goal.
The existing dark/bright results (§§4.80–4.92) provide
certified algebraic inputs. The complete spectral analysis
in §§4.93–4.97 now additionally proves **genuine isolated,
signed and quantitatively controlled spectral splitting**
on the infinite graph. Coherent-control and state-preparation
questions are separate downstream goals. The immutable first
Palomar registration remains unchanged.

**Remaining tasks for the original spectral-product program**

- [ ] Derive an isolation radius and a nonzero analytic-cofactor lower
  certificate for a specified geometric spectral level or cluster.
  Account for multiplicity; do not assume simple spectrum.
- [ ] Combine these data with a quantitative spectral-tail bound to
  certify a finite-product cutoff and exact disk zero count (§6.3).
  The onsite constants of §4.67 do not automatically apply here.
- [ ] Prove a uniform vertex-separation estimate if needed for sharper
  geometric estimates; it is not a prerequisite for the established
  summability and full-product application.

**Further geometric and research questions**

- [ ] Formalize global rotational symmetry, polygonal tiling coverage and
  aperiodicity when these properties are part of a claimed application.
  The present spectral theorem is about the explicitly defined graph.
- [ ] Compare the proved multiplicity-two classification of §4.78 with
  the compact-state literature and obtain an expert assessment (§6.8).

The radius-two intervention gives the nine-level full-product response
of §4.72. The first-ring intervention gives the exact crossing
eigenspace (§4.78) and real spectral gap (§4.79). L1–L5 now also
certify the distinct moving level, isolated signed splitting and
quantitative bright geometry (§§4.93–4.97); these do **not** certify
quantum state preparation. L7a now proves exact invariance of the original
plane under both coordinated controls, and L7b establishes the effective
matrix, full Lie generation and constructive Euler state reachability
(§§4.99–4.101). The verified L7c.1 single-axis trajectories (§4.102) solve the full
natural-domain Schrödinger equations with exact zero leakage. L7c.2 identifies them with the exact phase-weighted rotations (§4.103).
L7c.3 proves their continuous three-pulse composition with exact zero
leakage (§4.104). L7c.4 proves the arbitrary-target endpoint theorem
from dark for this verified trajectory (§4.105).
The one-edge, small-leakage preparation route remains open, and the
spectral-product and relative-determinant objectives are unchanged.

### 6.5. Local geometric defects and relative spectral products

**Target theorem: an exact finite determinant for the relative product**

For a verified finite-support perturbation
$H'=H+\iota_S K\iota_S^*$, establish the identity of §2.3:
```math
\frac{F_{H'}(z)}{F_H(z)}
=\frac{\det(I+K G_S(z))\det(I+K G_S(-z))}
       {\det(I+K G_S(0))^2}.
```

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

Finite-rank perturbation determinants are established operator theory, including
in work on infinite graphs; see
[Golinskii](https://doi.org/10.1080/03081087.2016.1155529).
The research contribution must be identified through a precise geometric
application or quantitative result beyond a relabeling of that theory.

### 6.6. Certified finite-patch approximation and zero response

A finite Green matrix still contains information about the infinite system.
This phase provides the missing approximation certificate.

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

The intended result is a quantitative statement about the response of an
infinite system that can be assessed using finite data with a proved error.

### 6.7. Exploratory objectives: zero statistics and structural constraints

**Local statistics on the fixed line**

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

**Separate long-term question: a line determined by structure**

- [ ] Define an analytically meaningful object from an independently
  specified geometric construction without encoding a desired zero line
  in its factors or an affine coordinate. Investigate whether a proved
  structural mechanism then forces its zeros onto a line.

This last question is distinct from the program using the prescribed line
$c+d\mathbb R$. It is exploratory, not a prerequisite for the response
theorem, and carries no asserted connection to the Riemann zeta function.

### 6.8. Independent statement verification and research-interest assessment

**Historical first registration — preserved.** The 2026 Palomar
record `PALOMAR-2026-11-06-000012` selected
`crossingEigenspace_finrank` and
`crossing_eigenvector_representation`, plus three
necessary model witnesses (§4.78). It proved the full
infinite-operator crossing eigenspace was exactly
two-dimensional. Neither this record nor its registration
is being replaced.

**Earlier, unsubmitted candidate (§4.92).** The former
generator-response candidate `crossingOneEdgeDarkBrightResponse`
and its dedicated
[`palomar/dark-bright/comparator.json`](palomar/dark-bright/comparator.json)
are kept as an archive, with exact snapshots of its original
Challenge and Solution. It has **not** been claimed as
a separate registered Palomar theorem.

**L5 selection and editorial history (§4.98).** The preserved L5
Challenge and Solution select
`crossing_final_signed_bright_spectral_splitting`, with six
necessary concrete-model witnesses. Its theorem-specific
[Comparator](palomar/signed-bright-splitting/comparator.json)
is preserved; the earlier unsubmitted generator-response candidate
remains archived under `palomar/dark-bright/`.

- [x] Preserve the original registered theorem, source proof
  and archived candidate without rewriting their history.
- [x] Complete the original L5 independent Challenge/Solution
  package and verification.
- [x] Submit the original L5 package; mechanical and renderability checks
  passed, while the automated editorial review requested an explicit
  existence statement for the fixed dark eigenstate.
- [x] Strengthen the selected theorem and independent Challenge with
  `crossingDark ≠ 0` and the full fixed-dark eigenvector equation;
  verify the corrected package with full Lean and Comparator.
- [x] Record the separate L5 registration
  [PALOMAR-2026-11-23-000017 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-23-000017&version=1) on 23 November 2026 (§4.98).

**Third registration (§4.105).** The Lean-verified exact preparation theorem is selected with its concrete graph witnesses and local-edge certificates. The [independent package](palomar/exact-leakage-free-preparation/) passed full Lean and independent Comparator verification, Palomar mechanical verification and renderability checks. The automated editorial review identified no blocking problem. The result was registered on 25 November 2026 as [PALOMAR-2026-11-25-000001 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-25-000001&version=1).

**Registration boundary.** The historical first registration
`PALOMAR-2026-11-06-000012` remains unchanged.
Successful Lean checks and a successful Comparator alone are **not** Palomar registration. The separate registry record [PALOMAR-2026-11-23-000017 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-23-000017&version=1) subsequently registered L5 on 23 November 2026.

**Potential research interest, without a priority claim.** The compact
A/B patterns are known in quasicrystal tight-binding research
([Oktel 2021](https://doi.org/10.1103/PhysRevB.104.014204)).
Protected combinations and local rank-one perturbations are not novel
mathematical primitives. What may merit further examination is the **full infinite-system
spectral statement**: a protected simple dark eigenstate, a second
unique simple nearby energy whose shift sign and quadratic
remainder are proved, and a moving eigenvector with quantified
external coupling. These statements avoid the unjustified
assumption that the two original localized states form an
exactly invariant closed two-level system.

The clearest possible **mathematical interest** is the
fully infinite-operator conclusion: a protected simple eigenstate,
a distinct simple moving level with a signed and quantitatively
controlled energy shift, and a bound on the moving eigenvector's
coupling to the exterior. For **theoretical condensed-matter and
wave-network researchers**, the contrast between exact first-ring
detuning and a single connecting-edge change provides a concrete
example of localized states, protected dark combinations and
bright-state response. The time-uniform ON/OFF pulse bounds may
motivate further analysis but remain conditional on the supplied
evolution. The [scientific-audience overview](#scientific-audience-and-possible-relevance)
explains these connections and their limitations.

These possible readerships and the originality of the results have
not been independently assessed. The coordinated L7 result adds exact
normalized target preparation from dark with zero leakage on the full
infinite graph (§4.105), in contrast to the conditional single-edge pulse
bounds. No general complex full-space propagator, arbitrary-initial-state
preparation theorem or experimental realization is claimed.

- [ ] Compare the precise new theorem against the specialist
  literature and obtain independent expert assessment of interest
  and novelty independently of registry verification.
- [ ] Continue the separate scalar cofactor and finite-patch
  certificates required in §§6.3, 6.5 and 6.6.

**Maintenance rules:** append each new verified result to §4 and to the
roadmap **without deleting earlier results or historical registrations**;
update the canonical §5 module list whenever source imports change;
update the **table of contents** whenever sections are added, renamed
or reorganized; and review the entire README for **obsolete statements**,
revising old status sentences and open-problem descriptions when later
theorems resolve them without erasing their historical context.
For Palomar, preserve a separate Comparator inside each
`palomar/<candidate>/` directory, preserve predecessor packages,
and never place a redundant Comparator at the repository root.

Keep the **entire README scientific, cumulative and readable in plain English**.
Explain each result's mathematical meaning, assumptions, exact conclusions,
limitations and relationship to earlier theorems. Retain formulas and Lean
declaration names where useful, but explain them in accessible language.
Do not include commit hashes, pull request references, numbered CI runs,
build logs, failed proof attempts or operational development chronology
in the README. Such provenance belongs in the repository history and CI
records, or in separate technical notes when needed. Keep existing Palomar
registry identifiers and links, because they identify independently
registered mathematical statements. Report verification status and scope
without operational identifiers. Never mark a result as verified before
the required checks have succeeded, and distinguish full Lean verification
from independent comparison of the selected Palomar statements.