[← Main README and table of contents](../README.md)

### 4.113. Exact finite-pattern recurrence and separation

**Plain-English result.** A finite set of lattice coordinates, including sites
that are excluded by the octagonal acceptance window, can be translated
arbitrarily far in physical space while preserving every admission decision.
For any prescribed finite number of copies and any nonnegative separation,
the centers can be chosen mutually separated and the complete translated
finite lift sets can be made disjoint. These are exact statements for the
implemented infinite graph, not finite sample observations.

**Arithmetic mechanism.** Write alpha = sqrt(2)/2. The silver-unit inflation
sequence has physical norm (1+2 alpha)^k and internal displacement
(1−2 alpha)^k on the real axis. The first tends to infinity and the second
tends to zero. No integer lift lies on any of the eight supporting lines
of the exact open window: the axis thresholds contradict integer parity,
and the diagonal thresholds contradict the even irrational coefficient.
For each lift, the nonzero margins to the thresholds ensure eventual
preservation of admission and exclusion. A finite induction supplies a
single threshold for the whole finite set.

**Multiple copies.** Given an already selected finite set S of recurring
centers, a new center can be chosen beyond
max(R,0)+D+sum of the physical norms of the centers in S. The triangle
inequality gives separation greater than D from every previous center.
Induction gives any finite cardinality, including zero. If every lift in
the original pattern has physical norm at most r, centers separated by
more than 2r give disjoint translated lift sets. Taking r as the sum of
the original lift norms yields an explicit sufficient separation and
covers excluded as well as admitted coordinates.

**Verified Lean declarations.** In
[`AmmannBeenkerPatchRecurrence.lean`](../SpectralGeometry/AmmannBeenkerPatchRecurrence.lean):

- `internal_window_boundary_avoided`: exact avoidance of every supporting line.
- `internal_inflatedOriginNeighbor`, `recurrence_internal_tendsto_zero`:
  explicit contracting internal displacement and convergence.
- `eventual_admitted_translate`, `eventual_finite_pattern_translate`:
  eventual preservation of a single decision and of a finite pattern.
- `recurrence_physical_norm_tendsto_atTop`, `finite_pattern_recurrence`:
  divergence and arbitrary remote recurrence.
- `finite_pattern_recurrence_family`, `separated_translated_lifts`,
  `finite_pattern_disjoint_copies`: arbitrarily many recurring centers
  and disjoint translated lift sets.

**Status and limits.** These ten public theorems have passed the complete
Lean/Mathlib build. Three of them (`internal_window_boundary_avoided`,
`finite_pattern_recurrence`, and `finite_pattern_disjoint_copies`) are selected
in the seventh registered package and have passed independent comparison.
The concrete candidate neighborhoods and complete graph-neighbor
correspondence are now verified as described below. Full-graph transfer of the compact eigenvector equations is now also
verified as described below. This does not give an isolated remote double
eigenvalue or a multi-pair control theorem. General cut-and-project recurrence is not
claimed as a new discovery; the concrete replicated spectral statement
is now proved in L9.2.

**Verified concrete neighborhood transfer.** In
[`AmmannBeenkerPatchNeighborhood.lean`](../SpectralGeometry/AmmannBeenkerPatchNeighborhood.lean),
`patchNeighborhoodLifts F` includes F and every signed unit-coordinate
candidate, admitted or excluded. The concrete `centralRecurrenceLifts`
applies this enlargement twice to the seventeen central lifts. The
theorem `translated_neighbors_exact` identifies the complete translated
neighbor set, not merely edges between already selected vertices.
`central_recurrence_neighbors_exact` specializes this to the central
patch and all of its immediate neighbors, while
`central_recurrence_disjoint_copies` gives arbitrary finite disjoint copies
of the entire two-step pattern. These statements passed full Lean/Mathlib
verification. Both `central_recurrence_neighbors_exact` and
`central_recurrence_disjoint_copies` passed independent comparison in the seventh registered package.

**Verified full-graph spectral transfer.** The module
[`AmmannBeenkerTranslatedModes.lean`](../SpectralGeometry/AmmannBeenkerTranslatedModes.lean)
defines a finite state translation as a sum of site vectors with the
original amplitudes at the translated coordinates. It proves that the
amplitudes agree at admitted translated sites and vanish elsewhere.
Using the exact neighbor correspondence and the full coordinate formula
for the Laplacian, `central_translate_eigenvector` transports every
eigenvector supported on the central sector. The proof also covers
exterior vertices neighboring the support (where cancellation matters)
and all other vertices (where the translated amplitudes and their
neighbor amplitudes vanish). There is no assumption of a global graph
automorphism or preservation of matching colors.
The concrete `translatedCompactA_eigenvector` and
`translatedCompactB_eigenvector` prove the eigenvector equations with
coefficients 3/16 and 1/4 on the entire infinite graph.
Full Lean/Mathlib verification passed, and the three eigenvector transfer statements
(`central_translate_eigenvector`, `translatedCompactA_eigenvector`, and
`translatedCompactB_eigenvector`) passed independent comparison in the seventh registered package.
The exact normalization and mutual orthogonality of the replicated family are also verified.


**Verified finite families.** In [`AmmannBeenkerReplicatedPairs.lean`](../SpectralGeometry/AmmannBeenkerReplicatedPairs.lean),
`translateFiniteState_inner` proves preservation of the inner product on admitted finite patterns;
`translateFiniteState_inner_of_disjoint` gives orthogonality of disjoint translated lift sets.
`translatedCompact_inner_products` proves both squared norms are 8 and their inner product is zero.
`central_translate_support` locates all nonzero amplitudes in the translated central lift set.
The bundled theorem `exact_recurrent_compact_mode_pairs` proves for any finite N, real R and D >= 0 the existence of N centers beyond R, separated by more than D, with complete disjoint candidate patterns, exact eigenvalues 3/16 and 1/4, squared norms 8 and all cross-pair inner products zero. Thus 2N nonzero mutually orthogonal compact eigenvectors exist on the same infinite graph. No finite boundary or global graph automorphism is assumed.

The principal theorem, `translatedCompact_inner_products` and `central_translate_support` are included in the independent selection; the supporting inner-product lemmas are verified in the full library.

The 129-module library is Lean-verified. All 16 selected propositions passed independent comparison with the Lean default, NanoDa and con-ron kernels; the seventh result is registered as [PALOMAR-2026-11-27-000067 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-27-000067&version=1). L9.2 is mathematically complete. The subsequent natural nondegenerate plateau results are now Lean-verified through bounded dynamics and finite-time stability; see [§§4.114–4.118](natural-plateau-architecture.md). The engineered distinct degenerate energies remain an alternative; see the [L9 roadmap](multi-qubit-roadmap.md).

**Scientific context.** General cut-and-project repetitivity is established (see [A characterisation of linear repetitivity for cut and project sets with general polytopal windows](https://doi.org/10.1016/j.indag.2024.03.003)). [M. Ö. Oktel, Phys. Rev. B 104, 014204 (2021)](https://doi.org/10.1103/PhysRevB.104.014204) studies compact localized patterns in the octagonal lattice in a tight-binding zero-energy model, not the present weighted Laplacian. The contribution here is the exact concrete certificate of recurrence, complete-neighbor transfer, full-graph spectral cancellation and disjoint orthogonal replication. No priority claim is made.

See the [executive summary and schematic](../README.md#exact-spatial-replication-of-compact-localized-eigenstates) for a plain-English explanation of the theorem.


**L9.3 progress — natural plateau transfer (Lean-verified).** The module [AmmannBeenkerNaturalPlateauPairs.lean](../SpectralGeometry/AmmannBeenkerNaturalPlateauPairs.lean) proves that the canonical central defect vanishes on exterior-supported states, and that the actual Hamiltonian agrees with the uniform bulk on such states. Any translated central support with center at norm greater than four is disjoint from the central defect. The bundled theorem `exact_recurrent_natural_plateau_pairs` gives arbitrary finite families on the actual canonical plateau, with exact energies C+3/16 and C+1/4, separation 1/16, and the same complete neighborhood disjointness and inner products as the seventh result. The full 130-module build passed, as did comparison of the existing 16 selected propositions. At that milestone the new L9.3 statements had not yet been selected; the later eighth-candidate selection has passed independent comparison (see [candidate](natural-plateau-palomar.md)). Local completeness and the obstruction to individual spectral isolation from identical-energy replicas are proved in the subsequent modules.


**L9.3 progress — original-cell completeness (Lean-verified).** [AmmannBeenkerNaturalCellCompleteness.lean](../SpectralGeometry/AmmannBeenkerNaturalCellCompleteness.lean) proves the eight exterior witness equations from the actual graph, retaining the full degrees of the seventeen central sites. The zero exterior amplitudes force alternating B-ring coordinates; the interior equations imply zero central amplitude and alternating A-ring coordinates. If a and b are the corresponding coefficients and c is a real Laplacian eigenvalue, then (3−16c)a=0 and (4−16c)b=0. The theorem `naturalCell_supported_eigenvector_classification` proves every nonzero full-graph eigenvector supported in the original cell is a nonzero scalar multiple of A at 3/16 or B at 1/4. This excludes additional eigenvector directions at any real energy for this support, but says nothing about larger supports or the full eigenspaces. The 131-module Lean build and existing Comparator passed. The remote transfer module has also passed verification.


**L9.3 progress — exact remote plateau completeness (Lean-verified).** The module [AmmannBeenkerNaturalRemoteCompleteness.lean](../SpectralGeometry/AmmannBeenkerNaturalRemoteCompleteness.lean) defines the translated seventeen-site cell, proves it has exactly seventeen vertices and is disjoint from the central defect when the center norm exceeds four, and constructs a supported preimage of every remote-supported state. The reverse transfer of the full Laplacian equation includes the exterior neighbors. The theorem `naturalRemoteCell_plateau_classification` proves that every nonzero eigenvector of the actual canonical plateau supported within any such recurrent cell is a nonzero multiple of A at C+3/16 or B at C+1/4. Together with the verified orthogonal nonzero modes, this identifies exactly two local eigenvector directions and one direction at each energy; it does not assert full-graph simplicity or exclude larger supported states. All 132 modules passed full Lean checking and the previous 16 Comparator propositions passed. No new independent statement selection or registration is claimed. The subsequent L9.4 results establish infinite multiplicity and an individual isolation obstruction; collective gaps remain open.


**L9.4 progress — infinite global multiplicity (Lean-verified).** The module [AmmannBeenkerNaturalMultiplicity.lean](../SpectralGeometry/AmmannBeenkerNaturalMultiplicity.lean) proves that arbitrary finite orthogonal eigenfamilies of squared norm eight contradict finite-dimensionality of the full eigenspace. Applying this to the verified recurrent modes yields `canonicalPlateau_natural_eigenspaces_infinite` for both energies of the actual canonical Hamiltonian and `plateauBulk_natural_eigenspaces_infinite` for every constant height C, including zero. This does not decide whether the two spectral points are isolated from other energies. The full 133-module Lean build passed, and the 16 previously selected propositions passed independent comparison. At that milestone the new statements were not yet selected; the later eighth-candidate selection has passed independent comparison. The explicit equal-energy orthogonal-partner obstruction has passed verification.


**L9.4 progress — individual isolation obstruction (Lean-verified).** [AmmannBeenkerNaturalIsolationObstruction.lean](../SpectralGeometry/AmmannBeenkerNaturalIsolationObstruction.lean) extends any prescribed recurring center by a recurrent cell beyond an arbitrary radius and distance with disjoint complete candidate patterns. Both natural energies admit nonzero eigenvectors orthogonal to both original directions. The theorem `naturalPlateauPair_no_individual_residual_gap` excludes every strictly positive residual lower bound on that plane's entire orthogonal complement, at either energy. The full 134-module build and previous 16 Comparator propositions passed. This is not a statement about isolation from distinct spectral energies after removing the entire corresponding eigenspace. The uniform spectral shift and collective residual upper bound have passed verification.


**L9.4 progress — uniform shift and collective residual upper bound (Lean-verified).** [AmmannBeenkerNaturalCollectiveSpectrum.lean](../SpectralGeometry/AmmannBeenkerNaturalCollectiveSpectrum.lean) proves exact equality of the bounded residuals of C I + L at C+e and L at e, the corresponding real-spectrum membership equivalence, and equivalence of collective residual bounds on the orthogonal complement of the entire eigenspace. Distinct-energy eigenvectors of a self-adjoint operator are orthogonal; applying this to the other natural level bounds any collective residual lower bound for either canonical natural energy by 1/16. The full 135-module Lean build and previous 16 Comparator propositions passed. No positive collective gap or accumulation result is established. The finite-defect comparison of eigenspace dimensions at bulk resolvent energies has passed Lean verification. A uniform onsite shift should not be confused with a change from the graph Laplacian to a pure adjacency Hamiltonian; the latter is a distinct prospective research direction.


**L9.4 progress — finite-defect dimension bound (Lean-verified).** [AmmannBeenkerNaturalDefectComparison.lean](../SpectralGeometry/AmmannBeenkerNaturalDefectComparison.lean) proves that at any real energy outside the uniform bulk spectrum, application of the central defect is injective on the canonical plateau eigenspace. Its dimension is bounded by the defect rank, hence by seventeen. Consequently any infinite-dimensional canonical plateau eigenspace occurs at a bulk spectral energy. The full 136-module Lean build and previous 16 Comparator propositions passed. Collective gaps and essential-spectrum equality remain unresolved; the subsequent L9.5 local addressing results do not assume either. The translated onsite and matched-edge controls and full-space driven action have passed verification.


**L9.5 progress — exact remote controls (Lean-verified).** [AmmannBeenkerNaturalRemoteControls.lean](../SpectralGeometry/AmmannBeenkerNaturalRemoteControls.lean) proves that the translated eight pairs are actual edges with disjoint endpoints, transports their rank-one Laplacian corrections by finite-state translation, and verifies the onsite projection on both compact modes. The full-space driven matrix has diagonal entries E_A+δ+η and E_B+η and equal off-diagonal entries −η. Thus the plane is invariant for arbitrary real strengths without assuming a positive collective gap. The 137-module Lean build and previous 16 Comparator propositions passed. The finite-family selectivity and reducing-complement module passed Lean verification. Time-dependent evolution, exact preparation and finite-time stability are established in the subsequent L9.6–L9.7 modules; long-time robustness remains open.


**L9.5 progress — spatial selectivity (Lean-verified).** [AmmannBeenkerNaturalControlSelectivity.lean](../SpectralGeometry/AmmannBeenkerNaturalControlSelectivity.lean) proves that the onsite and edge controls annihilate all states vanishing on the controlled cell. For finite families of disjoint recurring cells, independently signed simultaneous controls give exactly the local driven action on each selected plane and the unchanged central crossing action. The full operator is self-adjoint and each selected plane and the central plane have invariant orthogonal complements. The 138-module Lean build and previous 16 Comparator propositions passed. Sharp local norms and the exact compensation δ=1/16+d of the natural splitting passed Lean verification. This compensation is a control during a pulse, not a static well; it does not establish arbitrarily weak preparation or any collective gap.


**L9.5 progress — sharp norms and compensated drift (Lean-verified).** [AmmannBeenkerNaturalControlNorms.lean](../SpectralGeometry/AmmannBeenkerNaturalControlNorms.lean) certifies M²=2M, the exact operator norms of R and M (1 and 2), and the bound |δ|+2|η| on their combined perturbation. Detuning δ=1/16+d recovers the old degenerate matrix structure at the new common energy C+1/4. The full 139-module Lean build and previous 16 Comparator propositions passed. The subsequent L9.6 modules establish free and driven complex coefficient trajectories through the actual bounded Hamiltonian, with normalized remote dark/bright vectors, and exact arbitrary target preparation from dark. Arbitrarily weak control remains open.


**L9.6 progress — free and driven pair dynamics (Lean-verified).** [AmmannBeenkerNaturalPairDynamics.lean](../SpectralGeometry/AmmannBeenkerNaturalPairDynamics.lean) proves the actual bounded-Hamiltonian Schroedinger equations in the real/imaginary representation for free evolution, pure detuning and compensated matching pulses. It verifies the normalization of the remote dark/bright basis, norm conservation, exterior zero amplitudes and the relative free phase at angular frequency 1/16. The 140-module build and previous 16 Comparator propositions passed. The continuous compensated three-pulse composition passed Lean verification; its physical energy is C+1/4 and the controls are (1/16,p), (1/16−2t,0), (1/16,q) on successive unit intervals. The clamped trajectory is not asserted to satisfy the free equation before or after the protocol; the subsequent modules establish target reachability and finite-time stability; arbitrary weakness and long-time robustness remain separate tasks.


**L9.6 progress — continuous compensated pulse protocol (Lean-verified).** [AmmannBeenkerNaturalPulseComposition.lean](../SpectralGeometry/AmmannBeenkerNaturalPulseComposition.lean) certifies the continuous concatenation of three pulses on the remote normalized dark/bright basis, the preserved norm and zero exterior amplitudes at every time, including the switching instants, and the actual bounded-Hamiltonian differential equations on each open segment. The full 141-module build and previous 16 Comparator propositions passed. [AmmannBeenkerNaturalExactPreparation.lean](../SpectralGeometry/AmmannBeenkerNaturalExactPreparation.lean) implements the exact rotation matrices and their physical common phase, and bundles arbitrary normalized target preparation from the remote dark state with the previously proved trajectory properties. This module passed Lean verification. No claim of arbitrary weakness, collective spectral protection, or preparation from arbitrary initial data is made.


**L9.6 progress — arbitrary remote preparation (Lean-verified).** [AmmannBeenkerNaturalExactPreparation.lean](../SpectralGeometry/AmmannBeenkerNaturalExactPreparation.lean) proves exact preparation from the normalized remote dark direction to every normalized complex dark/bright pair, up to the explicit unit phase exp(i(-3(C+1/4)+t-p-q)), retaining the actual bounded-Hamiltonian equations, continuity, unit norm and zero exterior amplitudes. The 142-module build and previous 16 Comparator propositions passed. The new [AmmannBeenkerNaturalFamilyDynamics.lean](../SpectralGeometry/AmmannBeenkerNaturalFamilyDynamics.lean) module implements lifting of local solutions to the common finite-family Hamiltonian, exact free spectator evolution under arbitrary controls elsewhere and linear superposition of two trajectories. Full Lean verification passed. The subsequent bundled preparation results provide explicit schedules and norm accounting for the orthogonal direct sum, not a tensor-product construction. Arbitrarily weak preparation and collective spectral gaps remain open.


**L9.6 progress — common family dynamics (Lean-verified).** [AmmannBeenkerNaturalFamilyDynamics.lean](../SpectralGeometry/AmmannBeenkerNaturalFamilyDynamics.lean) verifies lifting of independent local equations to the same full Hamiltonian, exact free evolution of spectators with zero local controls, and addition of driven and spectator trajectories or two driven trajectories. The 143-module build and previous 16 Comparator propositions passed. The new [AmmannBeenkerNaturalTwoCellPreparation.lean](../SpectralGeometry/AmmannBeenkerNaturalTwoCellPreparation.lean) implements simultaneous preparation of two normalized local targets using the same three unit-duration intervals, with a normalized weighted direct sum (c²+d²=1), independent retained scalar phases, continuity, zero exterior amplitude outside the union and actual common-Hamiltonian equations. Full Lean verification passed. The phases are not asserted to be a single global phase of the combined state. This is not a tensor-product register or an entangling protocol.


**L9.6 progress — two-cell preparation (Lean-verified).** The full 144-module build and previous 16 Comparator propositions passed. [AmmannBeenkerNaturalTwoCellPreparation.lean](../SpectralGeometry/AmmannBeenkerNaturalTwoCellPreparation.lean) proves simultaneous normalized weighted preparation of two independently specified local targets, with distinct retained phases, the actual common-Hamiltonian equations and zero exterior amplitude. The finite-family extension in [AmmannBeenkerNaturalFinitePreparation.lean](../SpectralGeometry/AmmannBeenkerNaturalFinitePreparation.lean) uses arbitrary real weights c with sum of squares one and independent normalized local targets on a certified disjoint recurring family. The new module passed Lean verification. The three common unit-duration intervals are independent of the number of cells, not a bound on the total control resources. No tensor-product register, arbitrary weak preparation or collective gap is claimed.


**L9.6 progress — finite simultaneous preparation (Lean-verified).** [AmmannBeenkerNaturalFinitePreparation.lean](../SpectralGeometry/AmmannBeenkerNaturalFinitePreparation.lean) proves simultaneous local target preparation on arbitrary finite certified disjoint families, with the weighted norm one, zero exterior amplitudes, continuous trajectories and exact common-Hamiltonian equations on three unit-duration intervals. The 145-module build and previous 16 Comparator propositions passed. L9.7 begins with [AmmannBeenkerNaturalStorage.lean](../SpectralGeometry/AmmannBeenkerNaturalStorage.lean), implementing a continuous extension of preparation by free evolution, explicit physical phases and return up to a scalar phase after 32*pi, with norm and support preserved. Full Lean verification passed; ideal storage is not robustness to perturbations.


**L9.7 progress — ideal storage (Lean-verified).** The 146-module build and previous 16 Comparator propositions passed. [AmmannBeenkerNaturalStorage.lean](../SpectralGeometry/AmmannBeenkerNaturalStorage.lean) certifies the continuous switch from preparation to free evolution and return to the same local ray after 32*pi. [AmmannBeenkerNaturalDynamicalStability.lean](../SpectralGeometry/AmmannBeenkerNaturalDynamicalStability.lean) implements a first conservative finite-time squared state-distance bound 2*||P||*time for symmetric bounded errors, conditional on existence of the perturbed solution with the same initial state. The ideal storage solution is constructed explicitly. No collective gap or uniform-in-time protection is assumed. Full Lean verification passed; the subsequent quadratic stability and leakage modules sharpen this result.


**L9.7 progress — first dynamical stability bound (Lean-verified).** The 147-module build and previous 16 Comparator propositions passed. The conditional estimate 2*||P||*time in [AmmannBeenkerNaturalDynamicalStability.lean](../SpectralGeometry/AmmannBeenkerNaturalDynamicalStability.lean) requires no spectral isolation. [AmmannBeenkerNaturalQuadraticStability.lean](../SpectralGeometry/AmmannBeenkerNaturalQuadraticStability.lean) implements the stronger small-time squared distance estimate ||P||²*time² via the differential inequality for the full-state error and positive regularization of its square root. Full Lean verification passed. Existence is an explicit hypothesis of this intermediate theorem and is discharged for the constructed bounded evolution below; no time-uniform protection or collective gap is asserted.


**L9.7 progress — quadratic stability (Lean-verified).** The full 148-module build and previous 16 Comparator propositions passed. [AmmannBeenkerNaturalQuadraticStability.lean](../SpectralGeometry/AmmannBeenkerNaturalQuadraticStability.lean) certifies the conditional squared distance bound ||P||²*time² without spectral isolation. The new [AmmannBeenkerNaturalLeakage.lean](../SpectralGeometry/AmmannBeenkerNaturalLeakage.lean) implements the orthogonal remote dark/bright projection, its idempotence and nearest-plane identity, the exact total weight budget and the corresponding conditional quadratic off-plane leakage bound with retained weight at least 1-||P||²*time². Full Lean verification passed. Leakage includes noncompact-mode directions inside the cell, not only amplitudes outside its vertices. The subsequent bounded evolution constructs a perturbed solution; uniform-in-time protection and collective gaps remain open.


**L9.7 progress — full bounded evolution (Lean-verified).** The retained-weight proof in [AmmannBeenkerNaturalLeakage.lean](../SpectralGeometry/AmmannBeenkerNaturalLeakage.lean) uses the symmetry of the plateau Hamiltonian. [AmmannBeenkerNaturalBoundedEvolution.lean](../SpectralGeometry/AmmannBeenkerNaturalBoundedEvolution.lean) constructs the actual perturbed solution from the exponential of the bounded real block generator (r,i) -> (H i,-H r), on the full infinite product space. It implements the initial condition, derivative, full equations, norm conservation and leakage/retention bounds for this constructed solution. The full 150-module library passed Lean verification and the existing Comparator passed. At that milestone the new L9.3–L9.8 statements had not yet undergone independent comparison; the later eighth-candidate L9.3–L9.4 selection has passed, while L9.5–L9.8 remain outside that selection. No uniform spectral protection or collective gap is claimed. A thematic account of these developments, with theorem names and precise limitations, is available in [§§4.114–4.118](natural-plateau-architecture.md).
