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

The 129-module library is Lean-verified. All 16 selected propositions passed independent comparison with the Lean default, NanoDa and con-ron kernels; the seventh result is registered as [PALOMAR-2026-11-27-000067 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-27-000067&version=1). L9.2 is mathematically complete. The current L9.3 priority is to analyze the natural nondegenerate remote pairs on the existing plateau, including exact local completeness, followed by spectral environment and selective controls. The engineered distinct degenerate energies remain an alternative; see the [L9 roadmap](multi-qubit-roadmap.md).

**Scientific context.** General cut-and-project repetitivity is established (see [A characterisation of linear repetitivity for cut and project sets with general polytopal windows](https://doi.org/10.1016/j.indag.2024.03.003)). [M. Ö. Oktel, Phys. Rev. B 104, 014204 (2021)](https://doi.org/10.1103/PhysRevB.104.014204) studies compact localized patterns in the octagonal lattice in a tight-binding zero-energy model, not the present weighted Laplacian. The contribution here is the exact concrete certificate of recurrence, complete-neighbor transfer, full-graph spectral cancellation and disjoint orthogonal replication. No priority claim is made.

See the [executive summary and schematic](../README.md#exact-spatial-replication-of-compact-localized-eigenstates) for a plain-English explanation of the theorem.


**L9.3 progress — natural plateau transfer (Lean-verified).** The module [AmmannBeenkerNaturalPlateauPairs.lean](../SpectralGeometry/AmmannBeenkerNaturalPlateauPairs.lean) proves that the canonical central defect vanishes on exterior-supported states, and that the actual Hamiltonian agrees with the uniform bulk on such states. Any translated central support with center at norm greater than four is disjoint from the central defect. The bundled theorem `exact_recurrent_natural_plateau_pairs` gives arbitrary finite families on the actual canonical plateau, with exact energies C+3/16 and C+1/4, separation 1/16, and the same complete neighborhood disjointness and inner products as the seventh result. The full 130-module build passed, as did comparison of the existing 16 selected propositions. The new L9.3 statements have not yet been selected for independent comparison or registration. The local completeness question is being studied separately; individual spectral isolation from identical-energy replicas is impossible.
