[← Main README and table of contents](../README.md) · [L9 roadmap](multi-qubit-roadmap.md)

# 4. Infinite-dimensional geometric operators and spectral theory — §§4.114–4.118

**Verification status.** All 150 library modules, including the 21 natural-plateau modules following the registered 129-module baseline, have passed full Lean checking. The existing seventh-result Comparator selection of 16 propositions also passed. A new [eighth Palomar candidate](natural-plateau-palomar.md) selects the L9.3–L9.4 spectral results; all 22 selected propositions passed independent comparison and registration is pending. All seven registered results remain unchanged. Earlier development milestones are preserved in [§4.113](compact-patch-recurrence.md).

The model is the same fixed bounded canonical Hamiltonian H_C of §4.112 on the real square-summable state space of the infinite Ammann–Beenker graph. Write L=(D−A)/16 for its graph Laplacian, C=4+2√2 for the canonical plateau height, and U=C I+L for the uniform bulk. The central defect H_C−U is supported in the original seventeen-site sector; no extra static wells are introduced. The isolated central crossing and its gap ≥1/122 are distinct from the remote modes studied here.

### 4.114. Exact energies and local completeness (L9.3)

On each exact recurring radius-two cell whose center is farther than four from the origin, the translated compact A and B patterns are genuine eigenvectors of H_C at E_A=C+3/16 and E_B=C+1/4. Their squared norms equal eight and their inner product is zero. These energies are shared by every such cell, and their difference is exactly 1/16. This is an internal splitting, not a gap to the rest of the spectrum. For every finite N, prescribed radius and nonnegative separation, there exist N such cells with mutually disjoint complete candidate neighborhoods and all 2N compact vectors mutually orthogonal. The transfer follows because the defect annihilates exterior-supported states, not from a compressed finite Hamiltonian.

- [NaturalPlateauPairs](../SpectralGeometry/AmmannBeenkerNaturalPlateauPairs.lean): `canonicalPlateau_eq_bulk_of_exterior_support`, `naturalPlateauPair_eigenvectors`, `exact_recurrent_natural_plateau_pairs`.
- [NaturalCellCompleteness](../SpectralGeometry/AmmannBeenkerNaturalCellCompleteness.lean): `naturalCell_supported_eigenvector_classification`. The actual degree diagonal is 8 at the center, 3 on the first ring and 4 on the second ring. Eight exterior witness equations force cancellation on the second ring; the full interior equations force zero center amplitude and alternating first-ring coordinates. For a supported Laplacian eigenvector with coefficients a,b at eigenvalue e, (3−16e)a=0 and (4−16e)b=0. Every nonzero supported eigenvector is therefore a nonzero scalar multiple of A or B at its corresponding energy.
- [NaturalRemoteCompleteness](../SpectralGeometry/AmmannBeenkerNaturalRemoteCompleteness.lean): `naturalRemoteCell_card`, `naturalRemoteCell_laplacian_classification`, `naturalRemoteCell_plateau_classification`. Reverse translation preserves the full eigenvector equations, including exterior neighbors, and transfers the classification to H_C.

There are exactly two supported eigenvector directions across all real energies in a certified seventeen-site cell, one at each distinct energy. This does not classify states supported in larger regions and does not assert simplicity of either full-graph eigenspace.

### 4.115. Infinite multiplicity and limits of spectral isolation (L9.4)

The arbitrary finite orthogonal families imply that the full eigenspaces at E_A and E_B are infinite-dimensional. The same is true at the corresponding shifted energies for every uniform bulk height, including zero. More strongly, for each prescribed recurrent cell one can place another cell arbitrarily far away whose two modes are orthogonal to both original directions. Consequently no positive residual lower bound g‖x‖≤‖(H_C−eI)x‖ holds for all x orthogonal to a single cell's two modes, at either natural energy e. Exact local completeness and global infinite multiplicity are compatible.

- [NaturalMultiplicity](../SpectralGeometry/AmmannBeenkerNaturalMultiplicity.lean): `canonicalPlateau_natural_eigenspaces_infinite`, `plateauBulk_natural_eigenspaces_infinite`.
- [NaturalIsolationObstruction](../SpectralGeometry/AmmannBeenkerNaturalIsolationObstruction.lean): `naturalPlateauPair_orthogonal_partners`, `naturalPlateauPair_exterior_eigenvector`, `naturalPlateauPair_no_individual_residual_gap`.

A collective residual bound instead concerns the complement of the **entire** eigenspace at e. Uniform bulk spectral translation is exact, and the collective residual bound at C+e is equivalent to that for L at e. At either natural energy of H_C any such bound is at most 1/16, using a nonzero eigenvector at the other energy. This is only an upper bound. Whether either energy is isolated in the real spectrum or accumulated by other spectral points remains unresolved.

If a real energy belongs to the bulk resolvent, the map sending an H_C eigenvector to its image under the central defect is injective. Its eigenspace is therefore finite-dimensional with dimension at most the defect rank, hence at most seventeen. Infinite-dimensional eigenspaces of H_C must occur at bulk spectral points. The enclosure [C,C+1] is not a claim that the spectrum fills an interval, nor an identification of the essential spectrum.

- [NaturalCollectiveSpectrum](../SpectralGeometry/AmmannBeenkerNaturalCollectiveSpectrum.lean): `plateauBulk_mem_realSpectrum_iff`, `plateauBulk_collectiveResidualBound_iff`, `canonicalPlateau_collectiveResidualBound_le`.
- [NaturalDefectComparison](../SpectralGeometry/AmmannBeenkerNaturalDefectComparison.lean): `natural_finiteDefect_eigenspace_bound`, `canonicalPlateau_eigenspace_bound_outside_bulk`, `canonicalPlateau_infinite_eigenspace_mem_bulk`.

### 4.116. Spatially selective controls and exact preparation (L9.5–L9.6)

Each recurring cell admits a first-ring onsite control R_j and an eight-edge matching control M_j. Their exact norms are 1 and 2, respectively. For signed real coefficients δ_j,η_j, the perturbation norm is at most |δ_j|+2|η_j|. On the A/B plane the full driven Hamiltonian acts as the matrix

    [ E_A+δ_j+η_j    −η_j       ]
    [ −η_j           E_B+η_j    ]

in equally normalized A/B coordinates. Controls on another selected cell annihilate that plane under complete candidate-neighborhood disjointness. The common bounded self-adjoint family Hamiltonian preserves each selected plane and its orthogonal complement; it also acts on the central plane by the original crossing energy. This is exact spatial selectivity despite equal energies between replicas. No individual spectral gap is assumed.

The drift compensation δ=1/16+d equalizes the baseline levels when d=0. In normalized dark/bright coordinates, the compensated matching and onsite controls implement phase and mixing rotations. Three unit-time pulses with coefficients (δ,η)=(1/16,p), (1/16−2t,0), (1/16,q) reach any normalized complex target from dark up to a specified phase of modulus one, with 0≤t≤π/2. The construction provides continuous real and imaginary full-space components, norm one, exactly zero leakage including the switches, and the coupled Schrödinger equations on each open pulse interval. Differentiability at switches is not asserted. The compensating offset is not an arbitrarily weak control scheme.

The same exact dynamics can be combined under one common Hamiltonian: undriven selected cells undergo their known free evolution, and independently driven cells follow their local protocols. The two-cell result extends to arbitrary finite certified disjoint families S. For real weights c_j with Σ c_j²=1 and independently normalized local complex targets (a_j,b_j), the initial weighted sum of dark vectors evolves continuously to the weighted sum of the chosen local targets, each carrying its own explicit phase. The total squared norm stays one, the trajectories have no amplitudes outside the union of the selected cells, and the same three intervals suffice. These are direct-sum states of one Hilbert space, not tensor products of N qubits. Relative phases between different cells are not independently removed or claimed globally irrelevant.

- [NaturalRemoteControls](../SpectralGeometry/AmmannBeenkerNaturalRemoteControls.lean) and [NaturalControlSelectivity](../SpectralGeometry/AmmannBeenkerNaturalControlSelectivity.lean): local geometry, exact action, `naturalFamilyHamiltonian_pair_action`, `naturalFamilyHamiltonian_central_action`, `naturalFamilyHamiltonian_remote_complement`, `naturalFamilyHamiltonian_central_complement`.
- [NaturalControlNorms](../SpectralGeometry/AmmannBeenkerNaturalControlNorms.lean): `naturalRemoteOnsite_opNorm`, `naturalRemoteMatching_opNorm`, `naturalRemotePerturbation_norm_le`, `naturalRemote_compensated_pair_action`.
- [NaturalPairDynamics](../SpectralGeometry/AmmannBeenkerNaturalPairDynamics.lean), [NaturalPulseComposition](../SpectralGeometry/AmmannBeenkerNaturalPulseComposition.lean) and [NaturalExactPreparation](../SpectralGeometry/AmmannBeenkerNaturalExactPreparation.lean): explicit trajectories, normalization and support, continuous pulse composition, phase-retaining rotations and `naturalProtocol_exact_preparation`.
- [NaturalFamilyDynamics](../SpectralGeometry/AmmannBeenkerNaturalFamilyDynamics.lean): `naturalFamily_spectator_solvesAt`, `naturalFamily_driven_with_spectator` and common-Hamiltonian superposition.
- [NaturalTwoCellPreparation](../SpectralGeometry/AmmannBeenkerNaturalTwoCellPreparation.lean) and [NaturalFinitePreparation](../SpectralGeometry/AmmannBeenkerNaturalFinitePreparation.lean): `naturalTwo_exact_preparation` and `naturalFinite_exact_preparation`.

### 4.117. Free storage and finite-time stability (L9.7)

When controls are switched off, a remote A/B superposition evolves with phases exp(−iE_Aτ), exp(−iE_Bτ). Its support and norm remain exactly preserved. The relative phase rotates at frequency 1/16; the prepared ray returns after 32π, not at every time. The preparation and storage trajectory is continuous at the final switch and satisfies the free full-graph equations afterwards. See [NaturalStorage](../SpectralGeometry/AmmannBeenkerNaturalStorage.lean), `naturalStorage_AB_coefficients`, `naturalStorage_period_return`, `naturalProtocolStored_continuous`, `naturalProtocolStored_solves_after`, `naturalProtocolStored_return`.

For a bounded symmetric time-independent perturbation P on the entire real Hilbert space, compare an ideal normalized storage trajectory (r,i) with a perturbed trajectory (u,j) with the same initial data. For τ≥0 the squared state distance satisfies

    ‖u(τ)−r(τ)‖² + ‖j(τ)−i(τ)‖² ≤ 2‖P‖τ
    ‖u(τ)−r(τ)‖² + ‖j(τ)−i(τ)‖² ≤ ‖P‖²τ².

The first bound follows from conservation of weight and a differential overlap inequality; the sharper quadratic bound follows from the error differential inequality and regularizing its square root. Neither needs a spectral gap. These intermediate theorems take existence of the perturbed trajectory as a hypothesis.

- [NaturalDynamicalStability](../SpectralGeometry/AmmannBeenkerNaturalDynamicalStability.lean): `naturalTrajectoryWeight_constant`, `naturalStorage_error_sq_le`.
- [NaturalQuadraticStability](../SpectralGeometry/AmmannBeenkerNaturalQuadraticStability.lean): `naturalTrajectory_error_quadratic_le`, `naturalStorage_error_quadratic_le`.

The normalized dark and bright vectors define an orthogonal projection onto the encoded remote plane. Its complement measures leakage, including directions inside the same seventeen-site cell that are not in the encoded plane, as well as amplitude elsewhere. Orthogonality, idempotence, nearest-plane identity and exact weight accounting imply that the total squared off-plane norm is at most ‖P‖²τ², with retained plane weight at least 1−‖P‖²τ². These estimates are not restricted to perturbations that preserve the plane. See [NaturalLeakage](../SpectralGeometry/AmmannBeenkerNaturalLeakage.lean), `naturalRemotePart_idempotent`, `naturalRemoteLeakage_nearest_sq`, `naturalRemoteLeakageWeight_budget`, `naturalStorage_leakage_quadratic_le`, `naturalStorage_retained_weight_ge`.

Finally [NaturalBoundedEvolution](../SpectralGeometry/AmmannBeenkerNaturalBoundedEvolution.lean) constructs the full perturbed solution itself. For a bounded real operator H, the block generator G_H(r,i)=(Hi,−Hr) is bounded on the product of the two complete real Hilbert spaces. The Banach-algebra exponential exp(τG_H) acting on the initial pair gives a solution for every real time. The derivative is G_H applied to the solution, and symmetry of H gives conservation of the physical squared Hilbert weight for nonnegative time as stated in the verified theorem. This weight is the sum of squared norms, not the product Banach norm used to construct the exponential. The construction discharges the existence hypothesis in the leakage and retention estimates for H=H_C+P.

The key declarations are `naturalBoundedEvolution_initial`, `naturalBoundedEvolution_deriv`, `naturalBoundedEvolution_solvesAt`, `naturalBoundedEvolution_weight`, `naturalFullSolves_exists` and `naturalBoundedStorage_leakage_and_retention`. The final result applies to a normalized remote state, a certified remote recurrent cell and any bounded symmetric static P, for τ≥0. The estimate is informative for small ‖P‖τ; it is not uniform-in-time protection, exclusion of replica mixing, or an evolution construction for the original unbounded confined model.

### 4.118. Arbitrary finite architecture and remaining questions (L9.8)

Together the placement, local classification, family reduction and finite preparation theorems establish an ideal arbitrarily large finite addressable direct-sum architecture on the unchanged plateau. The geometry permits any finite number of selected separated cells. The controls are local and signed, and the finite-family protocol is exact. The construction does not establish an infinite simultaneously driven family, a tensor-product architecture, a uniform-in-N bound on aggregate control strength, entanglement, hardware feasibility or spectral protection for individual remote cells.

The next mathematical questions are collective isolation versus accumulation at the two natural energies; larger-support compact modes; arbitrarily weak remote controls and pulse schedules; concrete static disorder and replica-mixing examples; refocusing or phase tracking; and a comparison with the uniform zero-potential model and the deferred engineered architecture. The generic finite-time perturbation estimate alone does not establish robustness to long-time disorder. Any proposed independent statement selection should preserve the explicit geometry, support, separation and perturbation hypotheses; a new registry submission requires a standalone Challenge and independent proof comparison. See [the roadmap](multi-qubit-roadmap.md) and [maintenance rules](maintenance-rules.md).
