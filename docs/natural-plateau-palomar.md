[← Main README and table of contents](../README.md) · [Natural plateau architecture](natural-plateau-architecture.md)

# Eighth Palomar candidate — local completeness and global multiplicity

Can a small region of an infinite network have exactly two localized wave patterns, while the same two energies occur infinitely many times elsewhere? For the Ammann–Beenker graph studied here, the answer is yes.

We use the same infinite octagonal network and bounded Hamiltonian as in the sixth registered result. Its potential is constant outside the original central seventeen-site region, with value C = 4 + 2√2. No new remote wells are added. The seventh result showed that the central geometric pattern can recur arbitrarily far away, including its surrounding candidate vertices.

In each such remote seventeen-site cell, two waves, A and B, have alternating positive and negative amplitudes on separate eight-site rings and vanish everywhere else. Their energies are exactly C + 3/16 and C + 1/4. They are orthogonal and each has squared norm eight. The energy difference is 1/16.

The first new conclusion is local completeness: every nonzero eigenvector supported entirely inside a certified remote cell is a nonzero multiple of A or B, at its corresponding energy. There is no third eigenvector direction confined to those seventeen sites. The proof checks the equations on the infinite graph, including cancellation at exterior neighbors, rather than treating the cell as a disconnected finite network.

The second conclusion is infinite global multiplicity. For any finite number of cells and any prescribed separation, copies can be placed arbitrarily far away with disjoint complete candidate neighborhoods. All copied waves are mutually orthogonal. Hence each of the two energies has an infinite-dimensional eigenspace. The same holds for the uniform graph Laplacian with any constant potential, including zero.

This gives a third conclusion: a single remote cell cannot be spectrally isolated from all other replicas at the same energy. Even a distant orthogonal state can have exactly the same energy. A gap after excluding the entire corresponding eigenspace is a different question: any collective residual bound is at most 1/16, but no positive collective gap has been established. At energies outside the uniform bulk spectrum, the central defect can produce eigenspaces of dimension at most seventeen.

Why is this interesting? Exact local classification does not require global simplicity or isolated energy levels. Geometry distinguishes the cells even when energy alone cannot. The result concerns one specified graph and support class; it does not establish collective spectral isolation, a complete spectrum classification, quantum control or experimental feasibility.

All 150 substantive Lean modules and all 22 selected propositions have passed Lean/Mathlib and independent Comparator checks using the Lean default, NanoDa and con-ron kernels. Registry review and independent human peer review are not claimed.

## Selected statements

- `admitted_zero` — The origin belongs to the concrete octagonal acceptance window.
- `finite_norm_sublevel` — Every bounded physical-radius region has finitely many admitted vertices; defines the central sector.
- `mate_involutive` — Each signed parity matching is an involution, so the weighted matching Laplacian is concrete.
- `canonicalPlateauHeight_ge_five` — The fixed height is at least five, so the bounded canonical onsite operator is defined.
- `plateauPotential_normalized_norm_le` — The normalized onsite multiplier is bounded by one, defining a bounded operator.
- `centralLift_admitted` — All seventeen explicit cell lifts are admitted.
- `centralPatch_card` — The explicit central cell has seventeen distinct vertices.
- `translatedCompactA_eigenvector` — The translated first-ring alternating mode satisfies the full Laplacian equation at 3/16.
- `translatedCompactB_eigenvector` — The translated second-ring alternating mode satisfies the full Laplacian equation at 1/4.
- `canonicalPlateau_eq_bulk_of_exterior_support` — For a vector zero on the central sector, the canonical Hamiltonian acts exactly as the uniform bulk.
- `naturalPlateauPair_eigenvectors` — At a remote recurrent cell both compact eigenvector equations hold for the actual canonical Hamiltonian, at C+3/16 and C+1/4.
- `exact_recurrent_natural_plateau_pairs` — For every finite N and prescribed radius and nonnegative separation, N exact remote pairs have disjoint complete candidate neighborhoods, squared norms eight and all mutual orthogonality.
- `naturalCell_supported_eigenvector_classification` — Every nonzero real Laplacian eigenvector supported in the original radius-two cell is a nonzero multiple of A at 3/16 or B at 1/4.
- `naturalRemoteCell_card` — Every exactly recurrent translated cell has seventeen vertices.
- `naturalRemoteCell_plateau_classification` — Every nonzero real eigenvector of the actual canonical plateau supported in a remote recurrent cell is a nonzero multiple of one of the two translated modes, at its stated energy.
- `canonicalPlateau_natural_eigenspaces_infinite` — Both full eigenspaces of the canonical Hamiltonian at the natural remote energies are not finite-dimensional.
- `plateauBulk_natural_eigenspaces_infinite` — The same infinite-dimensionality holds at the corresponding energies for any real uniform bulk height, including zero.
- `naturalPlateauPair_orthogonal_partners` — For any prescribed recurrent cell, arbitrarily distant recurrent partners exist, with both eigenvectors orthogonal to both original modes.
- `naturalPlateauPair_no_individual_residual_gap` — At either remote energy no positive residual lower bound can hold on the entire orthogonal complement of a single recurring cell's two modes.
- `plateauBulk_collectiveResidualBound_iff` — Collective residual bounds on the complement of the entire eigenspace are unchanged by a uniform shift of the Hamiltonian and energy.
- `canonicalPlateau_collectiveResidualBound_le` — Any collective residual bound at either canonical remote energy is at most 1/16; this does not give a positive lower bound.
- `canonicalPlateau_eigenspace_bound_outside_bulk` — At a real energy outside the uniform bulk spectrum the canonical plateau eigenspace is finite-dimensional with dimension at most seventeen.

## Verification and submission status

The 22-statement selection includes nine supporting concrete-model propositions and thirteen natural-plateau conclusions. The standalone Challenge is 463 physical lines and 21,695 UTF-8 bytes; this is below both hard limits and the preferred byte count, but exceeds the preferred 300-line review surface. The standalone Challenge imports only Mathlib; Solution imports the proved mathematical library, not Challenge. The seven previous packages remain preserved. All 22 selected propositions passed independent comparison with the Lean default, NanoDa and con-ron kernels. Submission still requires review of the exact public commit and the registry's own checks. No registration is claimed.
