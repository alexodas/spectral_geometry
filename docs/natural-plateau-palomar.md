[← Main README and table of contents](../README.md) · [Natural plateau architecture](natural-plateau-architecture.md)

# Eighth Palomar candidate — local completeness and global multiplicity

For the specified infinite octagonal Ammann–Beenker graph, a natural two-state cell can be locally complete even though each of its two energies has infinite global multiplicity.

The graph is the same centered cut-and-project graph as in the earlier registered results. Its weighted graph Laplacian L=(D−A)/16 acts on real square-summable vertex states. The fixed bounded canonical Hamiltonian H has a constant exterior potential C=4+2√2 and retains the original central defect. No new static wells are added. The two alternating compact ring patterns A and B have squared norms eight and, on every exactly recurrent remote seventeen-site cell, are full-graph eigenvectors at C+3/16 and C+1/4. Arbitrarily many mutually orthogonal pairs can be placed beyond any radius, with complete disjoint candidate neighborhoods and any prescribed nonnegative separation.

Every nonzero eigenvector supported within a certified seventeen-site remote cell is a nonzero scalar multiple of one of these two patterns, at the corresponding energy. The proof uses actual full-degree interior equations and exterior cancellation, not the spectrum of an artificially isolated finite matrix. This is classification of eigenvectors with this specified support, not classification of larger supported states or a claim of full-graph simplicity.

Both full eigenspaces of H at the natural energies are infinite-dimensional. The same holds for the uniform bulk C I+L at its corresponding energies for any real C, including zero. Arbitrarily distant equal-energy partners are orthogonal to both modes of any prescribed recurring cell. As a consequence, no positive residual lower bound at either natural energy exists on the entire orthogonal complement of a single cell's two modes.

The complement of an entire eigenspace is a different question: collective residual bounds are invariant under uniform energy shifts, and any such bound at either natural canonical energy is at most 1/16. This upper bound does not establish a positive collective gap. At a real bulk resolvent energy, the canonical eigenspace is finite-dimensional of dimension at most seventeen, because the central defect has rank at most seventeen.

The result combines concrete local completeness, global infinite multiplicity, and an obstruction to individual spectral isolation. It neither identifies the essential spectrum nor proves collective isolation, accumulation, or novelty relative to all prior literature. Control and dynamics are separate results. The substantive Lean proofs have passed full checking; independent comparison of this new statement selection and registry review are pending.

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

The 22-statement selection includes nine supporting concrete-model propositions and thirteen natural-plateau conclusions. The standalone Challenge imports only Mathlib; Solution imports the proved mathematical library, not Challenge. The seven previous packages remain preserved. Submission requires successful independent comparison of this selection and review of the exact public commit. No registration is claimed.
