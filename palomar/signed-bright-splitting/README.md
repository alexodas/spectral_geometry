# Palomar candidate: signed dark/bright spectral splitting

This directory holds the **active, theorem-specific** Comparator configuration:
[`comparator.json`](comparator.json).

Selected scientific theorem:
`SpectralGeometry.AmmannBeenker.crossing_final_signed_bright_spectral_splitting`.

The six other selected declarations are required model witnesses for
the independently stated octagonal graph; they are not six separate
scientific submissions. The root [`Challenge.lean`](../../Challenge.lean)
defines the full model using only Mathlib and leaves only selected
proof obligations blank. [`Solution.lean`](../../Solution.lean)
imports the verified source theorem and does not import Challenge.

The theorem concerns **real natural-domain eigenvectors of the entire
infinite operator** for `0<|ε|≤1/1024`. It proves one protected
simple energy and one unique simple nearby moving energy, the signed
direction of the shift, its `112ε²` error, and the exterior
eigenvector bound. It does not assert quantum control or a
separate theorem for complex spectrum.

The project verification script explicitly reads this directory's
Comparator, runs the Lean full build, and invokes the bundled
independent kernel checkers. There is intentionally **no**
`comparator.json` at repository root. Only a fully green
verification on an immutable source commit can support an eventual
Palomar submission; preparing this package is not itself a
Palomar registration or acceptance.

The earlier *unsubmitted* generator-response candidate is preserved
at [`../dark-bright/`](../dark-bright/).
