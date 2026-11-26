[← Main README and table of contents](../README.md)

## 5. Building and verification

The canonical import list is maintained in [`SpectralGeometry.lean`](../SpectralGeometry.lean). It imports **116 Lean modules**: eleven analytic and window modules, four finite-dimensional geometry modules, and one hundred and one infinite geometry/operator/spectral modules (including domain-generic interfaces). The full library is Lean-verified. The original fourteen bright generator lemmas and the fifteenth bundled theorem are distinct from the later spectral-level results in §4.93.

- **Analytic core, indexed points and certified windows (11):**
  - [`CanonicalProduct.lean`](../SpectralGeometry/CanonicalProduct.lean)
  - [`CanonicalProductAnalytic.lean`](../SpectralGeometry/CanonicalProductAnalytic.lean)
  - [`CanonicalProductZeroOrder.lean`](../SpectralGeometry/CanonicalProductZeroOrder.lean)
  - [`IndexedSpectralPoints.lean`](../SpectralGeometry/IndexedSpectralPoints.lean)
  - [`OrderedSpectralWindow.lean`](../SpectralGeometry/OrderedSpectralWindow.lean)
  - [`CanonicalProductClusterCount.lean`](../SpectralGeometry/CanonicalProductClusterCount.lean)
  - [`AnalyticZeroLocalization.lean`](../SpectralGeometry/AnalyticZeroLocalization.lean)
  - [`CanonicalProductApproximation.lean`](../SpectralGeometry/CanonicalProductApproximation.lean)
  - [`AnalyticDiskZeroCount.lean`](../SpectralGeometry/AnalyticDiskZeroCount.lean)
  - [`AnalyticRouche.lean`](../SpectralGeometry/AnalyticRouche.lean)
  - [`CanonicalProductNumericalBounds.lean`](../SpectralGeometry/CanonicalProductNumericalBounds.lean)
- **Finite-dimensional geometry (4):**
  - [`FinitePerturbation.lean`](../SpectralGeometry/FinitePerturbation.lean)
  - [`FinitePositiveEnergy.lean`](../SpectralGeometry/FinitePositiveEnergy.lean)
  - [`FiniteGeometricEnergy.lean`](../SpectralGeometry/FiniteGeometricEnergy.lean)
  - [`FiniteStrictPositivity.lean`](../SpectralGeometry/FiniteStrictPositivity.lean)
- **Onsite foundations, growth and summability (6):**
  - [`InfiniteOnsite.lean`](../SpectralGeometry/InfiniteOnsite.lean)
  - [`InfiniteOnsiteDensity.lean`](../SpectralGeometry/InfiniteOnsiteDensity.lean)
  - [`InfiniteOnsiteEigenvalues.lean`](../SpectralGeometry/InfiniteOnsiteEigenvalues.lean)
  - [`InfiniteOnsiteSummability.lean`](../SpectralGeometry/InfiniteOnsiteSummability.lean)
  - [`InfiniteOnsitePowerGrowth.lean`](../SpectralGeometry/InfiniteOnsitePowerGrowth.lean)
  - [`InfiniteOnsiteOrderedEnumeration.lean`](../SpectralGeometry/InfiniteOnsiteOrderedEnumeration.lean)
- **Infinite interactions and local-operator estimates (11):**
  - [`InfiniteFiniteEdgeInteraction.lean`](../SpectralGeometry/InfiniteFiniteEdgeInteraction.lean)
  - [`InfiniteBoundedPerturbation.lean`](../SpectralGeometry/InfiniteBoundedPerturbation.lean)
  - [`InfiniteSummableEdgeInteraction.lean`](../SpectralGeometry/InfiniteSummableEdgeInteraction.lean)
  - [`InfiniteLocalMatching.lean`](../SpectralGeometry/InfiniteLocalMatching.lean)
  - [`InfiniteLocalBoundedDegree.lean`](../SpectralGeometry/InfiniteLocalBoundedDegree.lean)
  - [`InfiniteLocalEigenvalueBounds.lean`](../SpectralGeometry/InfiniteLocalEigenvalueBounds.lean)
  - [`InfiniteLocalSignedPerturbationGap.lean`](../SpectralGeometry/InfiniteLocalSignedPerturbationGap.lean)
  - [`InfiniteLocalCoerciveGap.lean`](../SpectralGeometry/InfiniteLocalCoerciveGap.lean)
  - [`InfiniteLocalGraphNorm.lean`](../SpectralGeometry/InfiniteLocalGraphNorm.lean)
  - [`InfiniteLocalClosedGraph.lean`](../SpectralGeometry/InfiniteLocalClosedGraph.lean)
  - [`InfiniteLocalAdjointCharacterization.lean`](../SpectralGeometry/InfiniteLocalAdjointCharacterization.lean)
- **Onsite resolvents and compactness (4):**
  - [`InfiniteOnsiteResolvent.lean`](../SpectralGeometry/InfiniteOnsiteResolvent.lean)
  - [`InfiniteOnsiteFiniteLowEnergy.lean`](../SpectralGeometry/InfiniteOnsiteFiniteLowEnergy.lean)
  - [`InfiniteOnsiteCompactResolvent.lean`](../SpectralGeometry/InfiniteOnsiteCompactResolvent.lean)
  - [`InfiniteOnsiteResolventIdentity.lean`](../SpectralGeometry/InfiniteOnsiteResolventIdentity.lean)
- **Interacting resolvents and spectral results (21):**
  - [`InfiniteLocalCompactResolvent.lean`](../SpectralGeometry/InfiniteLocalCompactResolvent.lean)
  - [`InfiniteLocalCompactResolventBounds.lean`](../SpectralGeometry/InfiniteLocalCompactResolventBounds.lean)
  - [`InfiniteLocalSelfAdjointPMap.lean`](../SpectralGeometry/InfiniteLocalSelfAdjointPMap.lean)
  - [`InfiniteLocalResolventSpectrum.lean`](../SpectralGeometry/InfiniteLocalResolventSpectrum.lean)
  - [`InfiniteLocalEigenpairCorrespondence.lean`](../SpectralGeometry/InfiniteLocalEigenpairCorrespondence.lean)
  - [`InfiniteLocalFullEigenspaces.lean`](../SpectralGeometry/InfiniteLocalFullEigenspaces.lean)
  - [`InfiniteLocalFredholmSpectralExhaustion.lean`](../SpectralGeometry/InfiniteLocalFredholmSpectralExhaustion.lean)
  - [`InfiniteLocalFullEigenvectorsComplete.lean`](../SpectralGeometry/InfiniteLocalFullEigenvectorsComplete.lean)
  - [`InfiniteLocalResolventNormGap.lean`](../SpectralGeometry/InfiniteLocalResolventNormGap.lean)
  - [`InfiniteLocalResolventSpectralIsolation.lean`](../SpectralGeometry/InfiniteLocalResolventSpectralIsolation.lean)
  - [`InfiniteLocalFullEigenvalueIsolation.lean`](../SpectralGeometry/InfiniteLocalFullEigenvalueIsolation.lean)
  - [`InfiniteLocalFullEigenvalueEnumeration.lean`](../SpectralGeometry/InfiniteLocalFullEigenvalueEnumeration.lean)
  - [`InfiniteLocalFullRealResolvent.lean`](../SpectralGeometry/InfiniteLocalFullRealResolvent.lean)
  - [`InfiniteLocalFullEigenvalueMultiplicity.lean`](../SpectralGeometry/InfiniteLocalFullEigenvalueMultiplicity.lean)
  - [`InfiniteLocalFullEigenvalueMultiplicityCoverage.lean`](../SpectralGeometry/InfiniteLocalFullEigenvalueMultiplicityCoverage.lean)
  - [`InfiniteLocalFullRealSpectralCompleteness.lean`](../SpectralGeometry/InfiniteLocalFullRealSpectralCompleteness.lean)
  - [`InfiniteLocalFullOrderedMultiplicityWindows.lean`](../SpectralGeometry/InfiniteLocalFullOrderedMultiplicityWindows.lean)
  - [`InfiniteLocalFullGlobalOrderedEnumeration.lean`](../SpectralGeometry/InfiniteLocalFullGlobalOrderedEnumeration.lean)
  - [`InfiniteLocalFullOrderedEigenvalueDivergence.lean`](../SpectralGeometry/InfiniteLocalFullOrderedEigenvalueDivergence.lean)
  - [`InfiniteLocalFullVariationalComparison.lean`](../SpectralGeometry/InfiniteLocalFullVariationalComparison.lean)
  - [`InfiniteLocalFullLowEnergyCounting.lean`](../SpectralGeometry/InfiniteLocalFullLowEnergyCounting.lean)

- **Simultaneous observation, variational control and full summability (12):**
  - [`DomainSpectralSubspace.lean`](../SpectralGeometry/DomainSpectralSubspace.lean)
  - [`InfiniteLowEnergyObservation.lean`](../SpectralGeometry/InfiniteLowEnergyObservation.lean)
  - [`InfiniteLowEnergyCounting.lean`](../SpectralGeometry/InfiniteLowEnergyCounting.lean)
  - [`InfiniteLocalFullSpectralObservation.lean`](../SpectralGeometry/InfiniteLocalFullSpectralObservation.lean)
  - [`DomainEigenbasis.lean`](../SpectralGeometry/DomainEigenbasis.lean)
  - [`InfiniteLocalFullEigenbasis.lean`](../SpectralGeometry/InfiniteLocalFullEigenbasis.lean)
  - [`OrderedVariationalPrinciple.lean`](../SpectralGeometry/OrderedVariationalPrinciple.lean)
  - [`OrderedLevelMultiplicityTwo.lean`](../SpectralGeometry/OrderedLevelMultiplicityTwo.lean)
  - [`InfiniteOrderedSpectralControl.lean`](../SpectralGeometry/InfiniteOrderedSpectralControl.lean)
  - [`InfiniteOrderedSpectralExistence.lean`](../SpectralGeometry/InfiniteOrderedSpectralExistence.lean)
  - [`InfiniteFullSpectralSummability.lean`](../SpectralGeometry/InfiniteFullSpectralSummability.lean)
  - [`InfinitePositiveSpectralControl.lean`](../SpectralGeometry/InfinitePositiveSpectralControl.lean)

- **Full spectral products and analytic zero response (7):**
  - [`InfiniteFullSpectralProduct.lean`](../SpectralGeometry/InfiniteFullSpectralProduct.lean)
  - [`OrderedSpectralProductBridge.lean`](../SpectralGeometry/OrderedSpectralProductBridge.lean)
  - [`FiniteSectorZeroResponse.lean`](../SpectralGeometry/FiniteSectorZeroResponse.lean)
  - [`PositiveFiniteSectorZeroResponse.lean`](../SpectralGeometry/PositiveFiniteSectorZeroResponse.lean)
  - [`FullSpectralZeroLocalization.lean`](../SpectralGeometry/FullSpectralZeroLocalization.lean)
  - [`FullSpectralZeroCounts.lean`](../SpectralGeometry/FullSpectralZeroCounts.lean)
  - [`LinearOnsiteZeroCertificate.lean`](../SpectralGeometry/LinearOnsiteZeroCertificate.lean)

- **Explicit octagonal geometry, operator and spectral products (38):**
  - [`AmmannBeenkerCutProject.lean`](../SpectralGeometry/AmmannBeenkerCutProject.lean)
  - [`AmmannBeenkerGraph.lean`](../SpectralGeometry/AmmannBeenkerGraph.lean)
  - [`AmmannBeenkerOperator.lean`](../SpectralGeometry/AmmannBeenkerOperator.lean)
  - [`AmmannBeenkerSummability.lean`](../SpectralGeometry/AmmannBeenkerSummability.lean)
  - [`AmmannBeenkerSpectralProducts.lean`](../SpectralGeometry/AmmannBeenkerSpectralProducts.lean)
  - [`AmmannBeenkerRadialGap.lean`](../SpectralGeometry/AmmannBeenkerRadialGap.lean)
  - [`AmmannBeenkerCompactModes.lean`](../SpectralGeometry/AmmannBeenkerCompactModes.lean)
  - [`AmmannBeenkerCompactStates.lean`](../SpectralGeometry/AmmannBeenkerCompactStates.lean)
  - [`AmmannBeenkerCompactCrossing.lean`](../SpectralGeometry/AmmannBeenkerCompactCrossing.lean)
  - [`AmmannBeenkerEdgeControl.lean`](../SpectralGeometry/AmmannBeenkerEdgeControl.lean)
  - [`AmmannBeenkerTwoControlAlgebra.lean`](../SpectralGeometry/AmmannBeenkerTwoControlAlgebra.lean)
  - [`AmmannBeenkerQubitLeakage.lean`](../SpectralGeometry/AmmannBeenkerQubitLeakage.lean)
  - [`QubitLeakagePulseBound.lean`](../SpectralGeometry/QubitLeakagePulseBound.lean)
  - [`DomainEigenbasisGapResidual.lean`](../SpectralGeometry/DomainEigenbasisGapResidual.lean)
  - [`AmmannBeenkerNearCrossingEigenvectors.lean`](../SpectralGeometry/AmmannBeenkerNearCrossingEigenvectors.lean)
  - [`AmmannBeenkerPulseResidualBound.lean`](../SpectralGeometry/AmmannBeenkerPulseResidualBound.lean)
  - [`AmmannBeenkerPulseIntertwining.lean`](../SpectralGeometry/AmmannBeenkerPulseIntertwining.lean)
  - [`AmmannBeenkerPulseSelfAdjoint.lean`](../SpectralGeometry/AmmannBeenkerPulseSelfAdjoint.lean)
  - [`AmmannBeenkerPostpulseSwitchOff.lean`](../SpectralGeometry/AmmannBeenkerPostpulseSwitchOff.lean)
  - [`AmmannBeenkerDarkSchrodinger.lean`](../SpectralGeometry/AmmannBeenkerDarkSchrodinger.lean)
  - [`AmmannBeenkerBrightAmplitude.lean`](../SpectralGeometry/AmmannBeenkerBrightAmplitude.lean) *(14 original generator theorems and one combined Palomar-candidate theorem)*
  - [`AmmannBeenkerBrightSpectralSplitting.lean`](../SpectralGeometry/AmmannBeenkerBrightSpectralSplitting.lean) *(Lean-verified L1–L5, including the signed splitting, simple pair and quantitative exterior/energy bounds; §§4.93–4.98)*
  - [`AmmannBeenkerCoordinatedRingControl.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedRingControl.lean) *(eleven L7a theorems: matched edges, exact dark cancellation and full-space symmetry; §4.99)*
  - [`AmmannBeenkerCoordinatedInvariantPlane.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedInvariantPlane.lean) *(verified L7a completion and exact dark/bright action; §4.100; verified L8a.1 exact control norms and bounded decomposition; §4.106)*
  - [`AmmannBeenkerCoordinatedLieAlgebra.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedLieAlgebra.lean) *(verified L7b Pauli decomposition and commutators; §4.100)*
  - [`AmmannBeenkerCoordinatedLieGeneration.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedLieGeneration.lean) *(full real su(2) generation; §4.101)*
  - [`AmmannBeenkerCoordinatedEuler.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedEuler.lean) *(constructive normalized-pair Euler rotations and independent signed generator coefficients; §4.101)*
  - [`AmmannBeenkerCoordinatedPairDynamics.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedPairDynamics.lean) *(exact natural-domain complex-component eigenpair trajectories; §4.102)*
  - [`AmmannBeenkerCoordinatedAxisDynamics.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedAxisDynamics.lean) *(single-axis Schrödinger equations, norm conservation, zero leakage and full real self-adjointness; §4.102; verified L8a.2 exact controlled plane levels and natural-domain reduction; §4.107; verified L8a.3 full real spectral exclusion; §4.108; verified L8a.4 consolidated positive cluster isolation; §4.109; verified centered spectral protection; §4.110)*
  - [`AmmannBeenkerCoordinatedRotationDynamics.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedRotationDynamics.lean) *(exact phase-weighted rotation action and embedding into full natural-domain trajectories; §4.103)*
  - [`AmmannBeenkerCoordinatedPulseComposition.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedPulseComposition.lean) *(continuous three-pulse trajectory, switch matching, full-domain equations, conserved norm and zero leakage; §4.104)*
  - [`AmmannBeenkerCoordinatedExactPreparation.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedExactPreparation.lean) *(exact arbitrary normalized target preparation from dark up to global phase with continuous full-domain zero-leakage dynamics; §4.105)*
  - [`AmmannBeenkerCentralPatch.lean`](../SpectralGeometry/AmmannBeenkerCentralPatch.lean)
  - [`AmmannBeenkerCentralKernel.lean`](../SpectralGeometry/AmmannBeenkerCentralKernel.lean)
  - [`AmmannBeenkerCrossingMultiplicity.lean`](../SpectralGeometry/AmmannBeenkerCrossingMultiplicity.lean)
  - [`AmmannBeenkerCrossingGapCycle.lean`](../SpectralGeometry/AmmannBeenkerCrossingGapCycle.lean)
  - [`AmmannBeenkerCrossingGapFinite.lean`](../SpectralGeometry/AmmannBeenkerCrossingGapFinite.lean)
  - [`AmmannBeenkerCrossingGapOrthogonality.lean`](../SpectralGeometry/AmmannBeenkerCrossingGapOrthogonality.lean)

- **Bounded spectral errors and full zero-cluster certificates (2):**
  - [`InfiniteBoundedSpectralStability.lean`](../SpectralGeometry/InfiniteBoundedSpectralStability.lean)
  - [`InfiniteFullSpectralCluster.lean`](../SpectralGeometry/InfiniteFullSpectralCluster.lean)

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
[Challenge](../Challenge.lean), [Solution](../Solution.lean) and
[formalization metadata](../formalization.yaml) describe **Spectral Protection During Coordinated Control on an Infinite Ammann–Beenker Graph** (§4.110).
The principal selected theorem is
`SpectralGeometry.AmmannBeenker.coordinatedCluster_centered_isolation`.
Five concrete model witnesses, three locality certificates and supporting
plane-energy, domain-reduction and numerical-bound theorems accompany it.
All definitions are concrete; the independent Mathlib-only Challenge
uses proposition proof placeholders only. Solution publicly imports the
substantive controlled spectral proof, not Challenge.

The active [theorem-specific Comparator](../palomar/spectral-protection-during-coordinated-control/comparator.json)
and matching snapshots are in [`palomar/spectral-protection-during-coordinated-control/`](../palomar/spectral-protection-during-coordinated-control/).
The complete 116-module substantive library is Lean-verified with no
proof holes. Independent comparison of all 15 newly selected statements passed,
including the bundled NanoDa and con-ron kernels; no fourth registration
is claimed.

The third registered preparation package (§4.105) remains preserved in
[`palomar/exact-leakage-free-preparation/`](../palomar/exact-leakage-free-preparation/),
with five supporting model witnesses, three locality certificates and
`coordinatedProtocol_exact_preparation`, nine selected propositions in total.
Its independent comparison passed, including NanoDa and con-ron.
The third result is registered as [PALOMAR-2026-11-25-000001 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-25-000001&version=1).

The first registered exact-multiplicity theorem remains attached to
its original immutable revision. The second registered signed-splitting
package, with [Comparator](../palomar/signed-bright-splitting/comparator.json),
Challenge, Solution and metadata snapshots, is preserved in
[`palomar/signed-bright-splitting/`](../palomar/signed-bright-splitting/).
It retains [PALOMAR-2026-11-23-000017 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-23-000017&version=1).
The unsubmitted generator-response package remains archived under
[`palomar/dark-bright/`](../palomar/dark-bright/).
No root `comparator.json` exists. Local packaging and verification
checks select the new spectral-protection Comparator explicitly.

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
[formalization.yaml](../formalization.yaml) for the mathematical scope, research
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

