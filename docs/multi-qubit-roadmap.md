[← Main README and table of contents](../README.md) · [Track B roadmap](bright-spectral-splitting-roadmap.md) · [Research roadmap §6.10](research-roadmap.md#610-l9--independently-controllable-spectrally-protected-localized-qubits-open)

# L9 — Independently controllable spectrally protected localized qubits

**Status: active research; L9.1 bounded plateau isolation registered, multi-qubit target not yet proved.** This is the active Track B
direction. Track A (spectral geometry and analytic zeros), the original
L6 single-edge approximate preparation, and L8b–L8e imperfect-control
research are preserved but deferred. All six Palomar registrations and
the original confined Hamiltonian remain unchanged.

## Motivation and target architecture

The fifth registered result, [PALOMAR-2026-11-27-000003 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-27-000003&version=1),
establishes exact preparation from dark with arbitrarily weak ideal
controls, zero leakage and a prescribed fraction of the certified gap
on the original infinite confined graph (§4.111).

The new goal is to find multiple spatially separated copies of the
compact-mode mechanism on that same graph, using a different onsite
potential. Each local two-state plane should have a distinct rest
energy, an individual positive gap to the rest of the full spectrum,
and independently addressable ideal controls. A pair is degenerate at
rest, can split during pulses, and returns to degeneracy when the
controls are switched off. The prepared ray then remains unchanged
under the rest Hamiltonian.

The primary first example is two pairs, one central and one remote.
The ambitious target is any prescribed positive finite number N of
pairs, with the potential and gaps permitted to depend on N.
A fixed infinite architecture, a uniform gap as N grows, physical
hardware robustness and tensor-product quantum registers are not
asserted. Orthogonal two-state subspaces of one single-particle Hilbert
space form a direct sum, not an N-qubit tensor product; entanglement and
multi-qubit gates would require additional mathematics.

![Conceptual energy diagram of two individually protected localized qubits below the bulk spectral enclosure](figures/l9-two-protected-qubits.svg)

*Figure — First L9 target (not yet proved): two localized pairs with
distinct rest energies below the bulk spectral enclosure. Each pair is
degenerate with controls off and may split temporarily under ideal local
control, while retaining individual isolation from the full remaining
spectrum. The shaded windows are schematic; their existence and positive
margins must be proved. The bulk enclosure does not assert that the
spectrum fills an interval or is absolutely continuous.*

## L9.1 — Bounded plateau model

- [x] Introduce a separate bounded onsite potential
  V_R(x) = 1 + min(|p(x)|², R²), with plateau C = 1 + R²,
  preserving the original definitions and the central first-ring
  crossing correction t* = 17/16 + sqrt(2).
- [x] Choose R large enough to preserve both central compact-mode
  equations; distinguish preservation of those eigenvectors from
  preservation of the original exact multiplicity and gap.
- [x] Prove boundedness, symmetry/self-adjointness on the full real
  Hilbert space and equality of the natural domain with the entire space.
- [x] Prove real bounded-inverse spectral isolation of the crossing,
  without assuming compact resolvent or eigenvalue exhaustion.
  Complexification is a separate extension if needed.
- [x] Establish the bulk enclosure sigma(C I + B) ⊆ [C,C+1] using the
  verified positivity and norm bound of the interaction B. Prove the
  appropriate finite-rank perturbation/essential-spectrum statements
  if needed; do not assume that the bulk fills the interval or is
  absolutely continuous.

**Verified foundation.** [`AmmannBeenkerPlateauOperator.lean`](../SpectralGeometry/AmmannBeenkerPlateauOperator.lean)
constructs the bounded self-adjoint real Hamiltonian for every height
C >= 1. The canonical height C = 4 + 4 alpha (alpha = sqrt(2)/2)
preserves the original potential on all seventeen central vertices
and is exactly constant everywhere else. The operator norm is at most
C + 1 + |t*|. The verified
[`AmmannBeenkerPlateauCrossing.lean`](../SpectralGeometry/AmmannBeenkerPlateauCrossing.lean)
transfers the original full-space action on centrally supported states
for C >= 5 and preserves both independent compact eigenvectors at
crossingEnergy. The verified module
[`AmmannBeenkerPlateauResidual.lean`](../SpectralGeometry/AmmannBeenkerPlateauResidual.lean),
uses the central 1/24 bound, exterior barrier 2 and boundary coupling
1/4 to derive ||x|| <= 122 ||(H_C - E*)x|| for orthogonal states on
the old dense natural domain when C >= canonicalPlateauHeight.
The verified [`AmmannBeenkerPlateauMultiplicity.lean`](../SpectralGeometry/AmmannBeenkerPlateauMultiplicity.lean)
extends this bound to the entire Hilbert space using density and
continuity of the compact projection, then identifies the full
crossing eigenspace with the two-dimensional compact plane.
The full-space estimate and exact geometric multiplicity two are now
Lean-verified. The verified modules
[`BoundedSelfAdjointInverse.lean`](../SpectralGeometry/BoundedSelfAdjointInverse.lean)
and [`AmmannBeenkerPlateauSpectrum.lean`](../SpectralGeometry/AmmannBeenkerPlateauSpectrum.lean)
use closed range, self-adjointness and the reducing compact projection
to obtain bounded invertibility of the regularized residual and
exclude every different real spectral energy at distance < 1/122.
These full real spectral results are Lean-verified. The verified
[`AmmannBeenkerPlateauBulk.lean`](../SpectralGeometry/AmmannBeenkerPlateauBulk.lean)
proves the uniform bulk enclosure, finite-rank defect of rank at most
17 and a bundled isolated-double-eigenvalue theorem. No claim about the exact essential spectrum is made.

The sixth registered result focuses on the concrete
bounded plateau model, exact double eigenvalue, full real spectral
gap and finite-rank bulk comparison. Aim for the Registry's preferred
300-line / 32 KiB Challenge review surface using standalone concrete
coordinate definitions; the hard limits are 1,000 lines / 100 KiB.
The standalone Challenge contains 281 lines and 12547 UTF-8 bytes. All 13 selected propositions passed independent Comparator verification with the Lean default, NanoDa and con-ron kernels. Palomar mechanical verification and Challenge renderability passed, and the automated editorial review identified no blocking problem. Registered on 27 November 2026 as [PALOMAR-2026-11-27-000042 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-27-000042&version=1). All earlier registered packages remain unchanged.

## L9.2 — Recurrence of compact-mode patches

**First proof checkpoint (CI pending).** [`AmmannBeenkerPatchRecurrence.lean`](../SpectralGeometry/AmmannBeenkerPatchRecurrence.lean) proposes boundary avoidance for every lattice lift, internal contraction of the existing silver-unit inflation sequence, eventual preservation of every admission and exclusion decision on an arbitrary finite set, and existence of a recurring center beyond any prescribed physical radius. These statements do not yet transfer the compact eigenvectors or prove mutual separation of arbitrarily many copies.

- [ ] Prove recurrence for the exact cut-and-project window and
  lattice coordinates of the implemented graph, including all support
  sites and neighboring sites required for cancellation and control.
- [ ] Construct arbitrarily many mutually separated translated
  patches outside a prescribed radius, with disjoint supports and
  control neighborhoods. A finite patch illustration is not a proof.
- [ ] Transfer the full-space compact-mode equations
  B a_j = (3/16) a_j and B b_j = (1/4) b_j, orthogonality and
  squared norms 8. On a uniform plateau their prospective energies
  are C+3/16 and C+1/4, respectively, not a degenerate pair.
  Infinite multiplicity at a common plateau energy is a separate
  possible consequence of recurrence, not the preferred architecture.

## L9.3 — Two degenerate pairs at distinct rest energies

- [ ] Construct central and remote pairs with disjoint support and
  energies E_0 ≠ E_1. For a translated A/B patch, a candidate onsite
  assignment on the two rings is E_j−3/16 and E_j−1/4, respectively.
  Prove the full eigenvector equations, not just compressed ones.
- [ ] Explore choosing E_j below C with appropriate local wells and
  exterior barriers; keeping a pure plateau without local tuning
  cannot in general produce the desired distinct degenerate pairs.
- [ ] Preserve the original central energy E_0 = 13/4 + sqrt(2)
  if possible. The chosen construction must be justified, not assumed.

## L9.4 — Individual full-spectrum isolation

- [ ] For each pair P_j prove exact dimension two of the eigenspace
  at E_j and an explicit positive lower bound g_j on the distance
  from E_j to the spectrum of the restriction to P_j's orthogonal
  complement, including all other pairs and the bulk.
- [ ] Develop a bounded-inverse or coercive/residual estimate with
  surjectivity justified by self-adjointness; excluding eigenvectors
  alone is insufficient when essential spectrum is possible.
- [ ] First try isolated finite defects below the bulk enclosure,
  finite-block certificates and controlled exterior coupling
  (e.g. a Schur complement or a suitable barrier estimate).
  Prove that unwanted defect states do not enter the chosen windows.
  If this fails, revise the potential or patch construction rather
  than presupposing the gap. Internal bulk gaps are a later option.

## L9.5 — Independent local controls

- [ ] Transfer each first-ring onsite control R_j and eight-edge
  matching M_j to the verified translated patch, and prove the
  exact reducing-plane action and operator norm estimates.
- [ ] Prove each control annihilates every other encoded plane and
  that the full family of planes and common exterior reduce all
  ideal Hamiltonians. Spatial disjointness alone is not sufficient
  unless the complete operator action is checked.
- [ ] Derive explicit joint control budgets guaranteeing separation
  of each active pair from the other pairs and full exterior,
  for concurrent as well as sequential settings if attainable.

## L9.6 — Protected arbitrary-target preparation

- [ ] Transfer the three-pulse Euler construction to each pair,
  starting from its dark state and reaching any normalized complex
  target up to a local common phase.
- [ ] Prove exact normalization, continuous full-space trajectories,
  Schrödinger equations on open pulse intervals and zero leakage
  throughout, including switches. Establish a schedule with
  arbitrarily weak controls and any prescribed fraction strictly
  between zero and one of each certified gap retained.
- [ ] Show that preparing one encoded plane leaves the other
  encoded rays unchanged. If simultaneous preparation is proved,
  distinguish relative phases between different planes from
  phases internal to each plane. A sequential schedule suffices
  for the first milestone.

## L9.7 — Switch-off and storage

- [ ] Prove that both levels of each pair coincide again at E_j
  when its ideal controls are off, with no residual control.
- [ ] Prove that each prepared ray is stationary under the rest
  Hamiltonian, up to exp(−i E_j t). Different E_j can generate
  relative phases between planes in a global direct-sum state.
  This is ideal storage, not a noise-resilience theorem.

## L9.8 — Arbitrary finite architecture

- [ ] Extend the construction and full-spectrum certificates to
  any finite N, with explicit patch placement, rest energies,
  potentials, gaps and control budgets.
- [ ] Consolidate the exact two-pair result first, then generalize
  only after all assumptions are discharged on the actual graph.
  Reuse the existing Lean proofs where applicable; verify new
  results with full Lean/Mathlib checks and independent statement
  comparison before considering a separate registry candidate.
- [ ] Assess related literature and independent research interest;
  do not infer novelty from formal verification.

## Working order and boundaries

L9.1 is complete for the stated real spectral problem (§4.112). The next mathematical task is L9.2, recurrence of the exact compact-mode patches. A rigorous two-pair construction with full-spectrum isolation remains the first multi-pair target. A plateau
allows essential spectrum but does not guarantee spectral gaps, and
the five previous theorems do not establish L9. Preserve Track A's
analytic-product infrastructure: its compact-resolvent and summability
hypotheses may not hold for this new model. Do not transfer them without
new proofs. The first research deliverable, the separate bounded Lean model and its spectral certificates, is verified. The sixth result is registered; publication of a software release is a separate action.
