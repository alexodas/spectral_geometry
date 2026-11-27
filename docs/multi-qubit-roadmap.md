[← Main README and table of contents](../README.md) · [Track B roadmap](bright-spectral-splitting-roadmap.md) · [Research roadmap §6.10](research-roadmap.md#610-l9--independently-controllable-spectrally-protected-localized-qubits-open)

# L9 — Independently controllable spectrally protected localized qubits

**Status: proposed research, not yet proved.** This is the active Track B
direction. Track A (spectral geometry and analytic zeros), the original
L6 single-edge approximate preparation, and L8b–L8e imperfect-control
research are preserved but deferred. All five Palomar registrations and
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

- [ ] Introduce a separate bounded onsite potential
  V_R(x) = 1 + min(|p(x)|², R²), with plateau C = 1 + R²,
  preserving the original definitions and the central first-ring
  crossing correction t* = 17/16 + sqrt(2).
- [ ] Choose R large enough to preserve both central compact-mode
  equations; distinguish preservation of those eigenvectors from
  preservation of the original exact multiplicity and gap.
- [ ] Prove boundedness, symmetry/self-adjointness and the full
  bounded-inverse spectral interface (including complexification if
  needed). The original compact-resolvent and eigenvalue-exhaustion
  arguments cannot be assumed for this bounded model.
- [ ] Establish the bulk enclosure sigma(C I + B) ⊆ [C,C+1] using the
  verified positivity and norm bound of the interaction B. Prove the
  appropriate finite-rank perturbation/essential-spectrum statements
  if needed; do not assume that the bulk fills the interval or is
  absolutely continuous.

## L9.2 — Recurrence of compact-mode patches

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

Start with L9.1 and L9.2; a rigorous two-pair construction with
full-spectrum isolation is the first substantive target. A plateau
allows essential spectrum but does not guarantee spectral gaps, and
the five previous theorems do not establish L9. Preserve Track A's
analytic-product infrastructure: its compact-resolvent and summability
hypotheses may not hold for this new model. Do not transfer them without
new proofs. The first research deliverable is a separate Lean model and
verified statements, not a new Palomar registration or release.
