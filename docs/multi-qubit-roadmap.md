[← Main README and table of contents](../README.md) · [Research roadmap §6.10](research-roadmap.md#610-l9--independently-controllable-spectrally-protected-localized-qubits-open) · [Track B roadmap](bright-spectral-splitting-roadmap.md) · [Historical L9 roadmap](multi-qubit-roadmap-history.md)

# L9 — Independently controllable spectrally protected localized qubits

**Active priority.** Investigate how far the unchanged canonical plateau can support independently addressable localized two-state systems without additional static remote wells. Collective spectral protection and robustness are open; an individual gap from equal-energy replicas is impossible. The proved architecture is a direct sum of orthogonal subspaces of a single-particle space, not a tensor product. See [§§4.112–4.118](natural-plateau-architecture.md) and [verified milestones](verified-milestones.md) for completed results. The original Track A, L6 and L8b–L8e objectives remain paused or deferred.

## Motivation and target architecture

Prioritize natural nondegenerate remote pairs on the existing plateau. Do not require engineered degeneracy unless a necessary objective cannot be met by the natural architecture. The central isolated double eigenvalue remains unchanged. L9.1 and L9.2 are completed and retained in [§4.112](plateau-spectral-isolation.md), [§4.113](compact-patch-recurrence.md) and the historical roadmap, not in the active checklist.

<a id="l93--natural-plateau-pairs-exact-energies-and-local-completeness"></a>

## L9.3 — Larger compact-support geometry

The seventeen-site classification is complete. The remaining geometry task concerns larger supports.

- [ ] As a secondary geometry question, enumerate the next graph-distance shells and their full degrees, then test for other compact modes with exact boundary cancellation. A uniform degree alone does not establish an eigenvector. Treat exploratory calculations as unverified until proved.

<a id="l94--spectral-environment-and-the-limits-of-protection"></a>

## L9.4 — Collective spectral environment

The same two natural energies have infinite multiplicity. Individual residual gaps are ruled out, and any collective residual bound is at most 1/16. No positive collective gap has been proved.

- [ ] Distinguish the exact internal level splitting 1/16 from spectral gaps. Determine whether E_A and E_B are isolated spectral points of infinite multiplicity, embedded or accumulation points; investigate gaps between or around them and the distance to the spectrum outside their **full** eigenspaces. No positive collective gap is assumed.
- [ ] Study the uniform bulk L and C I + L, the full canonical H_C and the finite-rank central defect separately. Establish any required essential-spectrum or bounded-inverse claims rigorously; the enclosure [C,C+1] does not imply an interval of spectrum or absence of internal gaps.
- [ ] Where appropriate, use exact local residuals, rigorous finite-region bounds, and full-space estimates with justified invertibility. Numerical spectra can guide conjectures but cannot certify absence of spectrum on the infinite graph.
- [ ] Identify what protection is available through exact local reducing planes even if a global gap is impossible for an individual cell. If a collective spectral gap exists, determine its scope and whether controls preserve it.

<a id="l95--local-addressing-without-additional-static-wells"></a>

## L9.5 — Control strength and protection refinements

Ideal independent spatial addressing and finite-family reduction are proved. Energy selectivity is not required for those ideal protocols; what remains is quantitative refinement under spectral or nonideal constraints.

- [ ] Assess control strengths and any attainable protection against rigorously certified spectral bounds; analyze departures from ideal spatial selectivity.

<a id="l96--exact-preparation-under-the-natural-energy-splitting"></a>

## L9.6 — Weak-control preparation refinements

Exact simultaneous finite-family preparation is proved with the natural rest drift included. Arbitrarily weak controls on the remote pairs are not established.

- [ ] Investigate arbitrary weakness of controls, pulse durations and any attainable spectral protection separately. Do not transfer the fifth registered theorem's prescribed gap fraction without proving appropriate hypotheses.

<a id="l97--free-evolution-storage-and-perturbations"></a>

## L9.7 — Storage and perturbation refinements

Ideal free evolution and bounded finite-time perturbation estimates are proved. The remaining questions concern practical mathematical storage strategies and stronger robustness.

- [ ] Study known-phase tracking, refocusing or other storage strategies if needed. Compare the uniform-zero-potential model with the canonical plateau, retaining the central defect distinction.
- [ ] Investigate concrete onsite disorder, edge perturbations, imperfect addressing and mixing among equal-energy replicas; determine whether stronger or long-time bounds hold.
- [ ] Identify concrete obstructions, and only then consider the smallest additional static local intervention that resolves them. A plateau or a tuned well is not assumed necessary for remote control.

<a id="l98--arbitrary-finite-natural-architecture-and-decision-point"></a>

## L9.8 — Architecture decision and research assessment

Arbitrary finite direct-sum preparation is proved. Registry review and scientific assessment are separate from proof verification.

- [ ] Compare the natural nondegenerate architecture against the alternative engineered architecture below, based on proved results rather than assumed requirements. If an essential objective fails, investigate minimal modifications before pursuing distinct degenerate rest energies.
- [ ] Complete registry review and examine related literature without claiming priority or hardware feasibility.

## Alternative architecture — engineered degenerate rest energies (deferred)

The previous L9.3–L9.8 proposal is retained here in full. Its individual spectral isolation and stationary-ray storage targets are stronger and different from exact local addressing in the natural plateau. Pursue this route if the natural architecture proves insufficient for the chosen application, not by default.

![Conceptual energy diagram of two individually protected localized qubits below the bulk spectral enclosure](figures/l9-two-protected-qubits.svg)

*Figure — Alternative engineered target, not yet proved: two degenerate pairs at distinct rest energies below the bulk enclosure, with individual positive spectral windows. This is not the energy diagram of the current natural plateau pairs.*

### Alternative L9.3 — Two degenerate pairs at distinct rest energies

- [ ] Construct central and remote pairs with disjoint support and
  energies E_0 ≠ E_1. For a translated A/B patch, a candidate onsite
  assignment on the two rings is E_j−3/16 and E_j−1/4, respectively.
  Prove the full eigenvector equations, not just compressed ones.
- [ ] Explore choosing E_j below C with appropriate local wells and
  exterior barriers; keeping a pure plateau without local tuning
  cannot in general produce the desired distinct degenerate pairs.
- [ ] Preserve the original central energy E_0 = 13/4 + sqrt(2)
  if possible. The chosen construction must be justified, not assumed.

### Alternative L9.4 — Individual full-spectrum isolation

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

### Alternative L9.5 — Independent local controls

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

### Alternative L9.6 — Protected arbitrary-target preparation

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

### Alternative L9.7 — Switch-off and storage

- [ ] Prove that both levels of each pair coincide again at E_j
  when its ideal controls are off, with no residual control.
- [ ] Prove that each prepared ray is stationary under the rest
  Hamiltonian, up to exp(−i E_j t). Different E_j can generate
  relative phases between planes in a global direct-sum state.
  This is ideal storage, not a noise-resilience theorem.

### Alternative L9.8 — Arbitrary finite architecture

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

Prioritize L9.4, then weak controls and robustness in L9.5–L9.7; pursue larger-support geometry as a secondary question. Revisit the engineered route only if a necessary requirement fails on the natural plateau. Do not transfer compact-resolvent hypotheses from the confined model to the bounded model, or equate direct-sum systems with tensor-product qubits.

## Historical references

<a id="l91--bounded-plateau-model"></a>

[L9.1 — Bounded plateau model (completed)](multi-qubit-roadmap-history.md#l91--bounded-plateau-model)

<a id="l92--recurrence-of-compact-mode-patches"></a>

[L9.2 — Recurrence of compact-mode patches (completed)](multi-qubit-roadmap-history.md#l92--recurrence-of-compact-mode-patches)

The [complete historical roadmap](multi-qubit-roadmap-history.md) preserves all earlier results, figures, and checklists.
