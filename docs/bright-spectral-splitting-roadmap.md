# Dark–bright spectral splitting and control — Lean research roadmap

[Main README](../README.md) · [General roadmap](research-roadmap.md) · [Active L9 roadmap](multi-qubit-roadmap.md) · [Historical control roadmap](bright-spectral-splitting-roadmap-history.md)

**Deferred research.** L9 is the current Track B priority. The completed L1–L5 splitting, L7 exact preparation and L8a ideal protection are recorded in [§§4.80–4.98](single-edge-control.md), [§§4.99–4.111](coordinated-quantum-control.md) and [verified milestones](verified-milestones.md). This roadmap retains only unresolved refinements and the original L6 path. General full-space dynamics for the unbounded confined model are distinct from the now-proved bounded plateau evolution.

<a id="6-l7--exact-two-mode-preparation-without-leakage-verified"></a>

## 6. L7 — Remaining full-space dynamics and minimal-control questions

The exact plane preparation theorem is complete. The following extensions remain.

- [ ] Construct the general complex Hilbert-space model and unitary
      full-space propagators; distinguish the explicit plane trajectories
      from evolution for arbitrary infinite-space initial data.
- [ ] Optional later question: determine whether fewer than eight edges
      can realize a nontrivial exact phase control. No minimality claim
      is made yet.

## 7. Preserved original direction: L6 — single-edge approximate control (DEFERRED, NOT CANCELLED)

The original single-edge and ring-parameter protocol is a distinct objective. Preserve the [research note](edge-control-reachability.md) and prove the dynamical dark-occupation constraint and controlled bright mixing; conditional leakage estimates are not a propagator theorem.

- [ ] Construct the full complex unitary dynamics and switch-on/off
      sequences for the original one-edge perturbation.
- [ ] Give a precise target-state preparation theorem with controlled
      phases and amplitudes, stated in a norm or fidelity metric and
      with explicit pulse-strength/length dependence.
- [ ] Prove the leakage/error budget for the complete finite pulse
      sequence, including any residual state after restoring the
      unperturbed Hamiltonian.
- [ ] Compare L6 versus L7: number of independently changed edges,
      admissible control strengths, pulse cost and leakage. Neither
      exact controllability for L6 nor an optimality assertion for L7
      is presently established.

<a id="8-l8--robustness-of-the-embedded-qubit-open"></a>

## 8. L8 — Deferred imperfect-control robustness

<a id="l8a--quantitative-spectral-protection-under-coordinated-controls-verified-refinements-open"></a>

- [ ] Investigate further sharp bounds and imperfect control dynamics.
- [ ] Develop bounds for nonuniform control errors and leakage, preparation fidelity, and robust pulse design (L8b–L8e). Distinguish sufficient static protection from dynamical robustness.

## Historical references

<a id="1-established-starting-point"></a>

[1. Established starting point](bright-spectral-splitting-roadmap-history.md#1-established-starting-point)

<a id="2-quantitative-real-point-spectrum-splitting-l1l5-verified"></a>

[2. Quantitative real point-spectrum splitting: L1–L5 verified](bright-spectral-splitting-roadmap-history.md#2-quantitative-real-point-spectrum-splitting-l1l5-verified)

<a id="3-proof-milestones-ordered-by-dependency"></a>

[3. Proof milestones, ordered by dependency](bright-spectral-splitting-roadmap-history.md#3-proof-milestones-ordered-by-dependency)

<a id="4-efficient-lean-development-sequence"></a>

[4. Efficient Lean development sequence](bright-spectral-splitting-roadmap-history.md#4-efficient-lean-development-sequence)

<a id="5-l5-palomar-candidate-editorial-feedback-and-correction"></a>

[5. L5 Palomar candidate, editorial feedback and correction](bright-spectral-splitting-roadmap-history.md#5-l5-palomar-candidate-editorial-feedback-and-correction)

<a id="l7a--exact-invariant-plane-algebra-complete"></a>

[L7a — exact invariant-plane algebra (COMPLETE)](bright-spectral-splitting-roadmap-history.md#l7a--exact-invariant-plane-algebra-complete)

<a id="l7b--exact-effective-controls-and-reachability-algebra-complete-algebraically"></a>

[L7b — exact effective controls and reachability algebra (COMPLETE ALGEBRAICALLY)](bright-spectral-splitting-roadmap-history.md#l7b--exact-effective-controls-and-reachability-algebra-complete-algebraically)

<a id="l7c--exact-complex-compact-plane-preparation-verified"></a>

[L7c — exact complex compact-plane preparation (VERIFIED)](bright-spectral-splitting-roadmap-history.md#l7c--exact-complex-compact-plane-preparation-verified)

The historical document preserves the complete earlier proof milestones, candidate feedback, corrections, and registrations.
