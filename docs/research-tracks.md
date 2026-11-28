[← Main README and table of contents](../README.md)

## Research tracks and current priority

The project has **two complementary research tracks**, not a replacement
of its original goals:

**Current research priority:** Track B, specifically the new [L9 multi-qubit
architecture roadmap](multi-qubit-roadmap.md). Track A is paused, not
cancelled; all its verified results and open objectives are retained.
L6 and imperfect-control refinements L8b–L8e are deferred while L9 is explored.

| Track | Question | Status and next steps |
| --- | --- | --- |
| **A — Spectral geometry and analytic zeros (original program)** | How do local changes affect the full infinite-operator spectrum and the zeros of its canonical products? | **Paused.** Extensive formal results (§§2–4, 6.1–6.4); open cofactor and isolation certificates, relative determinant identities, certified finite-patch estimates and exploratory zero statistics (§§6.3, 6.5–6.7). |
| **B — Localized modes and coherent control (emergent program)** | Can local graph controls manipulate the dark/bright states of the same infinite Hamiltonian? | L1–L5 verified; L5 registered. **L7 registered.** **L7a complete** (§§4.99–4.100); **L7b complete at the algebraic level** (§§4.100–4.101): exact matrix, full Lie generation and constructive Euler state reachability. **L7c.1–4 complete for compact-plane preparation** (§§4.102–4.105): exact single-axis trajectories, phase-weighted rotations, continuous three-pulse dynamics and arbitrary normalized target preparation from dark up to global phase, with zero leakage at all times. General full-space dynamics for the original unbounded confined model remain open; bounded plateau evolution is now constructed (§4.117). **L8a.1 is verified** (§4.106): exact control norms and bounded decomposition. **L8a.2 is verified** (§4.107): exact plane energies and natural-domain reduction. **L8a.3 is verified** (§4.108): quantitative exterior exclusion in the full real spectrum. **L8a.4 is verified** (§4.109): explicit positive cluster isolation under small ideal controls. **Centered spectral protection is registered** (§4.110): a larger sufficient control region and stronger gap. **Exact protected preparation with arbitrarily weak controls is registered** (§4.111); all 19 selected propositions passed independent comparison. Further refinements and robustness questions remain open (§6.9); **L9.1 is registered** (§4.112): bounded plateau, exact double eigenvalue, full real gap ≥ 1/122 and finite-rank defect; all 13 selected propositions passed independent comparison. Registered on 27 November 2026 as [PALOMAR-2026-11-27-000042 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-27-000042&version=1). **L9 remains the active research priority** (§6.10); L9.2 recurrence and exact orthogonal compact-mode replication are Lean-verified, independently compared and registered (§4.113; [PALOMAR-2026-11-27-000067 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-27-000067&version=1)); L9.3 exact local completeness of the natural nondegenerate A/B pairs on the existing plateau is Lean-verified for the seventeen-site recurrent cells. L9.4 infinite multiplicity and the obstruction to individual gaps, L9.5 spatially selective reduction, L9.6 simultaneous exact preparation for arbitrary finite families and L9.7 bounded evolution with finite-time leakage and retention estimates are Lean-verified ([§§4.114–4.118](natural-plateau-architecture.md)). Collective spectral gaps, weak-control refinements and long-time robustness remain open. The engineered distinct degenerate energies remain a deferred alternative. The original **L6** single-edge approximate control is kept for later. |

Track B emerged from the verified graph geometry and spectral splitting,
but quantum control is **not a prerequisite** for completing Track A.
L7 now proves exact normalized target preparation from dark under coordinated controls; the distinct L6 single-edge approximate preparation theorem remains open.
L8a's static protection objective is verified (§§4.106–4.110), including a stronger centered estimate. The spectral-protection result passed independent statement verification and was registered on 26 November 2026 as [PALOMAR-2026-11-26-000015 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000015&version=1). Variable-duration preparation with simultaneous energetic protection is Lean-verified and independently compared (§4.111). Registered on 27 November 2026 as [PALOMAR-2026-11-27-000003 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-27-000003&version=1). Palomar mechanical verification and Challenge renderability passed, and the automated editorial review identified no blocking problem. Further refinements and imperfect controls remain research directions (§6.9).
See the [localized-mode control roadmap](bright-spectral-splitting-roadmap.md)
and the preserved [single-edge research note](edge-control-reachability.md).
The detailed Lean-module catalogue and all existing theorem descriptions
remain accessible from the [main table of contents](../README.md#table-of-contents).

