[← Main README and table of contents](../README.md)

## Research tracks and current priority

The project has **two complementary research tracks**, not a replacement
of its original goals:

| Track | Question | Status and next steps |
| --- | --- | --- |
| **A — Spectral geometry and analytic zeros (original program)** | How do local changes affect the full infinite-operator spectrum and the zeros of its canonical products? | Extensive formal results (§§2–4, 6.1–6.4); open cofactor and isolation certificates, relative determinant identities, certified finite-patch estimates and exploratory zero statistics (§§6.3, 6.5–6.7). |
| **B — Localized modes and coherent control (emergent program)** | Can local graph controls manipulate the dark/bright states of the same infinite Hamiltonian? | L1–L5 verified; L5 registered. **L7 registered.** **L7a complete** (§§4.99–4.100); **L7b complete at the algebraic level** (§§4.100–4.101): exact matrix, full Lie generation and constructive Euler state reachability. **L7c.1–4 complete for compact-plane preparation** (§§4.102–4.105): exact single-axis trajectories, phase-weighted rotations, continuous three-pulse dynamics and arbitrary normalized target preparation from dark up to global phase, with zero leakage at all times. General full-space complex dynamics remain open. **L8a.1 is verified** (§4.106): exact control norms and bounded decomposition. **L8a.2 is verified** (§4.107): exact plane energies and natural-domain reduction. **L8a.3 is verified** (§4.108): quantitative exterior exclusion in the full real spectrum. **L8a.4 is verified** (§4.109): explicit positive cluster isolation under small ideal controls. **Centered spectral protection is registered** (§4.110): a larger sufficient control region and stronger gap. **Exact protected preparation with arbitrarily weak controls is Lean-verified** (§4.111); independent candidate comparison is separate. Further refinements and robustness questions remain open (§6.9). The original **L6** single-edge approximate control is kept for later. |

Track B emerged from the verified graph geometry and spectral splitting,
but quantum control is **not a prerequisite** for completing Track A.
L7 now proves exact normalized target preparation from dark under coordinated controls; the distinct L6 single-edge approximate preparation theorem remains open.
L8a's static protection objective is verified (§§4.106–4.110), including a stronger centered estimate. The spectral-protection result passed independent statement verification and was registered on 26 November 2026 as [PALOMAR-2026-11-26-000015 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000015&version=1). Variable-duration preparation with simultaneous energetic protection is now Lean-verified (§4.111). Further refinements and imperfect controls remain research directions (§6.9).
See the [localized-mode control roadmap](bright-spectral-splitting-roadmap.md)
and the preserved [single-edge research note](edge-control-reachability.md).
The detailed Lean-module catalogue and all existing theorem descriptions
remain accessible from the [main table of contents](../README.md#table-of-contents).

