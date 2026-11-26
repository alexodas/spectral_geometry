[← Main README and table of contents](../README.md)

<details>
<summary>Contents of this document</summary>

- [6.1. P2 — Spectral foundations and the complex-resolvent interface](#61-p2--spectral-foundations-and-the-complex-resolvent-interface)
- [6.2. P2 — Quantitative observation and control of low-energy levels](#62-p2--quantitative-observation-and-control-of-low-energy-levels)
- [6.3. P3 — Full spectral products and their exact zero divisors](#63-p3--full-spectral-products-and-their-exact-zero-divisors)
- [6.4. P4 — A confined Ammann–Beenker model and a finite intervention](#64-p4--a-confined-ammannbeenker-model-and-a-finite-intervention)
- [6.5. Local geometric defects and relative spectral products](#65-local-geometric-defects-and-relative-spectral-products)
- [6.6. Certified finite-patch approximation and zero response](#66-certified-finite-patch-approximation-and-zero-response)
- [6.7. Exploratory objectives: zero statistics and structural constraints](#67-exploratory-objectives-zero-statistics-and-structural-constraints)
- [6.8. Independent statement verification and research-interest assessment](#68-independent-statement-verification-and-research-interest-assessment)
- [6.9. L8a — Quantitative spectral protection under coordinated controls (verified; refinements open)](#69-l8a--quantitative-spectral-protection-under-coordinated-controls-verified-refinements-open)

</details>

## 6. Roadmap: proof status and next steps

**The original goal remains unchanged:** obtain quantitative response
theorems for zeros of canonical products associated with explicitly
specified geometric interventions on infinite operators. The finite-site
observation theorem (§4.40), abstract response results, full spectral
products and the confined Ammann–Beenker application establish much
of its formal infrastructure.

**Two complementary lines of work are now tracked explicitly:**

1. **Track A — spectral geometry and analytic zeros.** The verified
   foundations and product-response work are recorded in §§6.1–6.4;
   the main remaining goals are numerical cofactor/isolation
   certificates for the interacting geometric product (§6.3),
   finite-rank relative determinants (§6.5), certified finite-patch
   approximations (§6.6), and optional exploratory zero statistics
   (§6.7). Their validity and priority do not depend on solving
   quantum control.
2. **Track B — localized dark/bright modes and control.** The full
   infinite-graph crossing and isolation (§§4.78–4.79) and
   quantitative L1–L5 splitting (§§4.93–4.97) are verified.
   **L7a is verified (§§4.99–4.100):** the eight matched edges
   preserve the entire original dark–bright plane exactly under both
   controls. **L7b is complete algebraically (§§4.100–4.101):** full
   su(2) generation and constructive matrix reachability from dark.
   L7c.1–4 verify exact single-axis trajectories, phase-weighted rotations,
   continuous three-pulse dynamics and arbitrary normalized target preparation
   from dark with zero leakage (§§4.102–4.105). General complex unitary
   evolution remains open. **L6 remains the deferred original
   single-edge approximate-control program**, not a cancelled goal.
   **L8a.1 is verified (§4.106):** exact full-space control norms and bounded decomposition. **L8a.2 is verified (§4.107):** exact controlled plane energies and natural-domain reduction. **L8a.3 is verified (§4.108):** exterior exclusion and real-spectrum characterization. **L8a.4 is verified (§4.109):** positive cluster isolation under explicit small controls. The stronger centered estimate is verified (§4.110); further refinements and imperfect control dynamics remain open (§6.9).
   The [detailed control roadmap](bright-spectral-splitting-roadmap.md)
   separates these tasks and their proof obligations.

**Research status and verification.** L5 is registered as described in §4.98.
L7a, L7b and L7c.1–4 are Lean-verified (§§4.99–4.105); the final preparation theorem and supporting locality certificates have passed independent statement comparison and are registered as [PALOMAR-2026-11-25-000001 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-25-000001&version=1).
The L7 exact zero-leakage preparation theorem from dark is proved.
A general complex quantum propagator and the distinct L6 reachability
theorem remain open. Earlier conditional time-uniform leakage bounds
retain their separate scope. The centered spectral-protection result
(§4.110) passed independent comparison and was registered on
26 November 2026 as [PALOMAR-2026-11-26-000015 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000015&version=1). The subsequent variable-duration preparation theorem with prescribed energetic protection is Lean-verified (§4.111); all 19 selected candidate propositions have passed independent comparison (§6.9). Separate registry verification remains pending.

A checked item below denotes an actual substantive Lean result
under its stated hypotheses; an unchecked item is an open task.
P2, P3 and P4 are research phases, not numbered new theorems.
All historical verified results and the complete §5 Lean-module
catalogue are retained.

### 6.1. P2 — Spectral foundations and the complex-resolvent interface

**Formalized foundations**

- [x] Define the natural onsite domain, prove its density and establish
  closedness and adjoint characterizations for the relevant operators
  (§§4.1–4.2, 4.13–4.15).
- [x] Construct bounded infinite matching interactions and their energy and
  norm bounds (§§4.6–4.12).
- [x] Prove self-adjointness in Mathlib's partial-operator API and compact
  shifted resolvents under the explicit properness, gap, symmetry and
  bounded-correction hypotheses (§§4.16–4.22).
- [x] Connect full-operator eigenvectors with compact-resolvent eigenspaces;
  prove finite geometric multiplicity, orthogonality and completeness in
  the self-adjoint setting (§§4.23–4.27).
- [x] Identify the real bounded-inverse spectrum with genuine real
  eigenvalues, with isolation, local finiteness and countability
  (§§4.28–4.32).
- [x] Prove positive multiplicity, exact multiplicity-tagged coverage and
  completeness indexed by real spectral levels (§§4.33–4.35).
- [x] Construct sorted finite spectral windows and a globally ordered,
  exact, injective infinite tag enumeration; prove qualitative divergence
  under the stated lower-bound and infinitude hypotheses (§§4.36–4.38).

**Open complex-resolvent interface for relative products (§6.5)**

- [ ] Construct the required complexification and complex shifted inverse
  on the natural domain, and relate it to the verified real spectral data.
- [ ] Prove the resolvent identities, analyticity and compression facts
  needed to define $G_S(z)$. The real completeness theorem is not by
  itself this complex-resolvent interface.
- [x] Establish infinitude and a positive lower bound before invoking the
  infinite enumeration for the explicit octagonal vertex graph (§§4.68–4.70).
  Finite and empty models continue to use the separate existing interfaces.

### 6.2. P2 — Quantitative observation and control of low-energy levels

**Formalized inputs**

- [x] Bound the full quadratic form relative to onsite multiplication by
  $\|B\|\|\psi\|^2$, and obtain a positive real-spectrum gap under the
  explicit hypotheses of §4.39.
- [x] Prove finite-coordinate detection and an injective restriction on
  each complete low-energy eigenspace, yielding its geometric
  multiplicity bound (§4.40).
- [x] Establish inverse-square summability for suitable linearly or
  power-law growing onsite-only levels (§§4.4–4.5).

**Verified simultaneous observation and spectral comparison (§§4.41–4.46)**

Assume the self-adjoint compact-resolvent setting, $V(t)\ge v_0$,
$C=\|B\|$, $R>v_0$, and $E<R-C$. Set
```math
F_R=\{t:V(t)\le R\},
\qquad
\kappa=\frac{R-C-E}{R-v_0}>0.
```

- [x] Strengthen the existing eigenspace restriction theorem to the
  quantitative estimate
  ```math
  \|P_{F_R}\psi\|^2\ge\kappa\|\psi\|^2
  ```
  for the entire spectral subspace below or at $E$, including linear
  combinations from distinct levels. Verify the domain, finite-dimensional
  and spectral-subspace hypotheses explicitly.
- [x] Derive the multiplicity-aware counting bound
  ```math
  \sum_{\substack{\lambda\in\sigma_{\mathrm{real}}(H)\\
                   \lambda<R-\|B\|}}m_H(\lambda)
  \le\#\{t:V(t)\le R\}.
  ```
  The separate bounds on individual eigenspaces in §4.40 cannot simply be
  summed to obtain it.
- [x] Connect the exact ordered enumeration to a variational/counting
  principle and prove
  ```math
  v_n-\|B\|\le\lambda_n(H)\le v_n+\|B\|,
  ```
  for onsite levels $v_n$ and full levels ordered with the same
  multiplicity convention. Exploit a nonnegative Laplacian to sharpen
  the lower bound where applicable.

**Verified finite-sector response and sufficient summability (§§4.46–4.48)**

- [x] For $H_\tau=H+\tau P_{F_R}$, prove
  ```math
  \kappa\tau
  \le\lambda_n(H_\tau)-\lambda_n(H)
  \le\tau,
  \qquad
  \lambda_n(H)\le E,\quad 0\le\tau\le R-v_0.
  ```
  The proof controls ordered levels with multiplicities and does not
  assume simple eigenvalues. The verified form-comparison route establishes
  ```math
  H\ge(R-C)I-(R-v_0)P_{F_R}
  ```
  on the natural domain and applies the proved variational comparison.
- [x] Transfer sufficient quantitative onsite growth to the ordered full
  eigenvalues and prove full-spectrum inverse-square summability.
  Positivity must also be verified; compact resolvent alone is insufficient.
- [x] Preserve the required positive gap and summability for nonnegative
  finite-sector perturbations, and prove existence of the ordered spectra
  throughout the response interval. Self-adjointness and compact shifted
  inverses are supplied by §§4.47–4.48; the resolvent shift may vary with the
  parameter.

**Verified signed-error extension, onsite ordering and positive interactions**

- [x] Preserve a supplied positive gap and inverse-square summability for
  symmetric bounded perturbations of either sign with $\|K\|<\gamma$,
  where $\gamma$ is the baseline gap (§4.55). Section 4.56 derives complete
  perturbed spectra and exact products under its sufficient onsite
  hypotheses. This includes small signed finite-support interventions;
  it does not cover errors exceeding the verified gap.
- [x] Derive a sorted onsite site bijection from finite onsite sublevel
  sets on an infinite site type (§4.57), including repeated onsite energies.
  Existing comparison/transfer APIs may still accept the bijection as an
  input; the existence obligation is now proved. The construction is
  noncomputable and does not enumerate finite or empty types by $\mathbb N$.
- [x] Package the sharper positive-interaction comparison with its gap and
  summability argument (§4.58). For symmetric nonnegative bounded $B$,
  $V\ge v_0>0$, properness and onsite inverse-square summability give the
  gap $v_0$ and summability of the full spectrum, without $v_0>\|B\|$.
  The matching-Laplacian corollary constructs the ordered spectrum under
  the existing involution and nonnegative-weight hypotheses.
- [x] Prove the stronger sector form bound and response for nonnegative
  interactions:
  ```math
  H\ge R I-(R-v_0)P_F,\qquad
  \frac{R-E}{R-v_0}\,\tau
  \le\lambda_n(H+\tau P_F)-\lambda_n(H)\le\tau.
  ```
  Here $R>v_0$, $\lambda_n(H)\le E<R$, $0\le\tau\le R-v_0$, and
  $V\ge R$ outside the finite sector. The positive-interaction family
  preserves its gap and summability for all $\tau\ge0$; the quantitative
  response retains the stated interval. Section 4.59 transfers this
  stronger estimate to the actual indexed full-product zeros.

**Scope of the verified statements.** The norm comparison and growth transfer
use a sorted bijection of the onsite sites, now supplied by §4.57 under
properness and infinitude. Ordered full levels
come from complete domain eigenbases; §4.44 connects the original exact tags,
and §4.47 derives their existence for infinite site types, proper lower-bounded
$V$ and symmetric bounded corrections. The sufficient positive-summability
package of §4.48 uses $v_0>\|B\|$ and summable onsite inverse squares (or the
proved power-growth criterion). The positive-interaction alternative in
§4.58 only requires the positive onsite lower bound $v_0>0$, together with
properness and onsite summability. Finite/empty cases are covered by observation, counting
and tag bases; the $\mathbb N$-sequence statements explicitly address the
infinite case.

This phase now supplies a proved abstract consequence of finite observation:
a finite onsite intervention has a controlled effect on every selected low
ordered level. Sections 4.52 and 4.59 transfer the respective norm-penalty and
positive-interaction responses to the indexed zeros of both full spectral
products. All the listed abstract obligations of this subsection are proved
under their stated hypotheses. Sections 4.68–4.70 now establish an explicit
vertex graph and a nonempty nine-level window for §6.4. Sections 4.71–4.72
now prove geometric summability and exact full-product zero response. Local scalar analytic
certificates and exact disk counts are now available in §6.3, together
with a numerical worked onsite certificate and quantitative tails for its
nonnegative interacting family (§§4.66–4.67). Interacting geometric
cofactor/radius data and finite-patch approximation certificates remain
open in §§6.3 and 6.6; noncircular contours are not covered by the disk theorem.
The concrete full-product theorem of §4.72 uses this spectral infrastructure;
analytic-product consequences have their own hypotheses.

### 6.3. P3 — Full spectral products and their exact zero divisors

**Verified analytic package**

- [x] Construct entire normalized paired products from positive levels
  with summable inverse squares; identify all zeros and their exact
  geometric spectral multiplicities, with fixed $c,d$, $d\ne0$
  (§§2.4, 4.49, 4.51). The prescribed line is part of the definition.
- [x] Transfer finite-sector response to indexed full-product zeros,
  including repeated levels and the positive-interaction coefficient
  $(R-E)/(R-v_0)$ (§§4.50–4.52, 4.59). The abstract theorem remains
  conditional on the selected baseline level being below $E$.
- [x] Certify separated zero windows under independently bounded operator
  errors, preserving total multiplicity with boundary exclusion
  (§§4.53–4.56), including empty windows and repeated levels.
- [x] Prove scalar truncation-error bounds, local cofactor-based location
  estimates and exact disk counts for analytic approximants
  (§§4.60–4.65). Rouché gives count $m$ under
  $\varepsilon<C\rho^m$; sufficiently long exact partial products qualify.
  The disk case includes zero-free disks and several or repeated zeros.
- [x] Supply the numerical onsite certificate and linear-growth tail rates
  of §§4.66–4.67: radius $1/4$, cofactor bound $1/5$, sufficient cutoff
  $16384$, truncation error $1/50$, additional boundary budget $1/100$,
  and zero distance at most $3/20$. The tail rates also hold for that
  linear onsite potential with symmetric nonnegative bounded interactions.

**Application-dependent work**

- [x] Instantiate the full-product theorem for the explicit graph of
  §6.4, with geometric summability and a nine-level zero-response
  conclusion derived in §§4.71–4.72.
- [ ] Derive numerical cofactor and isolation-radius certificates for
  this interacting geometric product. The linear onsite constants cannot
  be transferred unchanged to it.
- [ ] Extend counting to noncircular contours if an application needs
  them. This does not block §6.4. Finite-patch error certificates remain
  the separate task of §6.6.

### 6.4. P4 — A confined Ammann–Beenker model and a finite intervention

**Relationship to the two research tracks.** This section retains
the full original geometric and spectral-product objectives (Track A),
followed by the newer compact-mode control direction (Track B).
The L7 central control objective is now **verified** (§4.105): arbitrary normalized target preparation from dark up to an explicit global phase with zero leakage throughout. General complex full-space propagation, stronger control theorems, and the distinct L6 program remain open.
The earlier single-edge preparation narrative and its open tasks
remain here as the **preserved, deferred L6 program**; they are not
the present priority and are not already proved.

The application uses the **explicit centered octagonal cut-and-project
vertex graph** of §§4.68–4.70. The lattice projections, open-window
boundary convention and coordinate-step adjacency are defined in Lean.
The relation to the standard Ammann–Beenker construction is documented in
§4.68; a polygonal covering or aperiodicity theorem is not silently assumed.

**Completed geometric and spectral construction**

- [x] Define the accepted integer lifts, injective physical embedding and
  undirected unit-length coordinate edges. Prove infinitude by silver-unit
  inflation and finiteness within every bounded physical radius (§4.68).
- [x] Verify the central star with exactly eight unit-distance neighbors,
  degree at most eight everywhere, and the exact eight-color involutive
  matching representation, with no repeated nontrivial edges (§4.69).
- [x] Construct the full interaction and verify its coordinate formula,
  positivity, symmetry and norm at most one:
  ```math
  (H\psi)(x)=(1+|p(x)|^2)\psi(x)
    +\frac1{16}\sum_{y\sim x}(\psi(x)-\psi(y)).
  ```
- [x] Prove $V\ge1$, properness, finiteness of
  $S=\{x:|p(x)|\le2\}$ and $V\ge5$ outside it. Use the existing
  natural-domain, self-adjoint compact-resolvent construction to obtain
  the ordered full eigenbases (§4.70).
- [x] Prove that the nine central sites have onsite energy at most two;
  the variational comparison gives $\lambda_8(H)\le3$. Construct the
  spectra for $H_\tau=H+\tau P_S$, preserve the lower bound one, and prove
  ```math
  \frac\tau2\le\lambda_n(H_\tau)-\lambda_n(H)\le\tau,
  \qquad n<9,\quad 0\le\tau\le4.
  ```
  This counts multiplicities and supplies a genuinely nonempty window.

**Completed planar counting, summability and full-product application**

- [x] Prove an injective finite-residue planar code and the explicit
  bound $\#\{|p(x)|\le R\}\le25(2\lceil R+3\rceil+1)^2$ for $R\ge0$.
  This supplies the required planar growth bound without assuming or
  proving uniform separation (§4.71).
- [x] Prove $\sum_x(1+|p(x)|^2)^{-2}<\infty$ and transfer it to the
  positive complete interacting spectra throughout $0\le\tau\le4$,
  retaining the lower bound one (§§4.71–4.72).
- [x] Construct entire full products with exact operator-specific
  geometric zero orders and prove indexed displacements between
  $|d|\tau/2$ and $|d|\tau$ for nine slots on each reflected branch,
  including both interval endpoints (§4.72).

**Established ingredients for the next steps**

- [x] Strengthen the existing nine-level response to coefficient
  $4\sqrt2-5$ on $0\le\tau\le3+2\sqrt2$ using the next-shell barrier (§4.73).
- [x] Prove the two compact-state equations, orthogonality and exact
  ring-induced crossing on the infinite natural domain (§§4.74–4.75).
- [x] Prove the stationary state under a one-edge change and the exact
  Rayleigh response of the affected unit direction (§4.75).
- [x] Identify the radius-two sector as exactly the origin and the two
  compact rings; prove its internal adjacency, the ring degrees three and
  four, and the exact count of sixteen edges to the exterior (§4.76).
- [x] Validate the central-block kernel classification and its transfer
  to centrally supported natural-domain eigenvectors (§4.77).
- [x] Derive central support for every crossing eigenvector and prove
  that its two seed amplitudes parametrize the entire natural-domain
  eigenspace, of real dimension exactly two (§4.78).
- [x] Certify the closed real spectral isolation window
  $|E-E_*|\le1/128$ around the exact multiplicity-two crossing, with no
  other point of the full real bounded-inverse spectrum (§4.79).
  This is a conservative bound, not the exact nearest-level spacing.

**Near-term result: quantitative dark/bright spectral splitting (L1–L5 verified)**

The real natural-domain splitting progressed from eigenpair
existence (L2c) to unique simple levels in an isolated window
(L2d), then a full-exterior eigenvector estimate (L3),
a quadratic energy law with constant `112` (L4),
and finally a **strict signed shift** and a single
consolidated full-operator theorem (L5). The remaining
questions concern scientific assessment and separate
dynamical, geometric, and analytic-product research goals.
See the [research roadmap](bright-spectral-splitting-roadmap.md).

- [x] **L1 — Dark simplicity (Lean verified).** For ε ≠ 0 the
  perturbed eigenspace at E_* is exactly the dark line.

- [x] **L2a — Ordered complete eigenbases and norm stability.**
  The true infinite-operator levels obey
  |μₙ − λₙ| ≤ 2|ε| for every index.
- [x] **L2b — Exactly double, consecutive unperturbed crossing.**
  The counting theorem, consecutive-slot lemma and concrete corollary
  establish the exact multiplicity and consecutive positions.
- [x] **L2c — Actual distinct perturbed eigenvalue exists.**
  For every ε ≠ 0 there is a nonzero natural-domain eigenvector
  with energy E_b ≠ E_* and |E_b − E_*| ≤ 2|ε|.
- [x] **L2d — Isolated simple point-spectrum pair.**
  For `0 < |ε| ≤ 1/1024`, the closed `1/256` window contains
  exactly the simple dark energy and one distinct simple moving
  eigenvalue, with `|E_b-E_*| ≤ 2|ε|` (§4.94). This is a
  statement about all genuine natural-domain eigenvectors,
  not an unproved claim about an alternate spectrum definition.
- [x] **L3 — Quantitative bright eigenvector (§4.95).**
  The true moving eigenspace is dark-orthogonal, has a
  nonzero bright amplitude `c`, and satisfies the exact
  full-exterior estimate `‖Qx‖≤256|ε||c|‖QWF‖`
  for `0<|ε|≤1/1024`.
- [x] **L4 — True bright energy law (§4.96).**
  The full-graph bright amplitude identity, exact exterior
  coupling and sharp L3 estimate prove
  `|E_b(ε) − (E_* + ε/4)| ≤ 112 ε²` for
  `0 < |ε| ≤ 1/1024`, for the genuine moving
  natural-domain eigenvalue.
- [x] **L5 — Signed shift and consolidated theorem (§4.97).**
  The true moving eigenvalue shifts upward for positive ε
  and downward for negative ε. A single theorem packages
  the natural-domain eigenpair, the two simple eigenspaces,
  the point-spectrum window count, the `112ε²` quadratic
  energy law and the bright/exterior leakage estimate.
  The selected theorem is Lean- and Comparator-verified; independent
  scientific assessment remains separate.

**Verified L7 objective — exact zero-leakage two-mode preparation**

L7a uses the eight-edge *coordinated local perturbation* `M`. The following
static, algebraic and switched dynamical results are Lean-verified in §§4.99–4.105.

- [x] Construct eight genuine, distinct, mutually disjoint adjacent pairs.
- [x] Define the bounded symmetric finite sum and certify matching amplitudes.
- [x] Prove `M D=0` and `M F=2F`, with `M a=a-b` and `M b=b-a`.
- [x] Establish `Q M P=0` and natural-domain invariance under both controls.
- [x] **L7b (first part):** derive the exact dark/bright matrix, its Pauli
  decomposition and the three complex generator commutators.
- [x] **L7b (completion):** prove full real su(2) generation and constructive
  three-rotation reachability from dark for every normalized complex pair,
  with independent signed real generator coefficients.
- [x] **L7c.1:** exact single-axis real/imaginary Schrödinger trajectories,
  conserved norm, natural-domain lifts and zero leakage at every time;
  full real self-adjointness for both controls together.
- [x] **L7c.2:** identify the single-axis trajectories with Euler rotations
  including the common scalar phases, and certify identity at zero time
  and compatibility with matrix multiplication.
- [x] **L7c.3:** compose the three pulses with matching endpoint states,
  continuous full-space components, natural-domain membership, exact
  piecewise Schrödinger equations, norm conservation and zero leakage at
  every time, including the switches.
- [x] **L7c.4:** prove arbitrary normalized target preparation from dark up
  to the explicit global phase with `‖Qψ(t)‖=0` at every time, continuous
  natural-domain trajectories and full piecewise Schrödinger equations.
- [ ] Construct a general full complex Hilbert-space unitary propagator.

Static invariance and Lie generation alone would not suffice for a
preparation theorem; the explicit natural-domain trajectories and endpoint
proof now supply it. See the [verified L7 and preserved L6 roadmap](bright-spectral-splitting-roadmap.md#6-l7--exact-two-mode-preparation-without-leakage-verified).

**Deferred original research direction: L6 — single-edge approximate control (PRESERVED, OPEN)**

The original two-control plan remains a separate future target:
use only the single selected inter-ring edge `W` and the
eight-site parameter `t`, while proving an explicit small-leakage
and reachability budget for general complex Schrödinger dynamics.
Because `‖QWF‖²=7/16`, this one-edge correction does not preserve
the original dark–bright plane exactly. Verified conditional
uniform leakage estimates and static control identities remain
useful ingredients; no complete L6 target-state theorem is claimed.
The following original research narrative and
[edge-control note](edge-control-reachability.md) are retained
for later investigation. Its original compact-mode discussion uses the
`a/b` basis; in the `D/F` basis, detuning `t` does mix dark and bright.

The eight-site parameter `t` already gives a simple, exact energy response:
moving `t` away from `t_*` shifts one compact mode's energy and leaves the
other unchanged. Under a time-dependent quantum interpretation, this could
change the relative phase of a **pre-existing** coherent superposition; the
phase difference would remain after returning to `t_*`. Because the same two
modes remain eigenvectors for every `t`, changing `t` alone cannot create
the missing mode amplitude when starting in only one mode. At this historical single-edge stage, quantum time evolution and phase control were not formalized. The later coordinated-control theorems (§§4.102–4.105, 4.111) now construct the specified compact-plane dynamics, without resolving the original L6 problem or constructing a general complex propagator.

A change to the weight of the single edge between the two rings is a more
promising candidate for mixing the amplitudes. The original code already
proves that one combination remains an exact eigenstate after this edge
change, and that the complementary direction has an exact energy
expectation. The [edge-control research note](edge-control-reachability.md)
explains the nonzero coupling and a further constraint: in unitary dynamics
with only this edge varied, the common eigenstate's occupation is conserved.
Thus an edge-only pulse cannot reach every superposition from a single
initial mode. Two new Lean modules
[`AmmannBeenkerEdgeControl.lean`](../SpectralGeometry/AmmannBeenkerEdgeControl.lean)
and
[`AmmannBeenkerTwoControlAlgebra.lean`](../SpectralGeometry/AmmannBeenkerTwoControlAlgebra.lean)
build directly on the crossing equations, adding the exact coupling,
the normalized dark eigenstate and the response to detuning (§4.80).
Their exact operator identities have passed the full Lean build; the
dynamic single-edge no-go theorem and the L6 preparation protocol remain open. The separate coordinated L7 preparation protocol is now proved in §4.105.
Sections 4.81–4.91 now add an exact qubit/leakage decomposition,
the reduced-gap and exact-edge norm, quantitative **conditional**
time-uniform bounds for a selected-edge pulse and subsequent
free evolution, real pulse-Hamiltonian self-adjointness, and
one exact dark-state Schrödinger trajectory and the exact bright
forcing identity with external feedback. What remains
open is construction of the general **complex** unitary
propagator and a quantitative **target-state preparation**
theorem, not the conditional pulse-error bounds themselves.

- [x] **Finish the quantitative bright spectral splitting (§4.97).**
  The genuine moving level exists (L2c), is uniquely
  simple within the isolated window (L2d), has certified
  bright/exterior eigenvector control (L3), satisfies
  the `112ε²` energy law (L4), and has a signed
  shift and consolidated full-domain theorem (L5).
  The compressed energy expectation alone is not the theorem.
- [ ] **L6 (deferred): define the single-edge controlled dynamics.** Extend the relevant setting to
  complex quantum states and a time-dependent edge weight, while keeping
  the underlying infinite operator and its domain well defined. Determine
  how the two compact-mode amplitudes interact with the remaining modes.
- [ ] **L6 (deferred): characterize reachability and test a two-control protocol.**
  Prove the conserved dark-state occupation for edge-only time-dependent
  dynamics. Starting from one compact mode, test a weak edge pulse to
  change the amplitudes, then restore the edge and detune `t` to
  adjust their relative phase. Seek an explicit bound on preparation
  error and leakage into other energy levels; determine whether this
  achieves arbitrary targets in the compact plane up to a chosen error.
  See [the research note](edge-control-reachability.md) for the
  proposed protocol and its limitations.
- [x] **Certify full real-space qubit/leakage and conditional ON/OFF
  pulse bounds (§§4.81–4.88).** The orthogonal decomposition,
  certified gap and edge norm, exact-domain real self-adjointness,
  residual-conservation implications and duration-uniform
  `512|ε|` leakage estimate (under the explicit evolution
  hypotheses) have all passed Lean CI.
- [x] **Verify one exact complex-phase Schrödinger trajectory (§4.89).**
  The normalized dark mode has a real/imaginary solution of the
  coupled Schrödinger equations with norm one and zero leakage
  at every time for any real strength of the selected edge.
  This is **one solution**, not a constructed complex
  propagator on the full space.
- [x] **Verify the bright-amplitude forcing bridge (§4.91).**
  The fourteen bright generator declarations are Lean-verified. The exact
  forcing term and bound are static, full-infinite-graph identities, not
  integrated dynamical control.
- [x] **Verify the existing static dark/bright identities (§4.92).**
  The established combined theorem and source dependencies passed full Lean
  and independent statement checks.
  Those identities by themselves do not assert a moving level;
  that **later existence theorem** is independently proved in §4.93.
- [ ] **General complex dynamics and L6 controlled A/B preparation (open).** Build the genuine complex-Hilbert-space
  unitary evolution with natural-domain invariance and generator
  commutation, apply the proved leakage bounds to it, and then
  certify nontrivial bright-mode mixing, target amplitudes,
  relative phase and reachability limitations.

This is intended as a self-contained result with a possible physical
interpretation, **not** a claim that a laboratory implementation exists.
The spectral-product program below remains the project's long-term goal.
The existing dark/bright results (§§4.80–4.92) provide
certified algebraic inputs. The complete spectral analysis
in §§4.93–4.97 now additionally proves **genuine isolated,
signed and quantitatively controlled spectral splitting**
on the infinite graph. The distinct coordinated-control route has
since established exact preparation (§4.105) and quantitative static
spectral protection (§4.110). The original single-edge approximate
preparation goal remains open. The immutable first
Palomar registration remains unchanged.

**Remaining tasks for the original spectral-product program**

- [ ] Derive an isolation radius and a nonzero analytic-cofactor lower
  certificate for a specified geometric spectral level or cluster.
  Account for multiplicity; do not assume simple spectrum.
- [ ] Combine these data with a quantitative spectral-tail bound to
  certify a finite-product cutoff and exact disk zero count (§6.3).
  The onsite constants of §4.67 do not automatically apply here.
- [ ] Prove a uniform vertex-separation estimate if needed for sharper
  geometric estimates; it is not a prerequisite for the established
  summability and full-product application.

**Further geometric and research questions**

- [ ] Formalize global rotational symmetry, polygonal tiling coverage and
  aperiodicity when these properties are part of a claimed application.
  The present spectral theorem is about the explicitly defined graph.
- [ ] Compare the proved multiplicity-two classification of §4.78 with
  the compact-state literature and obtain an expert assessment (§6.8).

The radius-two intervention gives the nine-level full-product response
of §4.72. The first-ring intervention gives the exact crossing
eigenspace (§4.78) and real spectral gap (§4.79). L1–L5 now also
certify the distinct moving level, isolated signed splitting and
quantitative bright geometry (§§4.93–4.97); these do **not** certify
quantum state preparation. L7a now proves exact invariance of the original
plane under both coordinated controls, and L7b establishes the effective
matrix, full Lie generation and constructive Euler state reachability
(§§4.99–4.101). The verified L7c.1 single-axis trajectories (§4.102) solve the full
natural-domain Schrödinger equations with exact zero leakage. L7c.2 identifies them with the exact phase-weighted rotations (§4.103).
L7c.3 proves their continuous three-pulse composition with exact zero
leakage (§4.104). L7c.4 proves the arbitrary-target endpoint theorem
from dark for this verified trajectory (§4.105).
The one-edge, small-leakage preparation route remains open, and the
spectral-product and relative-determinant objectives are unchanged.

### 6.5. Local geometric defects and relative spectral products

**Target theorem: an exact finite determinant for the relative product**

For a verified finite-support perturbation
$H'=H+\iota_S K\iota_S^*$, establish the identity of §2.3:
```math
\frac{F_{H'}(z)}{F_H(z)}
=\frac{\det(I+K G_S(z))\det(I+K G_S(-z))}
       {\det(I+K G_S(0))^2}.
```

- [ ] Specify the allowed changes of site energies or couplings and
  prove their finite-support operator representation. If a geometric
  move changes the site set, construct and justify the identification
  used for the two Hilbert spaces.
- [ ] Verify self-adjointness, a strictly positive gap, compact resolvent
  and the summability assumptions for both operators.
- [ ] Construct the complex Green matrix using the interface of §6.1.
  Prove the determinant identity and its normalization, with an explicit
  common domain and meromorphic continuation statement.
- [ ] Track the difference of zero multiplicities through the relative
  identity, including shared zeros and pole cancellations.
- [ ] Relate finite-coordinate observation to the visibility of low
  eigenspaces in the compressed resolvent. Prove any residue-rank or
  nonvanishing statement that is used; do not assume that restriction
  injectivity already supplies the entire determinant theorem.
- [ ] Apply the result to an explicitly verified intervention or geometric
  change in the concrete model. State the resulting information about
  zero response with its actual parameter and energy range.

Finite-rank perturbation determinants are established operator theory, including
in work on infinite graphs; see
[Golinskii](https://doi.org/10.1080/03081087.2016.1155529).
The research contribution must be identified through a precise geometric
application or quantitative result beyond a relabeling of that theory.

### 6.6. Certified finite-patch approximation and zero response

A finite Green matrix still contains information about the infinite system.
This phase provides the missing approximation certificate.

- [ ] Define a finite-patch operator with explicit boundary conditions and
  its embedded resolvent. Preserve the distinction between truncating a
  fixed confined operator and changing the infinite-volume model.
- [ ] Bound the error of the Green matrix on specified compact sets away
  from spectral poles. Derive any exponential buffer estimate from
  verified locality and barrier assumptions, with explicit constants;
  do not assume a universal exponential rate.
- [ ] Propagate the matrix error to the relative determinant and the
  analytic products, controlling their normalizations. The absolute
  scalar tail budget of §4.61 and the linear-growth rate of §4.66 are
  available for a fixed spectral sequence; deriving the required data
  from a finite-patch matrix remains to be justified. The worked numerical
  onsite certificate of §4.67 does not supply such a matrix error.
- [ ] Certify zero counts in contours and intervals for the finite-patch
  approximation, with multiplicities. The bounded common-domain operator
  certificate of §4.56 is available only after a compatible error bound
  has been proved; it does not identify a finite matrix with the infinite
  operator. Sections 4.60–4.65 supply local location estimates with
  exponent $1/m$ and exact counts with multiplicities on disks under a
  strict scalar boundary error. A finite-patch application must still
  construct that error certificate and its boundary margins. Counts on
  noncircular contours and the required finite-patch error bounds remain
  open.
- [ ] Make the resulting error bounds small relative to the spectral
  scale of the proposed application. In statistical comparisons, fix the
  unfolding independently and control its amplification of spectral error.
- [ ] Produce a worked finite certificate for the concrete geometric
  application, separating proved error bounds from numerical evidence.

The intended result is a quantitative statement about the response of an
infinite system that can be assessed using finite data with a proved error.

### 6.7. Exploratory objectives: zero statistics and structural constraints

**Local statistics on the fixed line**

- [ ] Define the energy windows, symmetry sectors, normalization and
  averaging procedure for the zero statistics being compared.
- [ ] Investigate whether a specified model or geometric family has local
  correlations approaching a random-matrix law. A CUE/GUE bulk comparison
  targets the sine-kernel process after unfolding, not merely the
  mean density of zeros or one matching histogram.
- [ ] Analyze the operator's symmetry class. The current real model does
  not automatically provide unitary-class statistics; any magnetic
  extension requires complex couplings, verified self-adjointness and
  analysis of residual symmetries.
- [ ] Treat convergence of pair correlations, convergence of all local
  correlations and evidence from finite spectra as different claims.
  None follows from the prescribed line or from the relative-product
  identity.

**Separate long-term question: a line determined by structure**

- [ ] Define an analytically meaningful object from an independently
  specified geometric construction without encoding a desired zero line
  in its factors or an affine coordinate. Investigate whether a proved
  structural mechanism then forces its zeros onto a line.

This last question is distinct from the program using the prescribed line
$c+d\mathbb R$. It is exploratory, not a prerequisite for the response
theorem, and carries no asserted connection to the Riemann zeta function.

### 6.8. Independent statement verification and research-interest assessment

**Historical first registration — preserved.** The 2026 Palomar
record `PALOMAR-2026-11-06-000012` selected
`crossingEigenspace_finrank` and
`crossing_eigenvector_representation`, plus three
necessary model witnesses (§4.78). It proved the full
infinite-operator crossing eigenspace was exactly
two-dimensional. Neither this record nor its registration
is being replaced.

**Earlier, unsubmitted candidate (§4.92).** The former
generator-response candidate `crossingOneEdgeDarkBrightResponse`
and its dedicated
[`palomar/dark-bright/comparator.json`](../palomar/dark-bright/comparator.json)
are kept as an archive, with exact snapshots of its original
Challenge and Solution. It has **not** been claimed as
a separate registered Palomar theorem.

**L5 selection and editorial history (§4.98).** The preserved L5
Challenge and Solution select
`crossing_final_signed_bright_spectral_splitting`, with six
necessary concrete-model witnesses. Its theorem-specific
[Comparator](../palomar/signed-bright-splitting/comparator.json)
is preserved; the earlier unsubmitted generator-response candidate
remains archived under `palomar/dark-bright/`.

- [x] Preserve the original registered theorem, source proof
  and archived candidate without rewriting their history.
- [x] Complete the original L5 independent Challenge/Solution
  package and verification.
- [x] Submit the original L5 package; mechanical and renderability checks
  passed, while the automated editorial review requested an explicit
  existence statement for the fixed dark eigenstate.
- [x] Strengthen the selected theorem and independent Challenge with
  `crossingDark ≠ 0` and the full fixed-dark eigenvector equation;
  verify the corrected package with full Lean and Comparator.
- [x] Record the separate L5 registration
  [PALOMAR-2026-11-23-000017 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-23-000017&version=1) on 23 November 2026 (§4.98).

**Third registration (§4.105).** The Lean-verified exact preparation theorem was selected with its concrete graph witnesses and local-edge certificates. The [independent package](../palomar/exact-leakage-free-preparation/) passed full Lean and independent Comparator verification, Palomar mechanical verification and renderability checks. The automated editorial review identified no blocking problem. The result was registered on 25 November 2026 as [PALOMAR-2026-11-25-000001 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-25-000001&version=1).

**Fourth registration (§4.110).** Spectral protection during coordinated control is Lean-verified; the [independent package](../palomar/spectral-protection-during-coordinated-control/) passed full Lean verification and independent statement comparison, including NanoDa and con-ron. Registered on 26 November 2026 as [PALOMAR-2026-11-26-000015 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000015&version=1).

**Registration boundary.** The historical first registration
`PALOMAR-2026-11-06-000012` remains unchanged.
Successful Lean checks and a successful Comparator alone are **not** Palomar registration. The separate registry record [PALOMAR-2026-11-23-000017 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-23-000017&version=1) subsequently registered L5 on 23 November 2026.

**Potential research interest, without a priority claim.** The compact
A/B patterns are known in quasicrystal tight-binding research
([Oktel 2021](https://doi.org/10.1103/PhysRevB.104.014204)).
Protected combinations and local rank-one perturbations are not novel
mathematical primitives. What may merit further examination is the **full infinite-system
spectral statement**: a protected simple dark eigenstate, a second
unique simple nearby energy whose shift sign and quadratic
remainder are proved, and a moving eigenvector with quantified
external coupling. These statements avoid the unjustified
assumption that the two original localized states form an
exactly invariant closed two-level system.

A complementary **mathematical interest** is the contrast between
single-edge coupling to the exterior and exact reducing subspaces
under coordinated local controls. The latter yields a constructive
three-pulse preparation theorem on the full natural domain (§4.105),
followed by quantitative full-real-spectrum isolation (§4.110) with
exact plane energies and explicit sufficient control bounds. These
conclusions are stronger than a phenomenological two-state approximation:
the exterior component is exactly zero for the ideal preparation,
and the spectral separation is proved against the entire exterior
real spectrum for weak ideal controls.

For **theoretical condensed-matter and wave-network researchers**,
these results offer a concrete model in which local interventions
can preserve or couple localized waves in different ways. The original
single-edge ON/OFF pulse bounds remain conditional on the supplied
evolution. The coordinated preparation and static isolation theorems
are independent conclusions; their combination into arbitrary-target
preparation with a prescribed fraction of the baseline gap throughout
variable-duration pulses is now Lean-verified (§4.111; §6.9).
The [scientific-audience overview](scientific-audience.md#scientific-audience-and-possible-relevance)
explains these connections and their limitations.

These possible readerships, the novelty and the significance of the
results have not been independently assessed. No general complex
full-space propagator, arbitrary-initial-state preparation theorem,
noise tolerance, optimal control range or experimental realization
is claimed.

- [ ] Compare the precise new theorem against the specialist
  literature and obtain independent expert assessment of interest
  and novelty independently of registry verification.
- [ ] Continue the separate scalar cofactor and finite-patch
  certificates required in §§6.3, 6.5 and 6.6.

<a id="69-l8a--quantitative-spectral-protection-under-coordinated-controls-open"></a>
### 6.9. L8a — Quantitative spectral protection under coordinated controls (verified; refinements open)

**Central static objective and centered refinement verified; further refinements open.** L7 proves that the
two localized modes can be manipulated without any leakage when both
controls are applied exactly as prescribed. That protection is
geometric: the two-mode plane is invariant even for large signed
control strengths. It does not by itself show that the two controlled
energy levels remain separated from the rest of the spectrum.
L8 begins by asking how much energetic protection survives while the
controls are active. This is a prerequisite for investigating the
effect of imperfections, not a proof of robustness against noise.

**Verified starting point.** At zero control strengths, the complete
real bounded-inverse spectrum has no other point in the closed
radius-`g = 1/128` window about `E_*` (§4.79). The original dark/bright
plane `P` and its orthogonal complement `Q = I - P` reduce the ideal
controlled Hamiltonian by exact invariance and symmetry
(§§4.99–4.102, with explicit natural-domain projection lifts and
commutation identities verified in §4.107). The exact characterization
of the two plane eigenvalues is now Lean-verified in §4.107:

```math
\lambda_\pm(\delta,\eta)
= E_*+\delta/2+\eta\ \pm\sqrt{\delta^2/4+\eta^2}.
```

**Verified L8a.1 (§4.106).** The exact natural-domain change from the zero-control
Hamiltonian is `B = δ R + η M`, where `R` is the first-ring onsite
projection and `M` is the sum of the eight matched edge operators.
Using the actual disjoint endpoints, Lean proves `M² = 2M`,
`‖R‖ = 1`, `‖M‖ = 2` and `‖B‖ ≤ ρ = |δ| + 2|η|` for all real δ, η.

**Verified L8a.2 (§4.107).** Both displayed energies have nonzero full-domain
compact eigenvectors, and these are the only energies with such
plane eigenvectors. Their half-spacing vanishes exactly for δ = η = 0.
The domain lifts of P and Q and their commutation with the full controlled
Hamiltonian are verified for arbitrary real control strengths.

**Verified L8a.3 (§4.108).** For every natural-domain exterior vector x,
`(g−ρ−|e−E_*|)‖x‖ ≤ ‖Hx−ex‖`. Every eigenvector with nonzero leakage
satisfies `g ≤ ρ+|e−E_*|`. Properness of the onsite potential gives
full real bounded-inverse spectrum equivalence to nonzero full-domain
eigenvectors at all controls. In the open window `ρ+|e−E_*|<g`,
all eigenvectors have zero leakage and the full real spectrum is
characterized by the two explicit plane energies.

**Verified L8a.4 (§4.109).** The consolidated theorem proves a conservative lower bound on the
separation between the controlled two-mode spectral cluster and
the spectrum on the orthogonal complement is

```math
g_{\rm protected}(\delta,\eta)\ \ge\ g-2\rho
\qquad\text{when }2\rho<g.
```

This is now a Lean-certified sufficient bound, with the explicit
condition `ρ < 1/256` and positive separation `1/128−2ρ`. The distance concerns the two-mode cluster versus the
exterior spectrum, not the spacing between its two levels, which
may coincide. The centered refinement below improves this estimate.
Do not infer loss of protection when a sufficient condition fails.

**Verified centered spectral protection (§4.110).** With `s=√(δ²/4+η²)`,
centering at the controlled midpoint gives the full-space perturbation
bound `ρ/2`. If `ρ/2+s<1/128`, the complete real spectrum is isolated
by at least `1/128−ρ/2−s>0`, with exactly the two levels in their closed
interval and no leakage at either. In particular `ρ<1/128` suffices and
the gap is at least `1/128−ρ`. The separate Palomar package passed
independent comparison and was registered as [PALOMAR-2026-11-26-000015 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000015&version=1).

**L8a proof obligations**

- [x] **L8a.1:** Exact bounded control decomposition, `M² = 2M`, exact norms
  `‖R‖ = 1`, `‖M‖ = 2`, and `‖B‖ ≤ |δ| + 2|η|` (§4.106).
- [x] **L8a.2:** Exact two-way controlled plane eigenvalue characterization,
  degeneracy criterion and reducing projections on the natural domain (§4.107).
- [x] **L8a.3:** Quantitative exterior residual and eigenvalue exclusion,
  full real-spectrum characterization and zero leakage in the explicit
  open window (§4.108).
- [x] **L8a.4:** Consolidated full-real-spectrum cluster isolation under
  `ρ < 1/256`, with positive separation `1/128−2ρ`, including the
  degenerate zero-control case (§4.109).
- [x] Verify the stronger centered control bound and consolidated spectral
  protection (§4.110).
- [x] Independently compare the new spectral-protection candidate.
- [x] Submit it for separate registry verification and record the fourth registration.
- [x] Exact variable-duration preparation with arbitrarily weak ideal controls,
  zero leakage and a prescribed fraction of the certified baseline gap (§4.111).
  The substantive proof is Lean-verified.
- [x] Independently compare all 19 selected propositions of the fifth candidate (Lean default, NanoDa and con-ron).
- [ ] Submit the fifth candidate for separate registry verification and record registration only if completed.
- [ ] Investigate further sharp bounds and imperfect control dynamics.

**Scope and continuation.** L8a is a verified static spectral-protection
theorem for ideal controls. Later L8b–L8e may address nonuniform control
errors, leakage, preparation fidelity and robust pulse design.
No dynamical noise bound, arbitrary-strength spectral gap, hardware
robustness is asserted. The fourth registration concerns static spectral protection. L6 and all
Track A objectives remain open as before.

See [Chapter 7 — Research methodology and maintenance rules](maintenance-rules.md#7-research-methodology-and-maintenance-rules) for the repository's documentation and verification policy.
