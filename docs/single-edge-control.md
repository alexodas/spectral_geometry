[← Main README and table of contents](../README.md)

# 4. Infinite-dimensional geometric operators and spectral theory — §§4.80–4.98

**Chapter 4 navigation:** [4.1–4.67. Infinite-dimensional spectral theory](infinite-spectral-theory.md) · [4.68–4.79. Ammann–Beenker geometry and the compact crossing](ammann-beenker-geometry.md) · **4.80–4.98. Single-edge control and spectral splitting** · [4.99–4.111. Coordinated quantum control and spectral protection](coordinated-quantum-control.md)

<details>
<summary>Contents of this document</summary>

- [4.81. Exact qubit/leakage bookkeeping after a temporary pulse](#481-exact-qubitleakage-bookkeeping-after-a-temporary-pulse)
- [4.82. Uniform leakage estimate conditional on a nearby invariant spectral plane](#482-uniform-leakage-estimate-conditional-on-a-nearby-invariant-spectral-plane)
- [4.83. From the certified 1/128 gap to a quantitative bound on nearby eigenvectors](#483-from-the-certified-1128-gap-to-a-quantitative-bound-on-nearby-eigenvectors)
- [4.84. Why spectral isolation yields a residual bound: infinite-dimensional Parseval](#484-why-spectral-isolation-yields-a-residual-bound-infinite-dimensional-parseval)
- [4.85. Uniform post-pulse leakage without a perturbed spectral projector](#485-uniform-post-pulse-leakage-without-a-perturbed-spectral-projector)
- [4.86. Residual conservation follows from Hamiltonian intertwining](#486-residual-conservation-follows-from-hamiltonian-intertwining)
- [4.87. The actual selected-edge pulse Hamiltonian is self-adjoint on its natural real domain](#487-the-actual-selected-edge-pulse-hamiltonian-is-self-adjoint-on-its-natural-real-domain)
- [4.88. A controlled pulse followed by free evolution after switching the edge off](#488-a-controlled-pulse-followed-by-free-evolution-after-switching-the-edge-off)
- [4.89. An exact complex-phase Schrödinger trajectory for the dark mode](#489-an-exact-complex-phase-schrödinger-trajectory-for-the-dark-mode)
- [4.90. Consolidated verified control checkpoint and outstanding dynamics](#490-consolidated-verified-control-checkpoint-and-outstanding-dynamics)
- [4.91. Verified bright-amplitude generator identity with explicit leakage forcing](#491-verified-bright-amplitude-generator-identity-with-explicit-leakage-forcing)
- [4.92. Earlier, unsubmitted Palomar candidate: exact dark protection and bright feedback](#492-earlier-unsubmitted-palomar-candidate-exact-dark-protection-and-bright-feedback)
- [4.93. Verified dark simplicity and a distinct perturbed spectral level](#493-verified-dark-simplicity-and-a-distinct-perturbed-spectral-level)
- [4.94. Two simple eigenvalues in a certified perturbed window](#494-two-simple-eigenvalues-in-a-certified-perturbed-window)
- [4.95. Bright amplitude and quantitative exterior leakage](#495-bright-amplitude-and-quantitative-exterior-leakage)
- [4.96. A sharp quadratic law for the actual moving level](#496-a-sharp-quadratic-law-for-the-actual-moving-level)
- [4.97. Signed shift and consolidated infinite-operator splitting](#497-signed-shift-and-consolidated-infinite-operator-splitting)
- [4.98. Palomar registration: signed bright splitting](#498-palomar-registration-signed-bright-splitting)

</details>

### 4.80. First exact algebraic results for controlling the two compact modes

This new step connects the crossing (§§4.75, 4.78), its certified spectral
isolation (§4.79), and the proposed coherent-control problem (§6.4).
The modules
[`AmmannBeenkerEdgeControl.lean`](../SpectralGeometry/AmmannBeenkerEdgeControl.lean)
and
[`AmmannBeenkerTwoControlAlgebra.lean`](../SpectralGeometry/AmmannBeenkerTwoControlAlgebra.lean)
extend the previously proved natural-domain equations. Both modules are
imported by the main Lean library and checked in the full CI proof build.
The statements here are exact static identities, not yet a dynamical
control or state-preparation theorem.

Let `a` and `b` be the original compact modes (each of squared norm
eight), let `W` be the actual one-edge Laplacian perturbation, and write
`D = (a + b)/4` for their **unit** equal-amplitude combination.
The edge has an exact nonzero cross-mode matrix element. More generally,
its bilinear form on two combinations is

```math
\langle r a+s b,\,W(u a+v b)\rangle=(r-s)(u-v).
```

This is an exact statement about the full infinite Hilbert space, **not**
a claim that the two-dimensional mode plane is invariant under `W`.
The new lemmas also show that `D` has unit norm and `W D=0`.
Building on `crossing_dark_eigenvector` (§4.75), they express its
stationarity as a **normalized, natural-domain eigenvector theorem**:
for every real edge change `ε`, the full perturbed operator still has
`D` at the original crossing energy.

The second module proves that the compact-mode plane stays exactly
invariant under any detuning and adds the energy response for `t=t_*+δ`:

```math
K_{t_*+\delta}a=(E_*+\delta)a,\qquad
K_{t_*+\delta}b=E_*b.
```

When the two controls are allowed together, the operator acts on the
dark state by the exact identity

```math
(K_{t_*+\delta}+\varepsilon W)D
=E_*D+\frac{\delta}{4}a.
```

Thus the edge alone leaves the dark direction fixed, while detuning
`t` changes it within the compact-mode plane. Neither identity asserts
a controlled quantum evolution. For the original single-edge route, the remaining work is to construct
the requisite complex unitary dynamics and prove approximate target
preparation. Conditional pulse leakage bounds are established later
in §§4.85–4.88; a different coordinated-control construction proves
exact preparation in §4.105.

See [the edge-control research note](edge-control-reachability.md) for
the proposed two-pulse strategy, the predicted obstruction to edge-only
universal preparation, and its currently unproved dynamical requirements.
These static single-edge and detuning identities are distinct from the
registered crossing theorem and from the later registered preparation
theorem using coordinated edges.

### 4.81. Exact qubit/leakage bookkeeping after a temporary pulse

The control goal has three phases: prepare an initial compact mode at the
crossing, apply a temporary edge pulse (and optionally detune `t`), and
restore both controls. Restoring the original operator restores the original
eigenvalues, eigenspaces and certified gap. **It does not restore the
initial state**: any amplitude transferred to unwanted modes can remain.

The new
[`AmmannBeenkerQubitLeakage.lean`](../SpectralGeometry/AmmannBeenkerQubitLeakage.lean)
imports §4.80 and defines a decomposition for *every* state `x` in
the **full real infinite-graph Hilbert space**. Using the original
orthogonal compact eigenvectors `a,b`, each of squared norm eight, put

```math
r=\langle a,x\rangle/8,\quad s=\langle b,x\rangle/8,
\qquad p=ra+sb,\quad\chi=x-p.
```

The new source proves `⟨a,χ⟩=⟨b,χ⟩=0`; thus `p` is
the true orthogonal two-mode component, and `χ` captures **all**
other modes, not only a hypothetical third one. Its exact norm identity is

```math
\|x\|^2=8(r^2+s^2)+\|\chi\|^2.
```

For unit-norm `x`, if `‖χ‖²≤η`, the total weight in
the compact-mode plane is at least `1-η`. The proof makes **no**
assumption that the transient edge operator preserves this plane.
It also does not prove that the *individual* amplitudes have the
requested values. The §4.81 declarations have now passed the full Lean CI verification.

A second theorem records what *is* guaranteed by restoring the
original operator `K_*` after the pulse:

```math
K_*p=E_*p.
```

This is a genuine natural-domain eigenvector equation for the compact
part of any final state; it is **not** a claim that `χ=0` or that
switching the pulse off erases the leakage.

**Exact static obstruction to an ideal two-level edge action.** The
same Lean module now computes the full-space edge response of the
original compact mode `a`. It proves

```math
\|Wa\|^2=2,\quad
\|PWa\|^2=\tfrac14,\quad
\|(I-P)Wa\|^2=\tfrac74>0,
```

where `P` is the orthogonal projection onto `span{a,b}`. For the
normalized mode `A=a/√8`, the corresponding external response is

```math
\|(I-P)WA\|^2=\tfrac7{32}.
```

More generally, the same source computes the off-plane response of
**every real combination** of the unnormalized compact modes:

```math
\|(I-P)W(ra+sb)\|^2=\tfrac74(r-s)^2.
```

In particular, the direct edge-induced off-plane response vanishes
for equal amplitudes `r=s` (the protected dark direction), but is
strictly positive whenever `r≠s`. The control cannot be modeled
as a closed exact two-level interaction on the entire qubit plane.

Thus the single-edge perturbation **really does couple A to modes
outside the qubit plane**. This is much stronger than merely saying
that leakage is possible: it is an exact nonzero numerical certificate
in the complete infinite graph, not a truncated finite model. The
exact calculation has passed Lean CI verification.

**Full single-edge and detuning response.** This Lean result also
treats the complete natural-domain action of both available controls,
`K_(t_*+δ)+εW`. For any real compact-mode input `ra+sb`,
the off-plane response has the exact squared norm

```math
\|(I-P)(K_{t_*+\delta}+\varepsilon W)(ra+sb)\|^2
=\tfrac74\,\varepsilon^2(r-s)^2.
```

The detuning `δ` disappears *exactly*: changing `t`
does not directly excite external modes, whereas the connecting
edge does whenever `r≠s`. These are static natural-domain
identities, **not** bounds on the leakage after a finite pulse.
This identity concerns the original single-edge and detuning controls,
not the later coordinated matching of §4.99.

**Careful distinction:** this number measures the *off-plane
component of the perturbation vector*, not leakage probability
after any particular pulse. Under a future complex unitary
Schrödinger model, it predicts a short-time leakage probability
`(7/32) ε² τ² + o(τ²)` for a constant edge pulse from A. That
short-time asymptotic is **not yet formalized in Lean**.
It does **not** rule out cancellation of external amplitudes at
a specially chosen final time, nor does it establish a universal
lower bound on final pulse leakage.

**Next stage: complex quantum dynamics.** Complexify the Hilbert space,
normalize the modes as `A=a/√8, B=b/√8`, and define orthogonal
projections `P` onto their two-dimensional span and `Q=I-P`.
For normalized quantum states the corresponding probability budget is

```math
|\langle A,\psi\rangle|^2+
|\langle B,\psi\rangle|^2+\|Q\psi\|^2=1.
```

Construct the restored self-adjoint Hamiltonian's unitary evolution
`U_0(τ)` and prove `P U_0(τ)=U_0(τ)P`. It would then follow that
`‖Q U_0(τ)ψ‖²=‖Qψ‖²`: **leakage already present
when the pulse is switched off persists**, while the two-mode part
only acquires a common phase. These time-evolution results are not
yet in the Lean library.

Finally construct the piecewise-constant edge/`t` pulse propagators
and seek a bound, up to a physically irrelevant global phase,

```math
\inf_{\theta\in\mathbb R}
\|U_{\mathrm{pulse}} A-e^{i\theta}(\alpha A+\beta B)\|
\le\eta,\qquad |\alpha|^2+|\beta|^2=1.
```

This **full-state error** would imply `‖Q U_pulse A‖≤η`
and hence leakage probability at most `η²`, while also
certifying the desired complex amplitudes and relative phase.
The existing real spectral gap is a possible input for such an
estimate, not proof of it. See §6.4 and
[the research note](edge-control-reachability.md).

### 4.82. Uniform leakage estimate conditional on a nearby invariant spectral plane

The most useful next analytical step is not merely to make an edge
pulse *short*: to produce a significant mixing of A and B using a
weak edge weight, its duration may have to grow as the weight shrinks.
A naive time-integrated bound proportional to `|ε| T` is
therefore insufficient.

The new
[`QubitLeakagePulseBound.lean`](../SpectralGeometry/QubitLeakagePulseBound.lean)
formalizes a **generic, conditional, time-uniform estimate** in a real
normed space. It assumes three bounded linear maps:

- `P`, the desired compact-mode projection;
- `S`, a projection onto a nearby *invariant* (perturbed) plane;
- `U`, a norm-preserving evolution map that commutes with `S`.

Assume the initial vector `x` is entirely in the desired plane
(`Px=x`), and the projections are quantitatively close:

```math
\|(P-S)y\|\le d\,\|y\|\quad\text{for every }y.
```

The Lean lemma derives **without assuming an evolution duration**
that

```math
\|Ux-PUx\|\le 2d\,\|x\|.
```

For `‖x‖=1` and `d≥0`, the squared-norm leakage is at
most `4d²`. The proof is only the triangle inequality: compare
the final state with the invariant perturbed plane and account for
the initial and final differences between `P` and `S`.
The result is **fully conditional on the displayed hypotheses**,
and is not yet instantiated with the Ammann–Beenker Hamiltonian or
a complex Schrödinger propagator. It does not prove that a useful
qubit rotation can be reached.

**Graph-specific projector goals still open for the single-edge route.** The existing full crossing gap
`g=1/128` suggests constructing a two-dimensional perturbed
spectral projector `P_ε` for a sufficiently weak fixed edge
perturbation and proving an operator-norm estimate
`‖P_ε-P‖≤d(ε)`, with `d(ε)→0` as `ε→0`. One must
then construct the complex unitary pulse propagator, prove it
commutes with `P_ε`, and instantiate the abstract lemma. This
would give uniformly small **final leakage for a long but weak
pulse**, independently of pulse duration. Finally one must
separately prove that the same pulse yields the intended relative
amplitudes/phase; a leakage bound alone does not prepare an
arbitrary target.

This sequence distinguishes three different assertions:
the exact static off-plane response (§4.81), the **conditional**
time-uniform estimate (this section), and the still-unproved
single-edge approximate preparation protocol (L6, §6.4). The alternative
coordinated-control protocol is proved in §§4.102–4.105, without using
this perturbed-projector construction.

### 4.83. From the certified 1/128 gap to a quantitative bound on nearby eigenvectors

The next theorem now has a **concrete numerical target**. In
[`AmmannBeenkerQubitLeakage.lean`](../SpectralGeometry/AmmannBeenkerQubitLeakage.lean),
the rank-one edge operator `W` is shown to have **exact operator norm
`‖W‖=2`**, not merely a finite-dimensional compression. Hence

```math
\|\varepsilon W x\|\le 2|\varepsilon|\,\|x\|.
```

The new
[`AmmannBeenkerNearCrossingEigenvectors.lean`](../SpectralGeometry/AmmannBeenkerNearCrossingEigenvectors.lean)
then sets up an exact full-natural-domain eigenvector comparison. Let
`K_*` be the crossing Hamiltonian, `P` the orthogonal projection
onto its two compact modes, `Q=I-P`, `E_*` its crossing energy, and
`g=1/128`. A perturbed eigenvector `x` satisfying

```math
(K_*+\varepsilon W)x=\lambda x
```

obeys the **unconditional residual identity**

```math
(K_*-E_*)x=(\lambda-E_*)x-\varepsilon Wx.
```

To turn this into a bound on the *external component* `Qx`, we
use the **reduced-gap residual estimate**

```math
g\,\|Qy\|\le\|(K_*-E_*)y\|
\qquad(y\in\operatorname{Dom}K_*).
```

In a complete self-adjoint spectral decomposition this is the
quantitative form of spectral isolation: every component outside
the `E_*` eigenspace has spectral distance at least `g`.
The graph's real spectral exclusion within radius `g` is already
certified (§4.79). The lemma
`crossingReducedGapResidualEstimate_full` derives
this norm inequality from the previously proved full eigenbasis
existence and operator symmetry (§4.84). These graph-specific
declarations are Lean-verified.

**Quantitative theorem, with the gap hypothesis now discharged
in source:** the full gap-bound declaration derives

```math
g\,\|Qx\|\le
\bigl(|\lambda-E_*|+2|\varepsilon|\bigr)\|x\|.
```

If the perturbed eigenvalue is also known to satisfy the usual
bounded-perturbation window `|λ-E_*|≤2|ε|`, this yields an explicit
numerical **one-sided eigenvector estimate**

```math
\boxed{\|Qx\|\le512|\varepsilon|\,\|x\|.}
```

For eigenvectors satisfying that energy-window hypothesis,
decreasing `|ε|` makes the proposed upper bound tend to zero.
This is precisely how the isolated gap can protect the two-mode
state against weak edge coupling.

**Two important boundaries:** the graph-specific residual inequality
has now been derived in source from complete-basis and gap theorems,
Lean-verified. The **perturbed eigenvalue-shift window** remains
an explicit hypothesis of this particular estimate; §§4.93–4.97 later establish the requisite window for the actual moving level. Also, an inequality on individual perturbed
eigenvectors is **not yet** an operator-norm estimate
`‖P_ε-P‖` for the whole perturbed two-dimensional spectral
projection. The latter requires constructing and identifying that
cluster, including its dimension, before §4.82's duration-independent
pulse estimate can be applied. This is *not* a proof of arbitrary
state preparation.

The full graph-specific gap-to-residual instantiation is **already
Lean-verified** (§4.84). Sections 4.85–4.88 also obtain a
**different**, conditional graph-specific leakage bound uniform
in pulse duration directly from residual conservation, without a
perturbed spectral projector. The isolated simple point-spectrum pair is now
established in §§4.93–4.97; constructing its spectral projector and proving
the operator-norm projector estimate of §4.82 remain open as a separate,
potentially sharper route. A general complex quantum propagator and
approximate target preparation using the original single-edge controls
remain open; exact nontrivial rotations and preparation using the
coordinated controls are proved in §§4.102–4.105.

### 4.84. Why spectral isolation yields a residual bound: infinite-dimensional Parseval

The following link in the proof is represented by two
Lean-verified theorem packages.

**Generic complete-basis theorem.** The new
[`DomainEigenbasisGapResidual.lean`](../SpectralGeometry/DomainEigenbasisGapResidual.lean)
starts with a genuine complete real *domain eigenbasis* `b_i`
of a symmetric (possibly unbounded) operator `K`, with energies
`E_i`. Suppose every energy other than `E_*` has distance at
least `g>0` from `E_*`. For every natural-domain vector `y`
having zero coefficient in all eigendirections with `E_i=E_*`,
Parseval and the eigenvector equation give

```math
g\,\|y\|\le\|(K-E_*)y\|.
```

This does not assume finite dimension or a bounded Hamiltonian.
In words: if an off-qubit vector has significant size, its
`(K-E_*)` residual cannot be tiny, because *every* frequency
participating in it is separated from `E_*`.

**Specialization to the real Ammann–Beenker crossing.**
The new `crossingReducedGapResidualEstimate_of_domainEigenbasis`
in
[`AmmannBeenkerNearCrossingEigenvectors.lean`](../SpectralGeometry/AmmannBeenkerNearCrossingEigenvectors.lean)
uses the previously established theorem that the **entire**
`E_*` eigenspace is `span{a,b}`, plus the explicit
`1/128` exclusion of every other eigenvalue. It derives the
missing residual estimate of §4.83 from **a supplied complete
domain eigenbasis and a symmetry proof for the original crossing
operator**:

```math
\tfrac1{128}\|(I-P)x\|\le\|(K_*-E_*)x\|.
```

The new `crossingReducedGapResidualEstimate_full` declaration
goes a step further: it **constructs the required complete crossing
eigenbasis** by invoking the repository's earlier
`onsitePlusBounded_exists_orderedEigenbasis` theorem for the proper
onsite potential, and supplies symmetry via
`finiteSectorCorrection_symmetric`. Hence the full reduced-gap
inequality is an **unconditional Lean-verified theorem for the
actual infinite graph**, not merely a supplied hypothesis.
**The gap-to-residual Lean code has passed CI.**

Consequently, `crossingEdge_perturbed_eigenvector_gap_bound_full`
states without any *additional* gap assumption that

```math
\tfrac1{128}\|(I-P)x\|\le
\bigl(|\lambda-E_*|+2|\varepsilon|\bigr)\|x\|
```

for **every real perturbed full-domain eigenvector** at `λ`.
The related `crossingEdge_nearby_eigenvector_leakage_le_full`
gives `‖(I-P)x‖≤512|ε|‖x‖` whenever the
energy-window hypothesis `|λ-E_*|≤2|ε|` holds. These are
Lean-verified mathematical statements, *not* a spectral
projector or time-evolution result.

Even that eigenvector estimate does not yet prove
`‖P_ε-P‖→0`. The two simple eigenvalues in the relevant point-spectrum
window were subsequently certified in §§4.93–4.97. The corresponding
orthogonal spectral projector, its norm estimate and the
full complex unitary evolution are still needed to invoke the time-uniform pulse
bound of §4.82.

### 4.85. Uniform post-pulse leakage without a perturbed spectral projector

The verified §4.84 reduced-gap inequality gives a more direct route
to controlling **all** external modes during a constant-strength
connecting-edge pulse, without first constructing the perturbed
two-dimensional spectral projector.

The new
[`AmmannBeenkerPulseResidualBound.lean`](../SpectralGeometry/AmmannBeenkerPulseResidualBound.lean)
introduces the *shifted perturbed-Hamiltonian residual*

```math
R_\varepsilon(x)=(K_*+\varepsilon W-E_*)x.
```

Let `x` be an exact initial crossing eigenvector
(`K_*x=E_*x`) and `y` a possible state after the pulse,
both in the original infinite-graph natural domain.
If the final state satisfies the two explicit conservation laws

```math
\|y\|=\|x\|,\qquad
\|R_\varepsilon(y)\|=\|R_\varepsilon(x)\|,
```

then the new Lean theorem aims to certify

```math
\boxed{\|(I-P)y\|\le512|\varepsilon|\,\|x\|.}
```

For normalized initial states, this yields the corresponding
**squared-norm** bound `‖(I-P)y‖²≤(512|ε|)²`.
The proof combines the exact edge norm `‖W‖=2` and
the established infinite-graph reduced gap `g=1/128`:

```math
g\,\|(I-P)y\|
\le\|(K_*-E_*)y\|
\le\|R_\varepsilon(y)\|+2|\varepsilon|\,\|y\|
\le4|\varepsilon|\,\|x\|.
```

Crucially, **there is no factor depending on the elapsed pulse
time**. For a genuine unitary propagator of the *fixed*
self-adjoint Hamiltonian `K_*+εW`, the two conservation laws
follow from norm preservation, invariance of the natural domain,
and commutation with its own generator. The real-space Lean
statement deliberately assumes exactly these consequences:
**it does not yet construct a complex Schrödinger propagator**.

This bound sidesteps the need for a perturbed spectral projector
when the only goal is small external leakage from a constant
edge pulse. It does **not** assert that the pulse transfers the
requested amplitudes between A and B, controls their complex
relative phase, or achieves arbitrary-state preparation.
A protocol with changing `t` and/or piecewise-constant `ε`
also needs segment-by-segment analysis; conservation of
`R_ε` applies only during a segment with a fixed Hamiltonian.

**Lean status:** §§4.85–4.89, including the intertwining and switch-off
statements, are Lean-verified. The earlier unsubmitted Palomar candidate
is documented in §4.92 and the later registered L5 selection in §4.98.
### 4.86. Residual conservation follows from Hamiltonian intertwining

Section 4.85 established a time-uniform edge-pulse leakage inequality
under **two conservation hypotheses** for the full graph. The next
formal step removes the *independent* shifted-residual-conservation
assumption: it is a consequence of the operator intertwining identity.

The new
[`AmmannBeenkerPulseIntertwining.lean`](../SpectralGeometry/AmmannBeenkerPulseIntertwining.lean)
takes a continuous real-linear map `U` on the full infinite-graph
Hilbert space and requires:

- **Isometry:** `‖Uz‖ = ‖z‖` for every full-space vector `z`.
- **Natural-domain invariance:** `Ux` lies in the onsite domain
  whenever `x` does.
- **Hamiltonian intertwining on that domain:**

  ```math
  (K_*+\varepsilon W)Ux=U(K_*+\varepsilon W)x.
  ```

The new lemma `crossingPulseResidual_intertwines` proves, by
linearity and commutation, the **exact vector identity**

```math
R_\varepsilon(Ux)=U R_\varepsilon(x),
\quad R_\varepsilon=K_*+\varepsilon W-E_*.
```

Therefore `crossingPulseResidual_norm_conserved` proves
`‖R_ε(Ux)‖=‖R_ε(x)‖` from isometry; it is **no longer
a separate assumption**. Applying the §4.85 graph-specific
gap estimate gives, for every initial crossing eigenvector,
the Lean-verified theorem

```math
\boxed{\|(I-P)Ux\|\le512|\varepsilon|\,\|x\|.}
```

The same module also proves the statement for a supplied family
`U_ε(τ)` for **all real `τ`**, plus the squared-norm bound
`‖(I-P)U_ε(τ)x‖²≤(512|ε|)²` when `‖x‖=1`.
There is no elapsed-time factor and no perturbed spectral
projection in these statements. The graph and the selected
connecting edge remain unchanged.

**Crucial remaining distinction:** the family `U_ε(τ)` is
supplied as a hypothesis. This new real-Hilbert-space result
does *not* construct the physical complex Schrödinger unitary
`e^{-iτ(K_*+εW)}`, establish its generator or domain
invariance, or demonstrate a useful A/B rotation. Nor does
it assert a group law or continuity in time for the supplied
family. It simply proves that these concrete operator-theoretic
properties are **sufficient** for the previously certified
leakage conclusion.

**Lean status:** this intertwining module and its root import
have passed the full Lean verification. The statement remains
conditional on the supplied real isometry and domain/commutation
hypotheses; it does not certify state preparation.

### 4.87. The actual selected-edge pulse Hamiltonian is self-adjoint on its natural real domain

The next step specializes the existing genuine Mathlib
`LinearPMap` self-adjointness theorem to the **same physical
selected edge** used throughout §§4.80–4.86.

The new
[`AmmannBeenkerPulseSelfAdjoint.lean`](../SpectralGeometry/AmmannBeenkerPulseSelfAdjoint.lean)
defines the full unbounded partial operator `crossingEdgePulsePMap ε`
on the real infinite-graph Hilbert space. Its exact domain
is `infiniteOnsiteDomain potential`; for every real `ε`,
its action there is

```math
K_\varepsilon x=(K_*+\varepsilon W)x.
```

The source derives self-adjointness by using a zero-color
matching family, the known self-adjointness machinery for a
proper natural onsite domain, the symmetry of the original
bounded ring interaction, and the exact symmetry of the
rank-one selected-edge perturbation:

```math
\langle Wx,y\rangle=\langle x,Wy\rangle.
```

The Lean-verified theorem

```lean
crossingEdgePulsePMap_isSelfAdjoint (ε : ℝ) :
  IsSelfAdjoint (crossingEdgePulsePMap ε)
```

has **no small-ε restriction**: the perturbed operator
is self-adjoint for any real edge weight on its original
natural domain. The self-adjointness and exact-domain
statements concern the **full infinite operator**, not
an effective 2×2 matrix or a finite graph.

**Limitations:** this is self-adjointness over **ℝ**
in Mathlib's partial-linear-map API. Constructing the
physical complex Hilbert-space counterpart and its
strongly continuous unitary Schrödinger propagator,
including `U_ε(τ)D(K_ε)⊆D(K_ε)` and
`K_εU_ε(τ)=U_ε(τ)K_ε`, is still a separate task.
The §4.86 implication from these conditions to
residual conservation and the leakage estimate does
not by itself supply that physical evolution.

**Lean status:** this full-graph real self-adjointness theorem
and §4.86 have passed the full Lean verification. At that checkpoint, the original Palomar selection and its
Challenge/Comparator files were unchanged. The later
generator-response candidate is archived in §4.92, and the
later registered L5 selection is in §4.98. The first
registration remains immutable.

### 4.88. A controlled pulse followed by free evolution after switching the edge off

The new
[`AmmannBeenkerPostpulseSwitchOff.lean`](../SpectralGeometry/AmmannBeenkerPostpulseSwitchOff.lean)
formalizes an ON/OFF protocol using the **same selected edge**.

The pulse changes the Hamiltonian from `K_*` to
`K_ε=K_*+εW`; switching the edge off returns it to
`K_*`. These two different fixed Hamiltonians have
**different shifted-residual conservation laws**.
We therefore track

```math
R_\varepsilon(\psi)=(K_*+\varepsilon W-E_*)\psi,\qquad
R_0(\psi)=(K_*-E_*)\psi.
```

Suppose the initial vector `x` lies in the original
two-dimensional crossing eigenspace. After the active
pulse, let `y` be a full natural-domain state satisfying

```math
\|y\|=\|x\|,\qquad
\|R_\varepsilon(y)\|=\|R_\varepsilon(x)\|.
```

When the edge is switched off, the actual unperturbed
residual at the switching instant is bounded:

```math
\boxed{\|R_0(y)\|\le4|\varepsilon|\,\|x\|.}
```

This follows from `R_0(y)=R_ε(y)-εWy`,
`‖W‖=2`, and `R_ε(x)=εWx`. It does not
assume that the pulse leaves the qubit plane invariant.

Now let `z` be any final state of a free segment whose
**unperturbed** residual is conserved:

```math
\|R_0(z)\|=\|R_0(y)\|.
```

The full infinite-graph reduced-gap theorem yields

```math
\boxed{\|(I-P)z\|\le512|\varepsilon|\,\|x\|.}
```

The new module also proves the same result for any
supplied family of norm-preserving, domain-preserving
real-linear maps intertwining `K_*`, and then for a
**two-family ON/OFF protocol**: the first intertwines
`K_ε`, the second intertwines `K_*`. The leakage
bound is uniform over **both** elapsed times. There is
no approximation that treats the unperturbed and
perturbed residuals as if they were identical.

**Scope and remaining obligations:** these real-linear intertwining
families are supplied as assumptions. This single-edge result
certifies the consequences of the two segment-wise conservation
laws, **not** the existence of the general physical dynamics or
approximate target preparation by these controls. The distinct
coordinated-control construction in §§4.102–4.105 proves exact
nontrivial rotations and zero-leakage preparation on the original plane.

**Lean status:** §4.88 and its root import have passed the
full Lean verification, along with §§4.85–4.87.

### 4.89. An exact complex-phase Schrödinger trajectory for the dark mode

The selected edge has an exceptional *exact* eigenvector:
the normalized equal-amplitude combination
`crossingDark=(compactA+compactB)/4` is an eigenvector at
`E_*` for **every** real selected-edge strength `ε`;
the rank-one edge acts as zero on this vector.

The new
[`AmmannBeenkerDarkSchrodinger.lean`](../SpectralGeometry/AmmannBeenkerDarkSchrodinger.lean)
constructs an explicit time-dependent solution, for every
real `τ`, in the full graph's natural domain:

```math
\psi_\varepsilon(\tau)=
e^{-i E_*\tau}\,\mathrm{dark}
=\underbrace{\cos(E_*\tau)\,\mathrm{dark}}_{\operatorname{Re}\psi}
-i\underbrace{\sin(E_*\tau)\,\mathrm{dark}}_{-\operatorname{Im}\psi}.
```

The source works with its real and imaginary parts as
**two full real Hilbert-space vectors**, each with an
explicit natural-domain lift. This representation avoids
assuming a yet-unconstructed complex infinite-graph
Hamiltonian. Using Mathlib's trigonometric derivative
lemmas and the **full** eigenvector identity, it verifies
the real and imaginary Schrödinger equations:

```math
\frac{d}{d\tau}\operatorname{Re}\psi
=(K_*+\varepsilon W)\operatorname{Im}\psi,
\qquad
\frac{d}{d\tau}\operatorname{Im}\psi
=-(K_*+\varepsilon W)\operatorname{Re}\psi.
```

Together these say `i∂_τψ=K_εψ` for this particular
phase trajectory. The module additionally establishes

```math
\operatorname{Re}\psi(0)=\mathrm{dark},
\quad \operatorname{Im}\psi(0)=0,
\quad
\|\operatorname{Re}\psi(\tau)\|^2+
\|\operatorname{Im}\psi(\tau)\|^2=1,
```

and zero leakage from **both** components for all times.
There is no small-`ε` restriction: the dark state
remains completely decoupled from this one edge at any
strength.

**Important limitation:** this verifies a *single explicit*
solution of the Schrödinger equation. It is not a
construction of the general complex unitary propagator,
does not prove its uniqueness or group law, and does not
show a nontrivial `A\leftrightarrow B` rotation. The
imaginary/real pair is a representation of this complex
trajectory, not yet a complete complex Hilbert-space
construction or generic dynamics theorem.

**Lean status:** this dark-state Schrödinger module and all prior
§§4.80–4.88 control declarations are Lean-verified.

### 4.90. Consolidated verified control checkpoint and outstanding dynamics

This section consolidates **previously proved and CI-checked** facts.
It does not introduce an additional Lean theorem and does not
replace §§4.75–4.89 or any earlier spectral-product results.

**Exact infinite-graph geometry and spectrum (§§4.74–4.79).**
At `t_*=17/16+√2`, two orthogonal eight-site compact
modes `a,b` have squared norm `8` and common energy
`E_*=13/4+√2`. They span the **entire real eigenspace**
at that energy, of dimension exactly two. The complete
real spectrum has no other point within the closed radius
`g=1/128` around `E_*`. These are properties of the
**full infinite graph**, not a finite truncation.

**One fixed control edge (§§4.80–4.83).**
We retain the actual adjacent lattice vertices
`u=(1,0,0,0)` and `v=(1,1,0,0)`; the bounded rank-one
edge operator is `W=|δ_u-δ_v⟩⟨δ_u-δ_v|` with
exact full-space norm `‖W‖=2`.
The normalized modes `A=a/√8` and `B=b/√8`
define the orthogonal projection `P` onto their span,
with leakage projection `Q=I-P`. The edge has
a nonzero A/B coupling and a **nonzero external
response**, so the two-mode plane is not asserted
to be invariant while the edge is on. The normalized
dark vector `D=(A+B)/√2=(a+b)/4` satisfies
`WD=0` and is an exact full-domain eigenvector of
`K_*+εW` at `E_*` for **all real ε**.

**Gap, perturbed eigenvectors and duration-independent
conditional pulse bounds (§§4.83–4.88).**
The complete eigenbasis and certified gap imply, for
every `x∈Dom K_*`,

```math
\frac1{128}\|Qx\|\le\|(K_*-E_*)x\|.
```

For any perturbed eigenvector of `K_*+εW` at `λ`,
the full graph obeys

```math
\frac1{128}\|Qx\|\le
  (|\lambda-E_*|+2|\varepsilon|)\|x\|.
```

In particular, the additional **eigenvalue-window**
assumption `|λ-E_*|≤2|ε|` gives
`‖Qx‖≤512|ε|‖x‖`. This does not by itself
construct a nearby perturbed rank-two projector.

For an initial crossing eigenvector `x`, if
a constant-strength pulse has a final state `y`
with `‖y‖=‖x‖` and with its **perturbed**
residual norm `‖(K_*+εW-E_*)y‖` conserved,
then `‖Qy‖≤512|ε|‖x‖`. If the edge is then
switched **off** and the following free segment
conserves the **unperturbed** residual norm, the
same bound holds at every such final state `z`:

```math
\boxed{\|Qz\|\le512|\varepsilon|\,\|x\|.}
```

The results also derive these residual conservation
laws for **supplied real-linear isometries** that
preserve the original natural domain and intertwine
the corresponding fixed generator. Both segment
durations are arbitrary. The full real unbounded
pulse operator is separately proved self-adjoint on
that domain for every `ε∈ℝ`. These are **conditional
evolution estimates**; no actual general complex
unitary propagator has yet been constructed.

**One exact complex-phase dark trajectory (§4.89).**
Writing the complex wavefunction as a pair of real
Hilbert vectors, Lean verifies the full-domain
solution

```math
\psi_D(\tau)=e^{-iE_*\tau}D,
\qquad
\frac{d}{d\tau}\operatorname{Re}\psi_D
 =(K_*+\varepsilon W)\operatorname{Im}\psi_D,
\qquad
\frac{d}{d\tau}\operatorname{Im}\psi_D
 =-(K_*+\varepsilon W)\operatorname{Re}\psi_D.
```

It has complex squared norm one and **zero leakage**
at every time, for any real selected-edge strength.
This is **one explicit Schrödinger solution**,
not a full complex unitary group, and contains no
bright-mode rotation.

**Historical open obligations for the single-edge route (L6).** Construct the complexified
self-adjoint Hamiltonian and its strongly continuous
unitary Schrödinger group, prove domain invariance
and generator commutation, integrate the now-exact bright-mode
response against a justified dynamic leakage estimate, and then determine
which `αA+βB` targets are reachable using the
same edge and the existing `t` detuning.
The static dark eigenstate indicates an edge-only
reachability obstruction, but the general
time-dependent quantum no-go theorem and approximate preparation
using the original single edge and detuning remain open. The distinct
coordinated-control route has since proved exact arbitrary normalized
target preparation from dark (§4.105), and static energetic protection
under sufficiently small ideal controls (§4.110). Simultaneous
arbitrary-target preparation with a prescribed spectral gap through
variable-duration pulses is Lean-verified and registered (§4.111; §6.9). The original relative-product and
finite-patch objectives (§§6.5–6.6) remain separate
and open.
**Historical scientific checkpoint.** The §§4.80–4.89 results were
verified before the bright generator identities in §§4.91–4.92.
The original Palomar registration remains unchanged. This section
is retained as a summary of those earlier results.

### 4.91. Verified bright-amplitude generator identity with explicit leakage forcing

**Verification.** The original fourteen theorems in
[`AmmannBeenkerBrightAmplitude.lean`](../SpectralGeometry/AmmannBeenkerBrightAmplitude.lean)
are Lean-verified. The source also includes the combined candidate theorem
described in §4.92.

For the same selected lattice edge, write
`H_ε=K_*+εW`, let `P` be the exact orthogonal projection onto
the normalized compact-mode plane, and let `Q=I-P`.
For every **real** state `x` in the full natural onsite domain,
the proved Lean theorem gives the **exact** bright matrix element:

```math
\langle F,H_\varepsilon x\rangle
=\left(E_*+\frac{\varepsilon}{4}\right)\langle F,x\rangle
 +\varepsilon\langle F,WQx\rangle.
```

The term `ε⟨F,WQx⟩` is the *feedback from the entire orthogonal
complement*. In particular, this is **not** the eigenvalue equation
`H_ε F=(E_*+ε/4)F`; that assertion would be false for nonzero ε
because the edge excites external modes. The module's certified
quantitative bound, using the previously certified exact edge norm, is

```math
\left|\langle F,H_\varepsilon x\rangle
-\left(E_*+\frac{\varepsilon}{4}\right)\langle F,x\rangle\right|
\le 2|\varepsilon|\,\|Qx\|.
```

The corresponding dark identity is simpler and exact:

```math
\langle D,H_\varepsilon x\rangle
=E_*\langle D,x\rangle.
```

**Dynamical interpretation and limits.** Once a general complex
Schrödinger evolution on the common domain is constructed, these
matrix elements yield equations for the bright and dark amplitudes.
The forcing term can then be integrated against a proven leakage
bound to estimate phase error. This section **does not yet** construct
a propagator, integrate the amplitude equations, assert adiabatic
following, prove final return to the compact plane, or transfer
constant-pulse bounds to a smooth ramp. At ε=0 the original
twofold dark/bright degeneracy is preserved; no nondegenerate
adiabatic theorem is being invoked.

The fourteen generator-level declarations are Lean-verified.
Their combined conjunction was prepared as a separate, unsubmitted Palomar
candidate for independent statement comparison (§4.92). The prior
registered theorem remains unchanged.

### 4.92. Earlier, unsubmitted Palomar candidate: exact dark protection and bright feedback

**Earlier unsubmitted candidate, not the later L5 registration; preserved for historical reference.** The declaration
`SpectralGeometry.AmmannBeenker.crossingOneEdgeDarkBrightResponse`
in [AmmannBeenkerBrightAmplitude.lean](../SpectralGeometry/AmmannBeenkerBrightAmplitude.lean)
combines previously established conclusions into **one** mathematical
statement on the full real infinite graph. Let
`H_ε=K_*+εW` on `D(V)`, `D=(a+b)/4`, `F=(a-b)/4`,
and `Qx=x-Px` for the orthogonal projection onto `span{a,b}`.
It states, for all `ε∈ℝ` and `x∈D(V)`,

```math
H_\varepsilon D=E_*D,\qquad
\langle F,H_\varepsilon x\rangle
=\left(E_*+\frac{\varepsilon}{4}\right)\langle F,x\rangle
 +\varepsilon\langle F,WQx\rangle,
```

```math
\left|\langle F,H_\varepsilon x\rangle
-\left(E_*+\frac{\varepsilon}{4}\right)\langle F,x\rangle\right|
\le 2|\varepsilon|\,\|Qx\|.
```

The first clause is a **full-operator eigenstate**, not merely a
two-dimensional compression. The second exposes the **nonzero possible
coupling to the infinite exterior**. The third controls the error in
the projected bright generator, without pretending that the bright
vector itself is a perturbed eigenvector. These clauses do not
assert an actual complex time evolution, a dynamic leakage bound
without hypotheses, or a perturbative splitting formula.

**Potential contribution.** The compact ring patterns and rank-one
edge techniques are not claimed as new by themselves. The candidate
offers an exact, quantitative protected-versus-coupled description
for one **explicitly defined, infinite, confined** Ammann–Beenker
operator with a genuine inter-ring edge. Its value is the full-space
scope and the rigorous separation of an invariant dark direction
from unavoidable bright-to-exterior feedback, rather than a claim
that a finite effective qubit model is exactly closed.

**Possible scientific readership.** These earlier exact
protected-versus-coupled identities may be relevant to mathematicians
studying finite-rank perturbations and localized states on infinite
graphs, and to theorists studying dark and bright modes in quasiperiodic
or coupled-resonator systems. They provide algebraic context for the
later genuine spectral-splitting result (§4.97), rather than a separate
claim of controlled dynamics. Relevant antecedents are Oktel,
[Phys. Rev. B 104, 014204 (2021)](https://doi.org/10.1103/PhysRevB.104.014204),
and Röntgen–Morfonios–Schmelcher,
[Phys. Rev. B 97, 035161 (2018)](https://doi.org/10.1103/PhysRevB.97.035161).
These are literature references, not endorsements or evidence of novelty;
see also [scientific audience and possible relevance](scientific-audience.md#scientific-audience-and-possible-relevance).

**Archived independent Challenge.** The historical
[`Challenge.lean`](../palomar/dark-bright/Challenge.lean) states this earlier scientific theorem
without importing SpectralGeometry proofs. Six additional selected
propositions are **technical model witnesses** needed to define the
origin, graph matchings, compact-domain vectors and edge endpoints.
All model definitions must be compared transitively, with
`definition_names=[]`; these witnesses are not six more proposed
discoveries. The Challenge is kept below 300 lines if possible, but
that earlier independently explicit model required 531 physical
lines, well below Palomar's hard 1,000-line/100-KiB limit.
Its [historical per-theorem Comparator](../palomar/dark-bright/comparator.json)
and root-file snapshots are preserved unchanged. The stronger final spectral theorem was registered separately in §4.98.
The active Comparator selects the seventh candidate, exact compact-mode replication (§4.113); all six registered results and the unsubmitted generator-response candidate are preserved. The fifth registered result remains the exact protected preparation theorem (§4.111).

### 4.93. Verified dark simplicity and a distinct perturbed spectral level

This is a **subsequent, Lean-verified spectral result**, separate from the
generator-level Palomar candidate of §4.92 and from the immutable first
Palomar registration (§4.78). It concerns the **true infinite graph
operator on its original natural domain**, not a finite-patch truncation
or an energy expectation in the two-mode plane.

Write `H₀ = onsitePlusBounded potential (ringInteraction crossingParameter)`,
`Hε = onsitePlusBounded potential (ringInteraction crossingParameter + ε • crossingEdge)`,
`E_* = crossingEnergy`, and `D = (a+b)/4`, `F = (a-b)/4`.
The selected edge `W = crossingEdge` has `‖W‖ = 2`.
The following **distinct** milestones have passed the full Lean build:

- **L1 — exact dark simplicity.** The two theorems
  `crossingEdge_zero_of_perturbed_crossing_eigen` and
  `crossingPerturbedEnergy_dark_only` in
  [AmmannBeenkerNearCrossingEigenvectors.lean](../SpectralGeometry/AmmannBeenkerNearCrossingEigenvectors.lean)
  show that for every real `ε ≠ 0`, every natural-domain eigenvector
  of `Hε` at `E_*` is a scalar multiple of `D`. Together with the
  exact, normalized dark eigenvector for all `ε`, the eigenspace is
  **exactly one-dimensional**, as verified in Lean.
- **L2a — ordered spectral stability and exterior force.** The theorem
  `crossingEdge_exists_ordered_eigenbases_and_stability` constructs
  complete, monotone natural-domain eigenbases for `H₀` and `Hε`
  and supplies `∀ n, |μ n - λ n| ≤ 2|ε|`. The theorem
  `crossingBright_external_edge_norm_sq` proves the **exact**
  infinite-space coupling `‖QWF‖² = 7/16`. Both are in
  [AmmannBeenkerBrightSpectralSplitting.lean](../SpectralGeometry/AmmannBeenkerBrightSpectralSplitting.lean)
  and are Lean-verified.
- **L2b — multiplicity-faithful consecutive spectral slots.**
  `crossing_exists_ordered_eigenbasis_exact_double` constructs an
  ordered complete eigenbasis in which `levelMultiplicity` at `E_*`
  is precisely two.
  `ordered_levelMultiplicity_two_consecutive` in
  [OrderedLevelMultiplicityTwo.lean](../SpectralGeometry/OrderedLevelMultiplicityTwo.lean)
  and `crossing_exists_ordered_eigenbasis_consecutive_pair` then
  certify indices `n, n+1` with
  `λ_n = λ_(n+1) = E_*`, and no other crossing occurrence.
  Both passed full Lean and independent Comparator checks.
- **L2c — existence of a *genuinely distinct* perturbed level.**
  `crossing_exists_distinct_perturbed_level_near` in the bright
  splitting module proves, **for every real ε ≠ 0**, the proposition
  `∃ E_b ∈ ℝ, ∃ x ∈ D(V)`, with `x ≠ 0`, such that

  ```math
  H_\varepsilon x=E_b x,\qquad
  E_b\ne E_*,\qquad
  |E_b-E_*|\le 2|\varepsilon|.
  ```

  It identifies the ordered counting basis with the stability basis
  through `DomainEigenbasis.ordered_levels_unique`, then combines
  dark-only eigenspace rigidity with orthonormality: **both** perturbed
  crossing slots cannot still equal `E_*`.
  This is a genuine full-operator eigenpair, not the compressed
  bright expectation `E_*+ε/4`. The source and independent Comparator
  passed verification.

**What remained after L2c.** The L2c theorem did **not**
identify the moving eigenvector quantitatively with the original
bright direction, assert its simplicity, or exhaust the perturbed
crossing window. These latter two issues are addressed separately
in §4.94; they were **not** part of the L2c proof. For
`0 < |ε| ≤ 1/1024`, the
target second-order law was (at that stage)

```math
\bigl|E_b(\varepsilon)-(E_*+\varepsilon/4)\bigr|
\le 112\,\varepsilon^2,
```

together with the proposed exterior-component control
`‖Qx‖ ≤ 256|ε| |c| ‖QWF‖` for `x=cF+Qx` orthogonal to `D`.
These were **future L3–L5 obligations at the L2c stage**, not
consequences of L2c itself. The exterior bound was subsequently
proved in §4.95 and the quadratic energy law in §4.96.
No new Palomar candidature or registration has been
created from this intermediate milestone.

### 4.94. Two simple eigenvalues in a certified perturbed window

This **L2d** milestone strengthens the genuine L2c eigenpair existence
without replacing any older result. It applies to the full confined
infinite Ammann–Beenker graph and the **actual natural-domain**
Hamiltonian `Hε` of §4.93, for

```math
0<|\varepsilon|\le\frac1{1024}.
```

The theorem
`SpectralGeometry.AmmannBeenker.crossing_perturbed_isolated_pair_simple`
in
[AmmannBeenkerBrightSpectralSplitting.lean](../SpectralGeometry/AmmannBeenkerBrightSpectralSplitting.lean)
exhibits a nonzero natural-domain eigenvector `x_b` and energy
`E_b≠E_*` with `Hε x_b=E_b x_b` and

```math
|E_b-E_*|\le2|\varepsilon|.
```

Moreover every **nonzero natural-domain eigenvector** `y` of `Hε`
at any energy `t` satisfying `|t-E_*|≤1/256` has either
`t=E_*` or `t=E_b`. Every eigenvector at the moving
energy is a scalar multiple of `x_b`, so its geometric
eigenspace is **one-dimensional**. Independently, the already
proved dark-only result (L1) identifies the entire eigenspace at
`E_*` with the **one-dimensional** dark line.

**Why the proof is not a two-level approximation.** The complete,
multiplicity-faithful Hilbert eigenbases for both true unbounded
operators have indexwise stability `|μ_n−λ_n|≤2|ε|`. In the
unperturbed sequence, only the two consecutive crossing indices
have value `E_*`. Every other baseline eigenvector must lie
**strictly beyond the certified gap** `1/128` by the existing
no-other-eigenvector theorem. The norm bound `2|ε|` then keeps
all other perturbed ordered positions outside `1/256`.
A general Hilbert-basis argument shows that every genuine
nonzero eigenvector's energy occurs among those ordered positions.
L1 supplies the dark position and L2c the distinct moving position;
these exhaust the two slots. A unique spectral index also yields the
exact one-dimensional eigenvector representation. The support lemmas
`DomainEigenbasis.eigenvalue_occurs` and
`DomainEigenbasis.eigenvector_eq_smul_of_unique_level`
make these completeness and simplicity inferences explicit in Lean.

**Scope of the result.** This is an exhaustive description of
**natural-domain real eigenvalues in the specified window**. It is
not, by itself, a new statement about an independently defined
resolvent or complex spectrum; it also does not establish the sign
of the shift, the target `112ε²` remainder, or quantitative
external eigenvector leakage. These are limitations of L2d **alone**:
the external eigenvector estimate was subsequently proved in §4.95
and the energy remainder in §4.96. The signed-shift corollary and
final consolidated statement are established separately in §4.97.

**Verification.** The L2d theorem and its generic Hilbert-basis
support passed full Lean and independent Comparator checks.

### 4.95. Bright amplitude and quantitative exterior leakage

The L3 results concern the **actual moving natural-domain eigenvector**
of the unbounded infinite Ammann–Beenker operator, rather than a
two-mode compression. Let `D=(a+b)/4` and `F=(a-b)/4`
be the normalized dark and bright vectors, `Q` the exact
orthogonal projection onto the complement of their span,
and `v=QWF` the selected edge's external bright force.
The already certified identity is `‖v‖²=7/16`.

For `0<|ε|≤1/1024`, take the unique simple moving
real eigenvalue `E_b≠E_*` from §4.94 and a nonzero
natural-domain eigenvector `x` satisfying
`Hε x=E_b x`. Theorems
`crossing_moving_eigenvector_dark_orthogonal`,
`crossingQubitPart_eq_bright_smul_of_dark_orthogonal`
and `crossing_moving_eigenvector_bright_nonzero`
prove the *exact* decomposition

```math
\langle D,x\rangle=0,\qquad
x=cF+q,\qquad c=\langle F,x\rangle\ne0,\quad q=Qx.
```

The sharper L3 theorem
`crossing_moving_eigenvector_sharp_leakage`
establishes the **full infinite-operator leakage estimate**

```math
\boxed{\|q\|\le256\,|\varepsilon|\,|c|\,\|v\|}.
```

The existential corollary
`crossing_exists_moving_bright_sharp_leakage`
packages this bound with a genuine eigenpair and
`|E_b-E_*|≤2|ε|`. The preceding theorem
`crossing_exists_moving_eigenvector_bright_and_leakage`
also certifies `‖Qx‖≤512|ε|‖x‖`.

**Proof mechanism.** Symmetry forces the baseline
residual `Rx=(H₀-E_*)x` into the original
crossing-plane orthogonal complement. The exact
projected eigen-equation is

```math
Rx=(E_b-E_*)q-\varepsilon(cv+QWq).
```

The proved gap inequality `(1/128)‖q‖≤‖Rx‖`,
nonexpansiveness of `Q`, and `‖W‖=2` imply

```math
(1/128-|E_b-E_*|-2|\varepsilon|)\|q\|
\le|\varepsilon|\,|c|\,\|v\|.
```

The left coefficient is at least `1/256`
because `|E_b-E_*|≤2|ε|` and
`|ε|≤1/1024`. No assumed spectral projector,
finite patch or two-state truncation is used.

**Scope and subsequent progress.** L3 itself controls the
eigenvector rather than the energy shift. The true quadratic
spectral bound is established separately in §4.96; the formal signed-shift
corollary and consolidated theorem are established in §4.97.
Quantum state preparation is a separate downstream problem.

**Verification.** The preliminary and sharp L3 estimates and existential
corollary passed full Lean and independent Comparator checks.

### 4.96. A sharp quadratic law for the actual moving level

**L4 — true spectral-level estimate, not a Rayleigh quotient.**
The new source declarations in
[AmmannBeenkerBrightSpectralSplitting.lean](../SpectralGeometry/AmmannBeenkerBrightSpectralSplitting.lean)
connect the **genuine** moving natural-domain eigenvector of
§§4.94–4.95 with its eigenvalue. For every real perturbation satisfying

```math
0<|\varepsilon|\le\frac1{1024},
```

the theorem `crossing_exists_moving_level_quadratic_bound`
exhibits a nonzero full-operator eigenvector `x` at a
distinct moving real energy `E_b`, with
`|E_b-E_*|≤2|ε|` and the exact quantitative estimate

```math
\boxed{\left|E_b-\left(E_*+\frac{\varepsilon}{4}\right)\right|
\le112\,\varepsilon^2}.
```

The level is the **unique simple non-dark energy** in the
closed radius-`1/256` point-spectrum window, by the
independently proved L2d theorem; L4 uses that actual
eigenpair rather than asserting a new eigenpair
solely from an expectation value.

**Exact mechanism.** With the normalized crossing
bright state `F`, set
`c=⟨F,x⟩≠0`, `q=Qx`,
`v=QWF`, where `Q` is the original crossing-plane
orthogonal projection. The exact generator identity
`crossingBright_pulse_amplitude`, together with
`crossingBright_edge_leakage_inner`, gives the true
eigenvalue equation projected against bright:

```math
\left(E_b-E_*-\frac{\varepsilon}{4}\right)c
=\varepsilon\langle v,q\rangle.
```

The real Hilbert-space Cauchy–Schwarz lemma
`crossing_abs_inner_le_norm_mul` and the verified
sharp L3 external estimate give

```math
\begin{aligned}
\left|E_b-E_*-\frac{\varepsilon}{4}\right||c|
&\le|\varepsilon|\,\|v\|\,\|q\|\\
&\le256\,\varepsilon^2\,|c|\,\|v\|^2\\
&=112\,\varepsilon^2\,|c|,
\end{aligned}
```

because the squared full-graph force is exactly
`‖v‖²=7/16`. The previously established
`c≠0` justifies cancelling the coefficient.
The result is thus a theorem about the actual
**infinite natural-domain eigenvalue**, not a
two-level compression or finite-patch approximation.

The reusable parametric theorem
`crossing_moving_energy_quadratic_bound` requires only a genuine
near-crossing eigenvector, its nonzero bright coefficient
and the stated smallness hypothesis;
`crossing_exists_moving_level_quadratic_bound`
attaches it to the verified moving level.

**Scope and subsequent progress.** L4 alone establishes the
quadratic energy law, not a signed-shift corollary or one
consolidated final theorem. Those later conclusions are separately
proved in §4.97, without changing the historical L4 proof.
General complex time evolution and preparation of arbitrary
two-mode states remain outside this static spectral result.

**Verification.** Full Lean/Mathlib and independent Comparator checks passed.

### 4.97. Signed shift and consolidated infinite-operator splitting

**L5 — the consolidated real point-spectrum theorem for the
selected-edge perturbation.** The full Lean source
[AmmannBeenkerBrightSpectralSplitting.lean](../SpectralGeometry/AmmannBeenkerBrightSpectralSplitting.lean)
now includes `crossing_moving_energy_shift_sign` and
`crossing_final_signed_bright_spectral_splitting`. They
combine the existing L1–L4 results without assuming a
new two-level approximation or perturbative projector.

Let `Hε=H₀+εW` denote the genuine **infinite**
Hamiltonian on its natural onsite domain, with original
crossing energy `E_*`, normalized dark mode `D`,
normalized bright mode `F` and orthogonal projection `Q`
onto the complement of their original two-dimensional plane.
For every real `ε` with `0<|ε|≤1/1024`, the new theorem
constructs a real energy `E_b` and a nonzero
natural-domain eigenvector `x` satisfying

```math
H_\varepsilon x=E_bx,\quad E_b\ne E_*,
\quad |E_b-E_*|\le2|\varepsilon|.
```

It verifies the **actual moving energy's quadratic law**

```math
\boxed{\left|E_b-\left(E_*+\frac{\varepsilon}{4}\right)\right|
\le112\,\varepsilon^2}
```

and its **strict signed displacement**

```math
\varepsilon>0\Longrightarrow E_b>E_*,
\qquad
\varepsilon<0\Longrightarrow E_b<E_*.
```

The sign follows numerically from the proven L4 error:

```math
112\varepsilon^2\le\frac7{64}|\varepsilon|
<\frac14|\varepsilon|
\quad(\varepsilon\ne0).
```

The consolidated theorem additionally states that
**every nonzero natural-domain eigenvector** with real
eigenvalue in the closed radius-`1/256` window has energy
either `E_*` or `E_b`. Both geometric eigenspaces
are simple: the dark eigenspace is exactly the line
`ℝD` and the moving eigenspace exactly the line `ℝx`.

Writing `c=⟨F,x⟩≠0`, the moving eigenvector is
orthogonal to dark and has the exact full-space
decomposition and quantitative leakage bound

```math
x=cF+Qx,\qquad
\boxed{\|Qx\|\le256|\varepsilon|\,|c|\,\|QWF\|},
\qquad \|QWF\|^2=\frac7{16}.
```

The proof assembles genuine natural-domain eigenpairs,
the ordered gap/exhaustion arguments, exact dark
rigidity, nonzero bright amplitude, the sharp
full-exterior L3 bound, and L4's true eigenvalue
estimate, all in one statement with common parameter
hypotheses. It does **not** claim a separate
classification of complex spectrum, construction of
the general quantum propagator, target-state preparation,
or the remaining analytic-product certificates.

**Verification.** Both the complete Lean 4/Mathlib build and the
independent Comparator passed.

<a id="498-palomar-candidate-signed-bright-splitting"></a>

### 4.98. Palomar registration: signed bright splitting

**Second Palomar registration, with preparation and editorial history.** The
package selects the fully proved L5 statement
`SpectralGeometry.AmmannBeenker.crossing_final_signed_bright_spectral_splitting`
from [AmmannBeenkerBrightSpectralSplitting.lean](../SpectralGeometry/AmmannBeenkerBrightSpectralSplitting.lean).
Unlike the earlier generator-response candidate (§4.92), this
theorem concerns a **genuine moving eigenvalue of the full infinite
operator**, not just a matrix element calculated on the original
two-dimensional plane.

**Plain-language theorem.** If we slightly change one edge
in the specified infinite octagonal network, one simple
nearby energy level stays fixed and a second simple level
moves up when the edge is strengthened or down when it is
weakened. There are no other real eigenvector energies in
the stated narrow window. The moving energy is within a
proved quadratic error of a first-order prediction, and
the theorem bounds the part of its wave pattern outside
the original two localized states. The result concerns the
entire infinite network and its natural domain; it is
not a time-evolution or experimental-control result.

**Independent registered package.** The L5 [Challenge](../palomar/signed-bright-splitting/Challenge.lean) imports only Mathlib and reconstructs the necessary concrete model without source proofs. Its seven selected propositions consist of six technical model witnesses and one scientific conclusion. All definitions are concrete. Its [Solution](../palomar/signed-bright-splitting/Solution.lean) imports the verified proof module and never Challenge. Its [Comparator](../palomar/signed-bright-splitting/comparator.json) and [formalization metadata](../palomar/signed-bright-splitting/formalization.yaml) are preserved with those root-file snapshots. The earlier unsubmitted [generator-response package](../palomar/dark-bright/) is also preserved. The third registered result (§4.105) and the fourth registered result (§4.110) are preserved as separate packages; the fifth and sixth registered packages (§§4.111–4.112) are likewise preserved. The active root files now describe exact compact-mode replication (§4.113). Each Comparator remains in its own directory; there is no root Comparator.

**Verification and registration.** The L5 mathematical source and
independently assembled package passed full Lean and independent kernel
comparison (NanoDa and con-ron). The automated editorial review requested
that the selected theorem explicitly assert the **nonzero dark eigenvector**
and its fixed-energy eigenvalue equation. The corrected scientific theorem
and Mathlib-only Challenge include both `crossingDark ≠ 0` and the full
natural-domain equation `Hε domainCrossingDark = E_* • crossingDark`.
The revised package passed verification and was registered separately as
[PALOMAR-2026-11-23-000017 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-23-000017&version=1)
on 23 November 2026. The original registration
`PALOMAR-2026-11-06-000012` remains unchanged.
Originality and significance still require independent assessment.

