# Single-edge control of the compact crossing: research note

**Status:** exact static algebra in two Lean modules, checked by the
full Lean/Mathlib build, and an exploratory dynamical research proposal.
This is **not** a certified quantum-control or state-preparation protocol. This note complements [README §4.80](../README.md#480-first-exact-algebraic-results-for-controlling-the-two-compact-modes)
and the [roadmap in §6.4](../README.md#64-p4--a-confined-ammannbeenker-model-and-a-finite-intervention)
without changing the selected [Palomar result](../PALOMAR.md).

## Starting point: an infinite-graph theorem, not a two-site model

At the certified crossing of the infinite confined octagonal vertex graph,
the *entire* eigenspace at the crossing energy is spanned by two orthogonal
compact modes, `a` and `b`. Each has squared norm 8. Write the normalized
modes as `A = a / √8` and `B = b / √8`, and define

- **Dark:** `D = (A + B) / √2 = (a + b) / 4`
- **Bright:** `Q = (A - B) / √2 = (a - b) / 4`

Both are unit vectors. The original operator acts on this plane as the
crossing energy times the identity. Its real spectrum is known to contain no
other point within a certified radius of 1/128 of the crossing energy.

The perturbation changes the weight of **one edge** between the rings.
Writing `u = δ_(A0) - δ_(B0)`, its operator is `W = |u⟩⟨u|`.
This is the *graph-Laplacian* edge change, which affects the two diagonal
and two off-diagonal matrix entries associated with the edge.

## Exact coupling: what is already algebraically accessible

The selected edge acts differently on the two modes. In the orthonormal
basis `(A, B)`, its **compression** to the crossing eigenspace is

```text
            [  1  -1 ]
P W P  =  1/8 [         ] .
            [ -1   1 ]
```

Equivalently, the compressed operator has the dark direction `D` with
coefficient zero and the bright direction `Q` with coefficient 1/4.

The module
[`AmmannBeenkerEdgeControl.lean`](../SpectralGeometry/AmmannBeenkerEdgeControl.lean)
contains the exact unnormalized two-mode bilinear formula, the nonzero
off-diagonal element, a normalized dark vector, the identity `W D = 0`,
and its **full natural-domain eigenvector equation for any edge weight**.
These results explicitly build on `crossing_dark_eigenvector` in the
previous crossing module. The second module,
[`AmmannBeenkerTwoControlAlgebra.lean`](../SpectralGeometry/AmmannBeenkerTwoControlAlgebra.lean),
makes the detuning response exact, shows that the **entire two-mode
span remains invariant for every detuning**, and records that, with both
controls available, the infinite operator sends `D` to
`E_* D + (δ/4) a` regardless of the edge weight. Both modules are
included in the root `SpectralGeometry.lean` import list.

**Crucial limitation:** `P W P` is a compression, **not** the action
of `W` on an invariant two-level system. In general, `W` also couples
a compact mode to states outside this eigenspace. The gap at the
unperturbed crossing does not by itself bound such leakage under control.

## What it means to return the Hamiltonian to its initial value

An ideal control cycle is **initial operator → temporary edge pulse →
original operator again**. At the end of the cycle, the original
crossing eigenvectors and their eigenvalues are restored, as is the
certified gap about `E_*`. But switching the pulse off **does not undo
the state evolution**. A mode `C` at a different energy can have
nonzero amplitude after the pulse even though the original gap and
spectrum have returned. Energy separation alone does not force its
amplitude to vanish.

Instead of following a single hypothetical `C`, define the entire
orthogonal remainder `χ`. The new Lean source
[`AmmannBeenkerQubitLeakage.lean`](../SpectralGeometry/AmmannBeenkerQubitLeakage.lean)
extracts the exact compact-mode component `p` of any real graph state
`x` using the already verified norms `‖a‖²=‖b‖²=8`:

```text
r = ⟨a,x⟩ / 8
s = ⟨b,x⟩ / 8
p = r a + s b
χ = x - p
‖x‖² = 8(r² + s²) + ‖χ‖² .
```

Here `χ` is orthogonal to both compact modes, with no restriction on
the number of external modes. For a unit real state, a leakage bound
`‖χ‖² ≤ η` certifies at least `1-η` squared weight in the
two-mode plane. At the restored crossing operator, the source also
proves the exact eigenvalue equation `K_* p = E_* p` on the
natural domain. These are Lean-verified algebraic facts, **not proofs of the
existence of a general complex unitary pulse evolution**.

**Complex probability and persistence obligation.** Define the
complex orthogonal projection `P` onto normalized `A,B` and
`Q=I-P`. For normalized `ψ`, the physically relevant budget is
`|⟨A,ψ⟩|² + |⟨B,ψ⟩|² + ‖Qψ‖² = 1`.
A future theorem must show that restored evolution
`U_0(τ)=exp(-iτK_*)` is well-defined, commutes with `P`,
and therefore preserves `‖Qψ‖²`. Thus **leakage already
present at the end of the pulse remains present**, while the two-mode
part acquires only a common phase. The mathematical fact that the
operator has been restored is not a method of removing `χ`.

A successful *preparation* result must control **two different errors**:

1. The total undesired probability `‖Q U_pulse A‖²`, counting *all*
   non-qubit modes of the infinite graph.
2. The fidelity or full-state distance, up to global phase, to the
   requested complex target `αA+βB`. Small leakage alone cannot
   choose the individual amplitudes or their relative phase.

A practical theorem specification is a full-state error at most `η`,
for every chosen `η>0`, with controls restored to the crossing values.
It implies leakage norm at most `η` and leakage probability at most
`η²`. A weak-pulse perturbation and the certified unperturbed gap
are candidates for proving this estimate; **it has not been proved**.

## Exact edge-induced excitation outside the qubit plane

The proposed two-level description is **not an invariant subspace**
under the physical one-edge perturbation. An explicit exact
full-infinite-Hilbert-space calculation in
[`AmmannBeenkerQubitLeakage.lean`](../SpectralGeometry/AmmannBeenkerQubitLeakage.lean)
(Lean-verified) shows, for the original **unnormalized**
compact mode `a`, and the exact orthogonal projection `P` onto
`span{a,b}`:

```text
‖W a‖²         = 2
‖P W a‖²       = 1/4
‖(1-P) W a‖²   = 7/4 .
```

For the **normalized** first-ring mode `A=a/√8` this yields
`‖(1-P) W A‖²=7/32`. Thus the external coupling is
*strictly nonzero* for the first compact mode. It cannot be
replaced by a closed two-by-two matrix without approximation.

This result is static. If the full complex Schrödinger evolution
under `K_*+εW` is constructed and a constant edge pulse is switched
on at time zero starting in `A`, a standard short-time expansion
formally predicts

```text
‖(1-P) ψ(τ)‖² = (7/32) ε² τ² + o(τ²) .
```

Deriving that asymptotic *inside Lean* requires the complex
dynamical construction; it is **not** yet a certified theorem.
Moreover, strictly positive short-time leakage does not prohibit
a later exact return of all external amplitudes to zero for a
specially shaped pulse. Arbitrarily accurate preparation and
exact zero final leakage remain separate open questions.

## A route to uniformly small leakage under long, weak pulses

An important issue is that a **weak** edge pulse may have to last
time proportional to `1/|ε|` to produce a useful two-mode rotation.
Therefore a crude bound proportional to `|ε| × pulse duration`
does not show that final leakage tends to zero.

The new abstract Lean module
[`QubitLeakagePulseBound.lean`](../SpectralGeometry/QubitLeakagePulseBound.lean)
isolates a stronger and more useful mechanism: **stability of an
isolated spectral cluster**. If `P` projects onto the original
two-mode eigenspace, `S` onto a nearby invariant perturbed
two-dimensional subspace, and `U` is any norm-preserving linear
evolution commuting with `S`, then an initial `x` with `Px=x`
satisfies

```text
If  ‖(P-S)y‖ ≤ d ‖y‖  for every y,
then ‖(I-P) U x‖ ≤ 2 d ‖x‖ .
```

For a normalized state, the **squared norm** of leakage is
`≤4d²` (provided `d≥0`). There is **no pulse-duration
factor** in this estimate; the result is a direct consequence
of the triangle inequality and invariance of the perturbed
spectral plane. The generic real normed-space lemma has
passed Lean CI; it neither constructs `S` nor identifies `U`
with the actual infinite-graph Schrödinger propagator.

**Remaining graph-specific theorem obligations:**

1. Prove the isolated two-dimensional spectral cluster survives
   sufficiently weak edge changes and construct its orthogonal
   spectral projection `P_ε` on the complexified graph Hilbert space.
2. Use the already proved gap at `E_*` to derive an explicit
   bound `‖P_ε-P‖≤d(ε)`, where `d(ε)→0` as `ε→0`.
3. Define the true unitary `U_ε(T)` of the unbounded
   natural-domain Hamiltonian, prove it commutes with `P_ε`,
   and instantiate the generic lemma. This would control **all**
   external modes throughout a long weak pulse and at switch-off.
4. Separately prove a **nontrivial desired rotation** inside
   the qubit plane, and then use detuning to adjust the complex
   relative phase. Small leakage by itself is not state preparation.

The new full natural-domain two-control *static* identity in
[`AmmannBeenkerQubitLeakage.lean`](../SpectralGeometry/AmmannBeenkerQubitLeakage.lean)
also gives the exact off-plane Hamiltonian response for a
real input `ra+sb`:

```text
‖(I-P) (K_(t_*+δ) + εW) (r a+s b)‖²
    = (7/4) ε² (r-s)² .
```

The detuning `δ` has **zero direct off-plane effect**.
But this equality is about the instantaneous operator action,
not the accumulated leakage under a pulse, and does not
supersede the spectral-projector stability proof.

## Making the crossing gap into an actual stability inequality

The gap `g=1/128` and the exact **rank-one edge norm**
`‖W‖=2` permit an explicit perturbative calculation in the
original infinite real Hilbert space. For any full-domain
eigenvector `x` of `K_*+εW` at energy `λ`, the exact identity

```text
(K_* - E_*) x = (λ-E_*) x - ε W x
```

holds. If the reduced-gap residual inequality

```text
g ‖(1-P)x‖ ≤ ‖(K_* - E_*)x‖
```

is available, the triangle inequality gives

```text
g ‖(1-P)x‖ ≤ (|λ-E_*| + 2|ε|) ‖x‖ .
```

In particular, if `|λ-E_*|≤2|ε|`,

```text
‖(1-P)x‖ ≤ 512|ε| ‖x‖ .
```

The module
[`AmmannBeenkerNearCrossingEigenvectors.lean`](../SpectralGeometry/AmmannBeenkerNearCrossingEigenvectors.lean)
proposes this precise eigenvector bound, **conditional on the
residual inequality and the eigenvalue window**. No dynamical
claim is involved.

**Why the residual inequality should follow from the proved gap.**
The separate
[`DomainEigenbasisGapResidual.lean`](../SpectralGeometry/DomainEigenbasisGapResidual.lean)
uses a complete real domain eigenbasis and Parseval to prove a
generic gap-to-residual theorem: on vectors having no component
at energy `E_*`, the norm of `(K-E_*)x` is at least
`g‖x‖`. The graph-specific lemma
`crossingReducedGapResidualEstimate_of_domainEigenbasis`
then combines that result with the **already proved** exact
two-dimensional `E_*` eigenspace and the spectral exclusion
within `1/128`.

The latest source now additionally declares
`crossingReducedGapResidualEstimate_full`, which **builds the
complete crossing eigenbasis** with the repository's existing
`onsitePlusBounded_exists_orderedEigenbasis` theorem and obtains
operator symmetry using `finiteSectorCorrection_symmetric`.
It therefore proposes the reduced-gap norm inequality as a
theorem of the **actual infinite graph, with no extra gap
hypothesis**. This is a new code change and **requires Lean CI**.

The latest `crossingEdge_perturbed_eigenvector_gap_bound_full`
then applies the unconditional gap statement to every genuine
edge-perturbed eigenvector. Its `512|ε|` specialization still
requires the displayed energy-window condition for the selected
perturbed eigenvalue; the perturbed spectral projector is not
yet constructed.

The eigenvector bound is a **one-sided** closeness result for
individual perturbed eigenvectors. Completing the desired
uniform-in-time leakage theorem additionally requires the
two-dimensional perturbed spectral cluster, its orthogonal
projector `P_ε`, an operator norm bound
`‖P_ε-P‖→0`, and an actual complex unitary pulse propagator.

## A direct time-uniform bound from energy-residual conservation

There is now a route to small leakage that **does not require
constructing the perturbed two-dimensional spectral projector**.
It uses the full crossing reduced-gap inequality already proved
in Lean in §4.84:

```text
(1/128) ‖(I-P)y‖ ≤ ‖(K_* - E_*)y‖ .
```

For a fixed edge strength `ε`, introduce the *perturbed
crossing-energy residual*

```text
R_ε(y) := (K_* + εW - E_*)y .
```

Suppose `x` is an exact initial crossing eigenstate,
`K_* x = E_* x`, and `y` is the full final state of a
constant-strength pulse, both in the natural domain.
The two central conservation laws are

```text
‖y‖ = ‖x‖
‖R_ε(y)‖ = ‖R_ε(x)‖ .
```

They are the familiar invariants of unitary evolution under a
fixed self-adjoint Hamiltonian, but a full complex Schrödinger
propagator for our graph has **not yet been constructed in Lean**.
The new module
[`AmmannBeenkerPulseResidualBound.lean`](../SpectralGeometry/AmmannBeenkerPulseResidualBound.lean)
therefore takes these two conservation laws as explicit hypotheses
and derives

```text
‖(I-P)y‖ ≤ 512 |ε| ‖x‖ .
```

For `‖x‖=1`, the squared external norm is at most
`(512|ε|)^2`. The key calculation is

```text
(1/128) ‖(I-P)y‖
    ≤ ‖(K_* - E_*)y‖
    ≤ ‖R_ε(y)‖ + |ε| ‖Wy‖
    = ‖R_ε(x)‖ + |ε| ‖Wy‖
    = |ε| (‖Wx‖ + ‖Wy‖)
    ≤ 4|ε| ‖x‖ .
```

The edge norm `‖W‖=2` is exact for the infinite graph.
There is **no pulse-duration factor** in the final estimate,
and we have avoided constructing any perturbed projector.

The missing dynamics is now particularly focused: show that
the fixed real-operator calculation extends appropriately to
the complexified self-adjoint graph Hamiltonian; construct the
unitary `U_ε(T)`, prove it preserves the natural domain,
norm, and the `R_ε`-norm, and instantiate the new theorem with
`y=U_ε(T)x`. To claim arbitrary target preparation we
must **separately** prove controllable transfer and complex
relative phase inside A/B; even a perfect leakage estimate
does not imply a useful rotation. The full real-space
conditional leakage theorem has passed Lean CI.

The nearby-projector approach above remains independently
valuable for tracking the moving spectral subspace and
its effective two-level dynamics. The conserved-residual
approach is a shortcut *specifically for bounding leakage*
during a fixed-Hamiltonian segment. When switching between
several controls, residual conservation has to be addressed
piece by piece.

## Intertwining replaces the residual-conservation assumption

The new
[`AmmannBeenkerPulseIntertwining.lean`](../SpectralGeometry/AmmannBeenkerPulseIntertwining.lean)
makes the needed dynamics more explicit, while still **not**
constructing it. Consider a real-linear isometry `U` acting
on the complete infinite-graph Hilbert space, with:

- `U(D(K_ε))⊆D(K_ε)` for the full natural domain; and
- `K_ε Ux = U K_ε x` for every `x∈D(K_ε)`,
  where `K_ε=K_*+εW` uses exactly the selected edge.

Then the residual identity and norm conservation follow
**as theorems rather than assumptions**:

```text
R_ε(Ux) = U R_ε(x)
‖R_ε(Ux)‖ = ‖R_ε(x)‖
R_ε = K_ε - E_*
```

For initial `K_* x=E_* x`, the earlier gap argument gives

```text
‖(I-P)Ux‖ ≤ 512 |ε| ‖x‖ .
```

For any *supplied* time family `U_ε(τ)` satisfying the
same three operator conditions at every time, this bound
is uniform over all `τ∈ℝ`, and its squared-norm version
holds for unit initial states.

**What this changes:** we no longer have to independently
verify conservation of the residual norm *once* domain
invariance, Hamiltonian commutation, and isometry have been
established. These three obligations are explicit.

**What is still open:** the physical complex Schrödinger
unitary group and its domain invariance are not constructed.
An arbitrary real-linear isometry is not automatically the
physical quantum evolution, and this theorem does not
certify any A/B rotation or universal qubit control.
This intertwining module and the underlying §4.85
conserved-residual theorem have passed Lean CI.

## The real pulse Hamiltonian is itself self-adjoint

The new
[`AmmannBeenkerPulseSelfAdjoint.lean`](../SpectralGeometry/AmmannBeenkerPulseSelfAdjoint.lean)
specializes the repository's existing Mathlib
`LinearPMap` self-adjointness theory to the actual
connecting edge `u=(1,0,0,0)`, `v=(1,1,0,0)`.
It packages

```text
K_ε = onsitePlusBounded potential
         (ringInteraction crossingParameter + ε • crossingEdge)
```

as a partially defined real-linear operator with exactly
the original natural onsite domain. It then proves, for
every `ε∈ℝ`, the symmetry of the bounded correction
and the stated `IsSelfAdjoint` property of the full
infinite-graph partial operator.

This real self-adjointness theorem has **no weak-pulse
assumption**, uses no finite graph, and is stronger than
merely observing that all displayed eigenvalues are real.

It is an analytic input toward constructing physical
complex unitary dynamics. However, real self-adjointness
in the current representation is **not itself** a
constructed complex Schrödinger propagator.
Complexification, the one-parameter unitary group,
natural-domain invariance and commutation with its
generator remain explicitly open. The real self-adjointness
declaration has passed Lean CI.

## Switching the selected edge OFF: a two-segment leakage estimate

[`AmmannBeenkerPostpulseSwitchOff.lean`](../SpectralGeometry/AmmannBeenkerPostpulseSwitchOff.lean)
addresses the first *piecewise-constant* protocol in the
original infinite graph.

Fix the same connecting edge `W` and a pulse strength `ε`.
Let `x` be a crossing eigenvector and `y` the state after
a constant-strength pulse. Suppose the pulse preserves its
norm and the `K_ε-E_*` residual norm:

```text
‖y‖ = ‖x‖,
‖(K_ε-E_*)y‖ = ‖(K_ε-E_*)x‖,
K_ε = K_* + εW .
```

At the instant the control is turned off, the important
quantity for **free** evolution is the *other* residual
`(K_*-E_*)y`. Its exact estimate is

```text
‖(K_*-E_*)y‖ ≤ 4|ε|‖x‖ .
```

If the subsequent unperturbed segment preserves the
norm of this unperturbed residual, then for *any* later
state `z` in the natural domain,

```text
‖(I-P)z‖ ≤ 512|ε|‖x‖ .
```

This is proved with the actual gap `1/128`, without
supposing the two segment Hamiltonians share their
residual conservation law. The new source also has
theorems for supplied norm-preserving, domain-preserving
intertwining maps, with **both segment durations**
arbitrary. No time factor appears.

All evolution families are still **hypotheses** on the
real Hilbert space; we do not yet have the physical
complex Schrödinger group or constructive state
preparation. This conditional ON/OFF theorem has passed
Lean CI.

## Exact dark-state quantum phase as a real/imaginary Schrödinger solution

The module
[`AmmannBeenkerDarkSchrodinger.lean`](../SpectralGeometry/AmmannBeenkerDarkSchrodinger.lean)
starts a genuinely **complex-phase** dynamical construction
without postulating the general quantum evolution.

We already know exactly that the normalized dark vector
`dark=(compactA+compactB)/4` is an eigenvector of the
complete selected-edge Hamiltonian `K_ε=K_*+εW`
at energy `E_*` for every real `ε`.

Therefore its explicit complex Schrödinger trajectory is

```text
ψ(τ) = exp(-i E_* τ) dark ,
Re ψ(τ) = cos(E_* τ) dark ,
Im ψ(τ) = -sin(E_* τ) dark .
```

We formalize both components in the full real
infinite-graph Hilbert space, provide their lifts
to the original unbounded operator domain,
and prove the **derivative** identities

```text
∂τ(Re ψ) = K_ε(Im ψ) ,
∂τ(Im ψ) = -K_ε(Re ψ) .
```

These are exactly the real and imaginary equations
of `i ∂τ ψ=K_ε ψ` for the particular dark trajectory.
Its initial state is dark, its total complex squared norm
`‖Re ψ‖²+‖Im ψ‖²` is one at every time, and
both components have **zero A/B leakage** at every time.

This is not a generic complex unitary group,
nor a solution for arbitrary superpositions, nor
a proof of nontrivial A/B controllability.
It does show that one exact complex-phase trajectory
with physical Schrödinger sign conventions is already
accessible from the certified real eigenstate.
This exact dark-state phase module has passed Lean CI.

## An obstruction to edge-only state preparation

The original repository proves this for the unnormalized vector
`a+b`, and the new `crossingDark_full_eigenvector` declaration
states it for the normalized dark vector on the **full natural domain**:
`(K + ε W) D = E_* D` for **every** real `ε`.
This is an exact static identity, not a dynamical theorem.

Assume a well-defined unitary Schrödinger evolution generated by
`K + ε(τ) W`, with only this edge varied in time and the eight-site
parameter held at its crossing value. Because `D` is a common
eigenvector at all times, its occupation probability is conserved:

```text
|⟨D, ψ(τ)⟩|² = |⟨D, ψ(0)⟩|² .
```

Starting from `ψ(0) = A`, the conserved value is exactly **1/2**.
Therefore **an edge-only pulse cannot prepare `D` from `A`**, nor
can it prepare the bright state `Q` from `A`, irrespective of
how the pulse is shaped. This holds even if the evolution temporarily
excites other energy levels.

For a normalized target `ψ_target = α A + β B` *entirely in the two-mode
plane*, a necessary condition for exact edge-only reachability from
`A` is

```text
|α + β|² = 1,  or equivalently  Re(conj(α) β) = 0.
```

For **real** coefficients, the necessary condition forces `αβ = 0`:
no nontrivial real-coefficient superposition in the two-mode plane can
be prepared from `A` using the edge alone. Relative-phase superpositions
such as `(A + i B)/√2` satisfy the necessary condition, but their
reachability is not yet proved.

**What is and is not formalized:** the existing and new Lean results
are over the *real* Hilbert space. The conservation argument above is a
mathematical deduction in the *complex* unitary-dynamics model; the
complexification, time-dependent propagator, and its hypotheses still
need formalization. Do not label the dynamical no-go as a Lean theorem
until that is accomplished.

## Candidate protocol and the next theorem

In the **projected** two-mode model, a constant edge pulse separates
the phases of `D` and `Q` at the rate `ε/4` in units `ℏ = 1`.
An initial `A = (D + Q)/√2` acquires a relative phase, suggesting
reachable superpositions with a relative factor of `i`, as well as
transfer towards `B`. These formulas are **not** automatically exact
for the full infinite graph.

The useful next result would be a rigorous **reachability and obstruction
theorem for the infinite graph**: (1) certify the conserved dark
occupation for any allowed edge-only pulse, (2) exhibit an explicit pulse
that prepares at least one nontrivial, controllable superposition to a
stated accuracy, (3) bound leakage to all other modes using the existing
spectral isolation theorem, and (4) explain what a second control
(such as detuning the eight-site parameter `t`) adds if one wants a
general target superposition.

**A two-control candidate.** The original eight-site parameter `t` is
an exact *phase* control on the two compact modes: changing `t` does
not mix their amplitudes. A promising pulse sequence is therefore:

1. Change the single edge by a small constant `ε` for a controlled
   duration, aiming to create a relative complex phase and transfer
   amplitude between `A` and `B`.
2. Restore that edge, then detune `t` for a chosen duration to adjust
   the relative phase without further mixing within the compact plane.
3. Restore `t` to the crossing value and estimate the preparation
   error and residual population outside the compact plane.

For example, in the *projected* model, an edge pulse giving a
dark/bright phase difference of `π/2` creates
`(A + i B)/√2` up to a global phase, and a subsequent `t` pulse
can rotate the relative phase to make `(A + B)/√2`. This **does not**
prove that the first pulse is an accurate operation in the infinite graph.

A possible rigorous method is to isolate the moving bright eigenstate
under a small fixed edge change, prove that it stays near `Q` using the
existing gap, estimate its energy shift, and use these estimates to
control a long but weak edge pulse. Then use the *exact* `t`-eigenvector
relations for phase adjustment. An explicit error bound must account for
both leakage and accumulated phase error; none is established yet.

One possible **future theorem statement**, deliberately still conjectural,
is: for any normalized complex target `α A + β B` and any chosen
accuracy `η > 0`, there are finite, piecewise-constant edge and
eight-site-control pulses, both returned to their crossing values at
the end, whose unitary evolution maps `A` to within distance `η`
of that target **up to a global phase**. The error estimate would include
every unwanted mode of the infinite system. Alongside it, a no-go
statement would rule out an arbitrary target under edge-only control,
using conservation of the dark occupation.

This offers a **candidate for a future Palomar-selected theorem**:
a quantitative, approximate two-control preparation protocol with a
precise edge-only impossibility statement. It requires full proof and
an independent novelty assessment. The
[existing registered selection](../PALOMAR.md), its ID, and its
Challenge/Comparator files are deliberately left unchanged.
