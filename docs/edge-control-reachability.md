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
natural domain. These are algebraic facts, **not proofs of pulse
existence or unitary dynamics** (the new module's CI is pending).

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
