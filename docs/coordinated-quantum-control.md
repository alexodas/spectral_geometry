[← Main README and table of contents](../README.md)

# 4. Infinite-dimensional geometric operators and spectral theory — §§4.99–4.111

**Chapter 4 navigation:** [4.1–4.67. Infinite-dimensional spectral theory](infinite-spectral-theory.md) · [4.68–4.79. Ammann–Beenker geometry and the compact crossing](ammann-beenker-geometry.md) · [4.80–4.98. Single-edge control and spectral splitting](single-edge-control.md) · **4.99–4.111. Coordinated quantum control and spectral protection**

<details>
<summary>Contents of this document</summary>

- [4.100. Exact invariant-plane control and Pauli generator algebra](#4100-exact-invariant-plane-control-and-pauli-generator-algebra)
- [4.101. Full Lie generation and constructive two-state rotations](#4101-full-lie-generation-and-constructive-two-state-rotations)
- [4.102. Exact natural-domain Schrödinger trajectories for both control axes](#4102-exact-natural-domain-schrödinger-trajectories-for-both-control-axes)
- [4.103. Exact identification of physical pulses with Pauli rotations](#4103-exact-identification-of-physical-pulses-with-pauli-rotations)
- [4.104. Continuous three-pulse protocol with exact zero leakage](#4104-continuous-three-pulse-protocol-with-exact-zero-leakage)
- [4.105. Exact arbitrary target preparation from dark without leakage](#4105-exact-arbitrary-target-preparation-from-dark-without-leakage)
- [4.106. Sharp coordinated-control norms and exact bounded perturbation](#4106-sharp-coordinated-control-norms-and-exact-bounded-perturbation)
- [4.107. Exact controlled plane energies and natural-domain reduction](#4107-exact-controlled-plane-energies-and-natural-domain-reduction)
- [4.108. Quantitative exclusion of exterior real spectral levels](#4108-quantitative-exclusion-of-exterior-real-spectral-levels)
- [4.109. Consolidated quantitative isolation of the controlled cluster](#4109-consolidated-quantitative-isolation-of-the-controlled-cluster)
- [4.110. Spectral protection during coordinated control](#4110-spectral-protection-during-coordinated-control)
- [4.111. Exact protected state preparation with arbitrarily weak controls](#4111-exact-protected-state-preparation-with-arbitrarily-weak-controls)

</details>

### 4.99. Coordinated eight-edge matching and exact dark cancellation

[`AmmannBeenkerCoordinatedRingControl.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedRingControl.lean)
starts L7a on the complete infinite real Ammann–Beenker Hilbert space.
It retains the existing graph, compact modes and single-edge results;
the coordinated perturbation is a different finite local intervention.

**Geometry and bounded correction.** For each `i : Fin 8`, pair the actual
vertices `firstRingVertex i` and `secondRingVertex i`. The pairs are
genuine adjacent edges, distinct, and have no shared endpoints. Write
`u_i` for their infinite edge vector (the difference of the two unit site
vectors), and define the bounded real continuous linear operators

```math
M=\sum_{i=0}^{7} W_i,\qquad W_i x=\langle u_i,x\rangle u_i.
```

Each term uses the same unit-increment Laplacian convention as
`crossingEdge`. The eight-edge sum is symmetric on the entire Hilbert
space. Its range is contained in the span of the eight edge vectors by
the displayed definition; the new module does not separately certify
a rank or operator-norm formula.

**Exact dark cancellation.** The matched amplitudes obey

```math
a(A_i)=b(B_i),\qquad a(B_i)=b(A_i)=0.
```

Thus for the normalized dark state `D=(a+b)/4`, every edge has zero
endpoint difference, so `W_i D=0` and `M D=0`. These equations hold on
the full infinite Hilbert space, not just after compression onto the
two-mode plane.

**New definitions:** `coordinatedRingPair`, `coordinatedRingEdge`,
`coordinatedRingControl`.

| Lean theorem | Verified content |
| --- | --- |
| `coordinatedRingPair_adjacent` | Every matched pair is adjacent in the actual graph |
| `coordinatedRingPair_injective` | The eight indexed pairs are distinct |
| `coordinatedRing_disjoint` | First- and second-ring vertices never coincide |
| `coordinatedRing_matching` | Distinct pairs have no common endpoint |
| `coordinatedRingEdge_apply` | Exact full-space action of each rank-one correction |
| `coordinatedRingControl_apply` | Exact full-space sum action |
| `coordinatedRing_amplitudes` | Equal corresponding amplitudes and zero cross-ring values |
| `coordinatedRingEdge_dark_zero` | Each individual edge annihilates dark |
| `coordinatedRingControl_dark_zero` | The coordinated sum annihilates dark |
| `coordinatedRingEdge_symmetric` | Each term is symmetric on the full real space |
| `coordinatedRingControl_symmetric` | The sum is symmetric on the full real space |

**Verification and subsequent result.** All eleven theorems and three
definitions are Lean-verified. Dark cancellation alone does not prove
invariance of the two-mode plane; the subsequent §4.100 establishes
that stronger result. The single-edge approximate-control route remains
a distinct research direction. Neither new module was selected in the historical L5 Comparator.
The third registered package includes the local-edge certificates from this module.

<a id="4100-proposed-invariant-plane-and-pauli-algebra-proofs-ci-pending"></a>

### 4.100. Exact invariant-plane control and Pauli generator algebra

**Plain-English result.** A change to one connecting edge generally
pushes part of the bright wave into the rest of the infinite network.
Changing all eight matched edges by the same amount is different:
the contributions combine exactly to preserve the two original
localized patterns as a space. The dark wave is unchanged by this
coordinated correction, while the bright wave receives twice the
edge-strength change in energy. No exterior component is produced by
the operator acting on any mixture of the two patterns. Combining this
correction with first-ring detuning still preserves that same space.
The statement holds for arbitrary real control strengths, not merely
small perturbations, and uses the full infinite operator.

**L7a — exact full-space invariance.** The module
[`AmmannBeenkerCoordinatedInvariantPlane.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedInvariantPlane.lean)
proves the following identities for the already defined unnormalized
compact modes `a,b`, normalized modes `D=(a+b)/4`, `F=(a-b)/4`,
and orthogonal components `P,Q=I-P`:

```math
Ma=a-b,\qquad Mb=b-a,\qquad MD=0,\qquad MF=2F,\qquad QMP=0.
```

The proof evaluates the sum of local edge corrections at every vertex.
On either ring exactly one matched edge contributes; away from both
rings all eight contributions and both compact modes vanish. This
proves an identity in the infinite Hilbert space, not merely in a
finite central block or a projected matrix.

For real detuning `δ`, coordinated strength `η` and real coefficients
`r,s`, the natural-domain Hamiltonian
`H(δ,η)=onsitePlusBounded potential (ringInteraction (crossingParameter+δ)+η M)`
acts exactly as

```math
H(\delta,\eta)(ra+sb)
=\big[(E_*+\delta+\eta)r-\eta s\big]a
+\big[(E_*+\eta)s-\eta r\big]b.
```

The left-hand side uses the natural-domain lifts of the compact modes.
The output belongs to the same compact plane and to the natural domain.
Its orthogonal exterior component is zero.

**L7b — exact effective matrix.** In the ordered normalized basis
`(D,F)`, the full-operator action therefore has the exact matrix

```math
H_{\mathrm{eff}}=\begin{pmatrix}
E_*+\delta/2&\delta/2\\
\delta/2&E_*+\delta/2+2\eta
\end{pmatrix}
=(E_*+\delta/2+\eta)I+(\delta/2)\sigma_x-\eta\sigma_z.
```

The scalar multiple of the identity affects only a common phase in
the corresponding Schrödinger model. The detuning and coordinated-edge
controls act along two different Pauli directions, so their order
matters. The module
[`AmmannBeenkerCoordinatedLieAlgebra.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedLieAlgebra.lean)
defines the complex matrices `X=iσ_x`, `Y=iσ_y`, `Z=iσ_z`
and proves, with `[A,B]=AB-BA`,

```math
[X,Z]=2Y,\qquad [Z,Y]=2X,\qquad [Y,X]=2Z.
```

It also proves noncommutation and the explicit real-coordinate
parametrization of the three generator directions. These are the
algebraic ingredients of the standard two-state rotation algebra.
The subsequent §4.101 establishes equality of the generated Lie algebra
with all of `su(2)` and constructive reachability by a three-rotation
matrix product. The subsequent §§4.102–4.105 realize these rotations
by actual infinite-system pulses, culminating in exact arbitrary
normalized target preparation from dark up to global phase.

| Lean theorem | Meaning |
| --- | --- |
| `coordinatedRingControl_compactA`, `coordinatedRingControl_compactB` | Exact action on both compact modes |
| `coordinatedRingControl_bright`, `coordinatedRingControl_pair` | Bright response and arbitrary real compact combination |
| `coordinatedRingControl_offplane_zero` | Zero exterior component of the coordinated correction on the plane |
| `coordinatedControls_compact_action` | Exact full natural-domain action of both controls |
| `coordinatedControls_offplane_zero`, `coordinatedControls_domain_invariant` | Plane and domain invariance |
| `coordinatedControls_dark_bright_action` | Exact action in normalized dark/bright coordinates |
| `coordinatedEffectiveMatrix_pauli` | Pauli decomposition of the real matrix |
| `coordinatedLie_XZ`, `coordinatedLie_ZY`, `coordinatedLie_YX` | Three complex commutator identities |
| `coordinatedLie_noncommuting` | The two control directions do not commute |
| `coordinatedLie_coordinates` | Explicit real-coordinate parametrization |

**Status and limits.** All fifteen public theorems, five private
coordinate-evaluation lemmas and four new definitions are Lean-verified.
L7a is complete; this section supplies the matrix and generator-algebra
foundation of L7b, completed at the algebraic level in §4.101.
The subsequent §4.102 establishes exact single-axis Schrödinger trajectories
with zero leakage at every time. Section 4.103 identifies their rotation
matrices including the common phase; §4.104 proves their continuous
three-pulse composition with exact zero leakage throughout. Section 4.105
proves arbitrary normalized target preparation from dark up to global phase.
The registered L7 package selects the final preparation theorem and supporting locality certificates (§4.105).
The original single-edge L1–L6 route and Track A remain distinct.


### 4.101. Full Lie generation and constructive two-state rotations

**Plain-English result.** The two available controls are enough to
generate every infinitesimal rotation of a two-state quantum system,
after a common energy shift is removed. Moreover, one can explicitly
choose three rotation angles that transform the dark coordinate into
any normalized pair of complex amplitudes. This is a theorem about
exact matrices; this section alone does not construct the time evolution
of the infinite Ammann–Beenker graph. That construction is provided by
§§4.102–4.105.

**Full Lie generation.** In
[§4.100](#4100-exact-invariant-plane-control-and-pauli-generator-algebra)
the two independent traceless generator directions were identified
as X = iσ_x and Z = iσ_z, with [X,Z] = 2Y and Y = iσ_y.
The new module
[`AmmannBeenkerCoordinatedLieGeneration.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedLieGeneration.lean)
defines the real vector space

```math
\mathfrak{su}(2)=\{A\in M_2(\mathbb C): A^\dagger=-A,\ 
\operatorname{tr}A=0\}.
```

It proves that this space is closed under matrix commutators, contains
X and Z, and that each of its elements is a real linear combination
of X, Y and Z. Specifically,

```math
A=\operatorname{Im}(A_{01})X+\operatorname{Re}(A_{01})Y+
\operatorname{Im}(A_{00})Z.
```

Any real linear subspace closed under commutators and containing X
and Z must also contain Y, since Y = [X,Z]/2. Consequently it must
contain every element of su(2). Together with closure of su(2) itself,
this proves that it is exactly the smallest such subspace. This is
a concrete, two-sided Lie-generation theorem rather than just a
calculation of three commutators.

**Constructive Euler state reachability.** In
[`AmmannBeenkerCoordinatedEuler.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedEuler.lean)
the two matrix rotations are defined by

```math
R_x(t)=\begin{pmatrix}\cos t&i\sin t\\i\sin t&\cos t\end{pmatrix},
\qquad
R_z(t)=\begin{pmatrix}e^{it}&0\\0&e^{-it}\end{pmatrix}.
```

The parameters here are half-angles in the Bloch-sphere convention.
For any real p, t, q the first column of the product is exactly

```math
R_z(q)R_x(t)R_z(p)\binom{1}{0}
=\binom{\cos t\,e^{i(p+q)}}{i\sin t\,e^{i(p-q)}}.
```

Given arbitrary complex amplitudes α and β with
|α|² + |β|² = 1, the proof constructs

```math
u=\arg(\alpha),\quad v=\arg(-i\beta),\quad
t=\arccos|\alpha|,\quad p=(u+v)/2,\quad q=(u-v)/2.
```

Then 0 ≤ t ≤ π/2 and the displayed product is exactly (α,β),
including the cases in which one amplitude is zero. The theorem
states existence of the three real angles; the proof gives these
explicit witnesses. It reaches the exact complex pair in the
rotation-matrix model, not merely its magnitudes.

In the full-operator restriction the scalar energy
E_* + δ/2 + η contributes a common phase. After removing it, the
Schrödinger generator has the two independently selectable
coefficients

```math
G(\delta,\eta)=-\frac{\delta}{2}X+\eta Z.
```

Lean proves G(-2t,0)=tX and G(0,t)=tZ for every real t.
Thus a unit-duration segment with signed detuning -2t or signed
coordinated edge strength t has the required algebraic generator
coefficient. This identifies the settings for the idealized
three-segment protocol, assuming independently tunable arbitrary
real control strengths. No nonnegativity restriction on the physical
edge weights or bounded-strength hardware constraint is imposed by
this theorem. The equality between these rotations and the actual single-axis
natural-domain trajectories, including the common phase, is proved in
§4.103. The continuous switched protocol is proved in §4.104;
its arbitrary-target endpoint theorem is proved in §4.105. A general
complex full-space propagator remains separate.

| Lean theorem | Meaning |
| --- | --- |
| `coordinatedSu2_commutator` | Closure under matrix commutators |
| `coordinatedSu2_X`, `coordinatedSu2_Z` | Both control directions belong to su(2) |
| `coordinatedSu2_coordinates` | Every traceless skew-Hermitian matrix has three real Pauli coordinates |
| `coordinatedSu2_le_of_controls` | Every commutator-closed real subspace containing X and Z contains su(2) |
| `coordinatedSu2_generated_iff` | Exact generated-algebra characterization in both directions |
| `coordinatedPhase_add`, `coordinatedPhase_norm` | Phase multiplication and unit modulus |
| `coordinatedEuler_dark_column` | Explicit dark-state column of the Z–X–Z product |
| `coordinatedEuler_reaches_from_dark` | Every normalized complex pair is reached by the rotation product |
| `coordinatedReducedGenerator_X`, `coordinatedReducedGenerator_Z` | Independent signed generator coefficients |

**Status and limits.** The twelve public theorems and five definitions
are Lean-verified. L7b is complete at the algebraic level. The formal
result is state reachability from the dark coordinate in a
two-by-two matrix model; it does not assert a full SU(2) group
factorization theorem or arbitrary initial-state dynamics.
Section 4.102 constructs the exact single-axis full-graph Schrödinger
trajectories in real and imaginary components, with zero exterior component
throughout each segment. Section 4.103 proves the exact phase-weighted
rotation identification, and §4.104 proves continuous pulse composition
with zero leakage at every time. Section 4.105 proves the final arbitrary
target preparation theorem from dark. A general complex full-space propagator
remains open. The third registered package selects supporting locality statements and the final
preparation theorem; it does not independently select the Lie-algebra results. The original single-edge L6 goal and the
analytic spectral-geometry program remain separate.


### 4.102. Exact natural-domain Schrödinger trajectories for both control axes

**Plain-English result.** The coordinated controls preserve the two
localized waves not only when the Hamiltonian acts on them, but also
during explicit time-dependent solutions. For either control used
alone, every complex combination of the two waves evolves with
exactly conserved total squared amplitude. Neither its real part nor
its imaginary part ever develops a component outside the original
two-state space. This is a dynamical theorem for the actual infinite
graph, not a calculation on a truncated graph or an assumption about
a supplied propagator.

**General two-eigenmode construction.** The module
[`AmmannBeenkerCoordinatedPairDynamics.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedPairDynamics.lean)
takes any two real eigenvectors x,y on the original natural onsite
domain, with respective real eigenvalues E,F for the same
onsite-plus-bounded operator H. For arbitrary complex coefficients a,b
it defines

```math
c(\tau)=a e^{-iE\tau},\qquad d(\tau)=b e^{-iF\tau},
\qquad
u(\tau)=\operatorname{Re}c(\tau)x+\operatorname{Re}d(\tau)y,\quad
v(\tau)=\operatorname{Im}c(\tau)x+\operatorname{Im}d(\tau)y.
```

The pair (u,v) represents the complex state u+iv. Both components
have explicit lifts to the natural domain for every real time. Their
initial values are the real and imaginary parts of the given
superposition. Differentiating the actual Hilbert-space vectors yields

```math
u'(\tau)=Hv(\tau),\qquad v'(\tau)=-Hu(\tau).
```

These are precisely the real and imaginary equations of
iψ'=Hψ for the componentwise complexification. The Hamiltonian
on the right is the full infinite operator applied to the
natural-domain lifts. The proof requires neither a finite-volume
approximation nor a pre-existing time-evolution map.

If x and y are orthogonal, the squared complex norm is conserved:

```math
\|u(\tau)\|^2+\|v(\tau)\|^2
=|a|^2\|x\|^2+|b|^2\|y\|^2.
```

If both eigenvectors have zero original-plane leakage, the two
components have zero leakage at every time. This follows from
linearity and is independent of the pulse strength or duration.

**Application to the two actual controls.** The module
[`AmmannBeenkerCoordinatedAxisDynamics.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedAxisDynamics.lean)
uses the following exact eigenpairs, without a spectral truncation.
Write a_0=compactA, b_0=compactB and D,F for the normalized dark
and bright modes.

| Control | Eigenvectors used | Exact energies |
| --- | --- | --- |
| First-ring detuning, η=0 | a_0, b_0 | E_*+δ, E_* |
| Eight coordinated edges, δ=0 | D,F | E_*, E_*+2η |

For the detuning control the compact eigenvectors are orthogonal
and each has squared norm eight; the conserved squared complex
norm is therefore 8(|a|²+|b|²) for their coefficients.
For the coordinated edge control the normalized dark and bright
vectors are orthogonal and the corresponding conserved norm
is |a|²+|b|². Both exact trajectories have zero leakage in both
components at every real time and for arbitrary real strengths.
Both bases span the original compact-mode plane.

**Self-adjointness on the full real space.** The bounded correction
is ringInteraction(crossingParameter+δ)+ηM. Lean proves symmetry
of this correction, identifies the associated unbounded real
partial linear operator with the full natural-domain Hamiltonian,
and proves self-adjointness for all real δ,η, including their
simultaneous use. This strengthens the earlier selected-edge
self-adjointness result. It does not by itself construct a complex
unitary group.

| Lean theorem | Meaning |
| --- | --- |
| `coordinatedEigenCoeff_initial`, `coordinatedEigenCoeff_norm` | Initial coefficient and exact constant modulus |
| `coordinatedEigenCoeff_re`, `coordinatedEigenCoeff_im` | Real trigonometric expressions for the phase |
| `coordinatedEigenCoeff_re_deriv`, `coordinatedEigenCoeff_im_deriv` | Exact scalar derivative identities |
| `coordinatedPair_domain_coe`, `coordinatedPair_initial` | Natural-domain lifts and initial conditions |
| `coordinatedPair_Schrodinger` | Both Hilbert-space Schrödinger derivative equations |
| `coordinatedPair_norm_sq`, `coordinatedPair_leakage_zero` | Conserved squared complex norm and exact zero leakage under the stated hypotheses |
| `coordinatedCorrection_symmetric` | Symmetry of the complete bounded correction |
| `coordinatedHamiltonianPMap_domain`, `coordinatedHamiltonianPMap_apply`, `coordinatedHamiltonianPMap_isSelfAdjoint` | Natural domain, full action and real self-adjointness |
| `coordinatedXAxis_eigenA`, `coordinatedXAxis_eigenB` | Exact compact eigenpairs under detuning |
| `coordinatedZAxis_eigenDark`, `coordinatedZAxis_eigenBright` | Exact dark/bright eigenpairs under coordinated edges |
| `coordinatedDarkBright_orthogonal`, `coordinatedBright_leakage_zero` | Orthogonality and bright confinement |
| `coordinatedXAxis_Schrodinger`, `coordinatedZAxis_Schrodinger` | Exact full-graph trajectory equations for each axis |
| `coordinatedXAxis_norm_sq`, `coordinatedZAxis_norm_sq` | Exact conserved squared complex norm on each axis |
| `coordinatedXAxis_leakage_zero`, `coordinatedZAxis_leakage_zero` | Zero exterior component of both real and imaginary parts at every time |

**Status and limits.** Twenty-seven public theorems, two private
supporting lemmas and seven definitions are Lean-verified.
L7c.1 is complete. These solutions use a real/imaginary representation
on the full graph with initial data in the compact plane. They are
not a general complex-Hilbert-space propagator for arbitrary initial
data. Section 4.103 (L7c.2) identifies the exact coefficient action
with the rotations of §4.101, including the scalar phases. Section 4.104
(L7c.3) joins the segments with matching initial and final states and
zero leakage throughout. Section 4.105 (L7c.4) proves arbitrary normalized
target preparation from dark up to global phase with zero leakage throughout. A general
complex unitary group remains a separate outstanding objective.
The final L7 preparation theorem is selected for the independently verified registered package (§4.105); the intermediate trajectory results are not separate submissions. The separate L6 and Track A goals are preserved.


### 4.103. Exact identification of physical pulses with Pauli rotations

**Plain-English result.** The rotations used to select a desired mixture
of the dark and bright waves are now proved to be the actual coefficient
evolution of the corresponding single-axis full-graph Schrödinger
trajectories. This identification retains the common complex phase,
rather than discarding it before comparing consecutive pulses. It
holds for every complex initial coefficient pair and every real
control strength and time.

The module
[`AmmannBeenkerCoordinatedRotationDynamics.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedRotationDynamics.lean)
defines the action of a two-by-two complex matrix on a pair of
coefficients, and the embeddings of their real and imaginary parts
into the full real graph Hilbert space:

```math
\mathcal E_{\mathrm{Re}}(a,b)=\operatorname{Re}(a)D+
\operatorname{Re}(b)F,\qquad
\mathcal E_{\mathrm{Im}}(a,b)=\operatorname{Im}(a)D+
\operatorname{Im}(b)F.
```

Here D and F are the original normalized dark and bright modes,
and E_* is their crossing energy. For the pure detuning pulse
of strength δ, write p=exp(-i(E_*+δ)τ) and q=exp(-iE_*τ).
The eigenmode phases in the original compact A/B basis give
the following exact matrix in the dark/bright basis:

```math
U_X(\delta,\tau)=
\frac12\begin{pmatrix}p+q&p-q\\p-q&p+q\end{pmatrix}
=e^{-i(E_*+\delta/2)\tau}R_X(-\delta\tau/2).
```

For the coordinated eight-edge pulse of strength η, the
dark/bright basis already consists of eigenvectors. Consequently,

```math
U_Z(\eta,\tau)=
\begin{pmatrix}e^{-iE_*\tau}&0\\0&e^{-i(E_*+2\eta)\tau}\end{pmatrix}
=e^{-i(E_*+\eta)\tau}R_Z(\eta\tau).
```

The rotation conventions are those of §4.101:
R_X(t)=cos(t)I+i sin(t)σ_x, and
R_Z(t)=diag(exp(it),exp(-it)).
The scalar phase in each identity has modulus one, and the
half-angle parameter is fixed by the corresponding energy difference.

**Connection to the infinite natural-domain trajectories.**
For input aD+bF the compact A/B coefficients are (a+b)/4 and
(a-b)/4, because D=(compactA+compactB)/4 and
F=(compactA-compactB)/4. Lean proves the coefficient conversion
and the full Hilbert-space identities for both components:
the detuning trajectory of §4.102 equals the real and imaginary
embeddings of U_X(a,b), and the coordinated-edge trajectory equals
those of U_Z(a,b). The same identities hold with the phase-weighted
rotation expressions substituted for the matrices. This connects
the matrix expressions directly to the previously proved
Schrödinger equations, natural-domain lifts, norm conservation
and zero leakage for each individual pulse. No full-space
propagator is assumed.

The two matrices equal the identity at time zero. The module
also establishes compatibility of the matrix action with
matrix multiplication, scalar multiplication of matrices and
common scaling of the input coefficients, and identifies
the first column as the action on the initial dark pair (1,0).
These facts are used in the exact composition of the three pulses in §4.104.

| Lean theorem | Meaning |
| --- | --- |
| `coordinatedApplyPair_mul` | Successive matrix actions equal the product action |
| `coordinatedApplyPair_smul`, `coordinatedApplyPair_scale_input` | Common scalar phases pass through matrix action |
| `coordinatedApplyPair_dark` | Dark input selects the first matrix column |
| `coordinatedPhase_trig` | Euler's formula for the phase convention |
| `coordinatedXAxisMatrix_rotation`, `coordinatedZAxisMatrix_rotation` | Exact phase-weighted rotation identities |
| `coordinatedXAxisMatrix_coefficients`, `coordinatedZAxisMatrix_coefficients` | Physical eigenmode coefficients in dark/bright coordinates |
| `coordinatedXAxis_trajectory_matrix`, `coordinatedZAxis_trajectory_matrix` | Equality with both full-graph trajectory components |
| `coordinatedXAxis_trajectory_rotation`, `coordinatedZAxis_trajectory_rotation` | Direct identification with phase-weighted rotations |
| `coordinatedXAxisMatrix_initial`, `coordinatedZAxisMatrix_initial` | Identity at zero time |

**Status and limits.** Fifteen public theorems, three private
supporting lemmas and five definitions are Lean-verified. L7c.2
is complete. For unit-duration pulses the X parameter t requires
δ=-2t and the Z parameter p requires η=p. The Z–X–Z protocol
uses independently tunable signed real strengths. Its composition
with matched endpoints and piecewise Schrödinger equations is
proved in §4.104 (L7c.3); its arbitrary-target theorem is proved in §4.105 (L7c.4).
A general unitary propagator on the full complex infinite Hilbert
space is not constructed by these results. The third registered package selects the final preparation theorem and supporting
locality statements; other intermediate results are not separate submissions. The original L6 approximate
control problem and Track A remain separate.


### 4.104. Continuous three-pulse protocol with exact zero leakage

**Plain-English result.** The separate pulses of §4.103 can now be
joined into a single continuous trajectory on the actual infinite
Ammann–Beenker graph. No amplitude or phase is reset at a switch.
Each pulse starts exactly where the preceding pulse ends. The
state remains in the original two-mode plane throughout the
protocol, including both switching times. Its squared complex
norm is conserved, and both real and imaginary parts satisfy
the full natural-domain Schrödinger equations during each open
pulse interval.

The module
[`AmmannBeenkerCoordinatedPulseComposition.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedPulseComposition.lean)
uses the exact physical coefficient matrices U_X and U_Z of
§4.103, including their common scalar phases. Let w=(a,b) be
any initial complex dark/bright coefficient pair. For arbitrary
real parameters p,t,q, use the following unit-duration controls:

| Time interval | Detuning δ | Coordinated edge strength η |
| --- | --- | --- |
| [0,1] | 0 | p |
| [1,2] | -2t | 0 |
| [2,3] | 0 | q |

The entries at a shared endpoint describe the left and right
control values; the state itself has a unique value there.
Define a continuous saturated clock

```math
c(s)=\min(\max(s,0),1).
```

It is zero before its interval, equals the local time inside it,
and is one afterwards. The coefficient trajectory is

```math
W(\tau)=U_Z(q,c(\tau-2))\,
U_X(-2t,c(\tau-1))\,
U_Z(p,c(\tau))\,w.
```

All three matrices retain their physical energy phases. The
identity-at-zero property gives W(0)=w and exact segment
matching. In particular,

```math
W(3)=U_Z(q,1)U_X(-2t,1)U_Z(p,1)w.
```

Lean proves the three closed-interval formulas and the two
switch identities. Continuity of the phase, each pulse with
respect to time and continuous input, and the saturated clock
gives continuity of W for every real time. The real and imaginary
full-space embeddings are continuous as well.

**Full-domain dynamics and conservation.** Write
u(τ)=E_Re(W(τ)), v(τ)=E_Im(W(τ)) with the embeddings of §4.103.
The module provides their explicit lifts to the original natural
onsite domain for every τ. On the open intervals (0,1), (1,2)
and (2,3) respectively, Lean proves

```math
u'(\tau)=H_{\delta,\eta}v(\tau),\qquad
v'(\tau)=-H_{\delta,\eta}u(\tau),
```

using the full infinite-graph Hamiltonian with the indicated
control strengths. The proof first identifies the single-pulse
equations in the common coordinates and then transfers them to
the global trajectory by time translation and local equality.
It does not impose differentiability at the control switches,
where the Hamiltonian can jump. Continuity and domain membership
hold there nonetheless. The saturated extension is constant
outside [0,3]; no physical evolution equation outside the
three open pulse intervals is asserted.

For every real τ the exact identities are

```math
\|u(\tau)\|^2+\|v(\tau)\|^2=|a|^2+|b|^2,\qquad
Qu(\tau)=Qv(\tau)=0.
```

Here Q is the exterior component of the original compact-plane
decomposition. Thus the squared complex exterior norm is exactly
zero, including at the switches and endpoints. For normalized
initial coefficients the total squared complex norm is one.
These statements do not use a perturbative small-strength
estimate, a finite graph truncation or a supplied propagator.

| Lean theorem | Meaning |
| --- | --- |
| `coordinatedApplyPair_one`, `coordinatedPulseX_initial`, `coordinatedPulseZ_initial` | Zero-time identity actions |
| `coordinatedState_domain`, `coordinatedState_leakage_zero` | Explicit natural-domain lifts and confinement of each embedded pair |
| `coordinatedStateWeight_eq`, `coordinatedPulseX_weight`, `coordinatedPulseZ_weight` | Squared complex norm and its single-pulse conservation |
| `coordinatedPhase_continuous`, `coordinatedPulseX_continuous`, `coordinatedPulseZ_continuous` | Continuity of phases and pulse actions |
| `coordinatedClock_zero`, `coordinatedClock_one`, `coordinatedClock_inside`, `coordinatedClock_continuous` | Saturated local-time clock |
| `coordinatedProtocol_first`, `coordinatedProtocol_second`, `coordinatedProtocol_third` | Exact closed-interval segment formulas |
| `coordinatedProtocol_initial`, `coordinatedProtocol_join_one`, `coordinatedProtocol_join_two`, `coordinatedProtocol_final` | Initial state, exact switch matching and final composition |
| `coordinatedProtocol_continuous`, `coordinatedProtocol_state_continuous` | Continuous coefficient path and both full-space components |
| `coordinatedProtocol_weight`, `coordinatedProtocol_leakage_zero`, `coordinatedProtocol_domain` | Conserved norm, zero leakage and natural-domain membership at all times |
| `coordinatedPulseX_solvesAt`, `coordinatedPulseZ_solvesAt` | Full natural-domain equations in common coordinates |
| `coordinatedSolvesAt_shift`, `coordinatedSolvesAt_congr` | Time translation and local equality of Schrödinger solutions |
| `coordinatedProtocol_solves_first`, `coordinatedProtocol_solves_second`, `coordinatedProtocol_solves_third` | Full switched trajectory solves the equations on each open interval |

**Status and limits.** Thirty-four public theorems and ten
definitions are Lean-verified. L7c.3 is complete. The construction
works for arbitrary initial coefficient pairs in the compact
plane and arbitrary real p,t,q. It supplies an actual continuous
piecewise differentiable full-graph trajectory in the real/imaginary
representation, not just a product of endpoint matrices.
Section 4.105 (L7c.4) combines the final coefficient product with the
constructive Euler reachability theorem of §4.101 to choose the
parameters for every normalized target from dark, retaining the
common scalar phase. The general complex Hilbert-space unitary
propagator for arbitrary infinite-space initial data remains a
separate objective. No experimental feasibility or minimal number
of controlled edges is claimed. The third registered package selects the final preparation theorem and locality
statements; the intermediate composition results are not separate submissions. L6 and Track A
remain preserved.


### 4.105. Exact arbitrary target preparation from dark without leakage

**Plain-English result.** Any normalized mixture of the two original
localized waves can be prepared from the dark wave by three consecutive
local control pulses on the actual infinite Ammann–Beenker graph.
The final state differs from the chosen target only by a common phase.
During the whole protocol no amplitude escapes the original two-mode
plane, the norm remains one, and the state is continuous. The two
real Hilbert-space components satisfy the exact natural-domain
Schrödinger equations on the open pulse intervals. This completes
the central L7 preparation objective without assuming a general
propagator or making a small-perturbation approximation.

The module
[`AmmannBeenkerCoordinatedExactPreparation.lean`](../SpectralGeometry/AmmannBeenkerCoordinatedExactPreparation.lean)
combines the constructive matrix reachability of §4.101 with the
actual phase-retaining trajectories of §§4.102–4.104.

**Exact final phase.** Let E_* be the crossing energy and D,F the
normalized dark and bright modes. The three unit-duration controls
are (δ,η)=(0,p),(-2t,0),(0,q). The physical endpoint matrix is

```math
U_Z(q,1)U_X(-2t,1)U_Z(p,1)
=e^{i\theta}R_Z(q)R_X(t)R_Z(p),
\qquad \theta=-3E_*+t-p-q.
```

The scalar factor has modulus one. This identity holds for arbitrary
real p,t,q, including when applied to any initial coefficient pair.
In particular the final coefficients starting from dark are

```math
e^{i\theta}\left(\cos(t)e^{i(p+q)},
i\sin(t)e^{i(p-q)}\right).
```

For a chosen complex pair (α,β) with |α|²+|β|²=1, the earlier
constructive Euler proof chooses t=arccos|α|, with
0≤t≤π/2, and p=(u+v)/2, q=(u−v)/2, where u=arg(α)
and v=arg(−iβ). Its phase identities also cover zero coefficients.
Thus there exist p,t,q for which the physical endpoint is exactly
e^{iθ}(α,β). The phase is not removed between pulses.

**Bundled full-graph theorem.** The theorem
`coordinatedProtocol_exact_preparation` proves the existence
of those parameters and all of the following properties for
the same trajectory f=coordinatedProtocolPair p t q (1,0).
Writing u and v for its real and imaginary full-space embeddings,
the initial state is u(0)=D, v(0)=0, and the final components are

```math
u(3)=\operatorname{Re}(e^{i\theta}\alpha)D+
      \operatorname{Re}(e^{i\theta}\beta)F,\qquad
v(3)=\operatorname{Im}(e^{i\theta}\alpha)D+
      \operatorname{Im}(e^{i\theta}\beta)F.
```

The coefficient path and both graph components are continuous.
For every real time both components belong to the original
natural onsite domain, and

```math
\|u(\tau)\|^2+\|v(\tau)\|^2=1,\qquad
Qu(\tau)=Qv(\tau)=0.
```

On the three open intervals (0,1), (1,2), (2,3), respectively,
the components satisfy u'=H_{δ,η}v and v'=−H_{δ,η}u
for the actual full Hamiltonian at the stated strengths.
The norm and zero-leakage identities include all switching times
and endpoints; differentiability across a control jump is not
required. The constant extension outside the protocol is not
asserted to solve a physical evolution equation there.

| Lean theorem | Meaning |
| --- | --- |
| `coordinatedProtocolAngle_eq`, `coordinatedProtocolPhase_norm` | Exact accumulated scalar phase and its unit modulus |
| `coordinatedProtocolMatrix_rotation` | Exact physical three-pulse matrix equals the phase-weighted Euler product |
| `coordinatedProtocol_final_rotation` | Physical endpoint for arbitrary initial coefficient pairs |
| `coordinatedProtocol_final_dark` | Explicit endpoint coefficients starting from dark |
| `coordinatedProtocol_reaches_from_dark` | Existence of parameters reaching every normalized complex target up to the stated phase |
| `coordinatedState_dark_initial`, `coordinatedProtocol_dark_weight` | Exact dark initial state and unit squared complex norm |
| `coordinatedProtocol_exact_preparation` | Combined endpoint, continuity, domain, norm, zero leakage and full piecewise Schrödinger equations |

**Status and limits.** The ten public theorems, one private
supporting lemma and one definition are Lean-verified. L7a–L7c.4
complete the exact dark-to-arbitrary-target preparation objective.
The state is represented by real and imaginary vectors of the full
infinite graph. A separate construction of a general complex
Hilbert-space unitary propagator for arbitrary initial data is
still open. The theorem starts from dark; arbitrary initial-to-target
control as a separately formalized result, exact phase-sensitive
preparation without quotienting by global phase, constraints on
physical edge strengths, experimental feasibility, and minimal
control resources are not claimed. The two independently tunable
controls are those defined in §§4.99–4.100; this is not the original
single-edge L6 preparation theorem. L7 has passed independent comparison and was registered separately on 25 November 2026 as [PALOMAR-2026-11-25-000001 (version 1)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-25-000001&version=1). The earlier registrations
and all Track A objectives remain unchanged.

**Independent preparation package.** The [Mathlib-only Challenge](../palomar/exact-leakage-free-preparation/Challenge.lean)
contains 687 lines, five model witnesses, three local-edge certificates
and the single scientific preparation theorem. All definitions are concrete.
The [Solution](../palomar/exact-leakage-free-preparation/Solution.lean) imports the verified source, and the
[Comparator](../palomar/exact-leakage-free-preparation/comparator.json) is kept
in the third registered package directory. Full Lean verification and independent
statement comparison with NanoDa and con-ron have passed. Palomar's mechanical and renderability checks passed, and its automated editorial review identified no blocking problem.


### 4.106. Sharp coordinated-control norms and exact bounded perturbation

**Plain-English result (L8a.1).** Changing all eight matched inter-ring
edges by the same amount changes the infinite Hamiltonian by a bounded
operator of exact norm two per unit edge strength. The eight edges have
disjoint endpoints, so their effects do not accumulate in the operator
norm as eight independent worst-case contributions. The first-ring onsite
control has exact norm one per unit detuning. These estimates concern
every square-summable state on the complete infinite graph, including
states outside the compact two-mode plane.

Let $H_0$ be the crossing Hamiltonian of §4.79 on the natural onsite
domain $D(V)$, $R$ the coordinate projection onto the eight first-ring
vertices, and $M$ the sum of the eight genuine matched-edge Laplacians
of §4.99. For arbitrary signed real detuning $\delta$ and edge strength
$\eta$, the existing ideal coordinated Hamiltonian is denoted by
$H(\delta,\eta)$.

**Matching geometry and exact norms.** Each matched pair of vertices
has a two-coordinate Laplacian with diagonal entries 1 and off-diagonal
entries −1. At every vertex outside the matched pairs, $Mx$ vanishes.
The two endpoint amplitudes of $Mx$ on each pair are opposite.
Applying $M$ a second time therefore doubles its output:

```math
M^2x=2Mx,\qquad x\in\ell^2(\mathrm{Vertex};\mathbb R).
```

Together with the previously proved full-space symmetry of $M$,
this gives

```math
\|Mx\|^2=2\langle x,Mx\rangle
\le 2\|x\|\|Mx\|.
```

The zero-output case is included, and the inequality yields
$\|M\|\le 2$. Equality follows from the normalized nonzero bright
vector $F$, which satisfies $MF=2F$ (§4.100). Likewise $R$ is a
coordinate contraction, and the nonzero compact mode A satisfies
$R\,\mathrm{compactA}=\mathrm{compactA}$. Hence the actual operator
norms are

```math
\|R\|=1,\qquad \|M\|=2.
```

The constants are exact; no finite-volume truncation or two-mode
compression is used.

**Exact bounded control decomposition.** On the unchanged natural
domain, the full Hamiltonian satisfies

```math
H(\delta,\eta)x=H_0x+B(\delta,\eta)x,\qquad
B(\delta,\eta)=\delta R+\eta M,\qquad x\in D(V).
```

The bounded perturbation is defined on the entire Hilbert space and
has the uniform bound

```math
\|B(\delta,\eta)\|\le \rho(\delta,\eta)
:=|\delta|+2|\eta|.
```

No smallness, sign or pulse-duration assumption is needed for these
identities and estimates. The norm bound for the combined perturbation
is an upper bound, not an asserted exact formula for its norm.

**Lean declarations.** The existing
[AmmannBeenkerCoordinatedInvariantPlane.lean](../SpectralGeometry/AmmannBeenkerCoordinatedInvariantPlane.lean)
now contains the following definition and seven theorems:

- `coordinatedRingControl_sq_apply`: exact quadratic identity for every full-space vector.
- `coordinatedRingControl_norm_le_two` and `coordinatedRingControl_opNorm`:
  the upper bound and its attainment.
- `coordinatedOnsiteProjection_opNorm`: exact norm of the first-ring projection.
- `coordinatedControlPerturbation`: bounded map $\delta R+\eta M$.
- `coordinatedControlCorrection_decomposition`: exact decomposition of the bounded interaction.
- `coordinatedControlHamiltonian_decomposition`: exact full natural-domain Hamiltonian equation.
- `coordinatedControlPerturbation_norm_le`: combined perturbation norm bound.

**Verification and scope.** Full Lean/Mathlib verification and the
existing independent L7 Comparator checks passed. The new statements
are Lean-verified but are not independently selected Palomar
statements. They establish L8a.1, not the complete L8a cluster
isolation theorem. Exact geometric invariance and the L7 preparation
theorem remain valid at arbitrary ideal control strengths.
The controlled eigenvalues and reducing complement are now verified in
§4.107 (L8a.2), and exterior spectral exclusion is verified in §4.108
(L8a.3). Consolidated cluster isolation is verified in §4.109 (L8a.4). No protection against nonuniform errors or experimental claim is asserted.
The fourth registration selects the centered protection theorem and its supporting statements (§4.110).

### 4.107. Exact controlled plane energies and natural-domain reduction

**Plain-English result (L8a.2).** Both energies of the ideal controlled
two-state plane are known exactly, even when the controls are not small.
The full infinite operator respects both the original localized plane
and its orthogonal complement on its natural domain. Invariance alone
does not exclude coincidence between an exterior energy and a plane
energy. The quantitative exclusion and isolation results of §§4.108–4.110
supply this additional protection under explicit control bounds.

**Exact eigenvalue characterization.** In the compact A/B coordinates,
the Hamiltonian action of §4.100 is given by the matrix

```math
\begin{pmatrix}
E_*+\delta+\eta&-\eta\\
-\eta&E_*+\eta
\end{pmatrix}
=cI+\begin{pmatrix}\delta/2&-\eta\\-\eta&-\delta/2\end{pmatrix},
\quad c=E_*+\delta/2+\eta.
```

Write $s=\sqrt{(\delta/2)^2+\eta^2}$. For any real energy $e$,
Lean establishes the equivalence

```math
\begin{aligned}
&\exists x\in D(V),\quad x\ne0,\quad Qx=0,\quad H(\delta,\eta)x=ex\\
&\qquad\Longleftrightarrow\quad e=c-s\ \lor\ e=c+s .
\end{aligned}
```

Here $Q$ is the original orthogonal leakage projection, not a newly
chosen spectral projector. Both directions are proved, so the roots
are actual full-domain eigenvalues with nonzero compact eigenvectors,
not merely necessary roots of a characteristic polynomial.

The proof uses the two scalar eigenvector equations for the traceless
matrix with entries $a=\delta/2$, $b=-\eta$, and $z=e-c$.
A nonzero coefficient pair implies $z^2=a^2+b^2$. Conversely, if
$b\ne0$, the pair $(b,z-a)$ is a nonzero solution. If $b=0$, the
equation factors into $z=a$ or $z=-a$ and a coordinate vector supplies
the solution. The compact coefficient extraction identities certify
nonvanishing in the actual Hilbert space. The nonnegative radius $s$
is zero exactly when $\delta=\eta=0$; the baseline multiplicity-two
theorem of §4.78 remains unchanged.

**Natural-domain reduction.** For any $x\in D(V)$, the explicit domain
lifts $p_x$ and $q_x=x-p_x$ have Hilbert-space values $Px$ and $Qx$,
where $P$ is the original two-mode orthogonal projection and $Q=I-P$.
The compact coefficients define $p_x$ using the natural-domain modes A
and B. Full Hamiltonian symmetry and the compact action imply

```math
P H(\delta,\eta)x=H(\delta,\eta)p_x,\qquad
Q H(\delta,\eta)x=H(\delta,\eta)q_x.
```

In particular, if the input is orthogonal to both compact modes, so is
its full Hamiltonian image. These domain-sensitive identities hold
for all real control strengths; neither an assumed spectral gap nor
a finite truncation is used.

**Lean declarations.** The existing
[AmmannBeenkerCoordinatedAxisDynamics.lean](../SpectralGeometry/AmmannBeenkerCoordinatedAxisDynamics.lean)
now contains four definitions, nine public theorems and one private
scalar algebra lemma:

- `coordinatedLevelCenter`, `coordinatedLevelRadius`:
  midpoint and half-spacing;
- `coordinatedLevelRadius_sq`, `coordinatedLevelRadius_eq_zero_iff`:
  squared radius and its degeneracy criterion;
- `coordinatedCompact_eigen_iff`, `coordinatedPlane_eigenvalue_iff`:
  scalar eigen-equations and the exact two-way full-domain characterization;
- `coordinatedPlaneDomainPart`, `coordinatedComplementDomainPart`,
  and their `_coe` theorems: natural-domain projection lifts;
- `coordinatedHamiltonian_plane_commutes`,
  `coordinatedHamiltonian_complement_commutes`,
  `coordinatedHamiltonian_complement_invariant`: the reducing identities.

**Verification and scope.** Full Lean/Mathlib and the existing independent
L7 Comparator passed. L8a.2 is Lean-verified, not a new independently
selected Palomar result. The equivalence concerns eigenvectors in the
compact plane only; it does not assert global simplicity or isolation
for nonzero controls. L8a.3 now quantitatively excludes exterior
energies in §4.108; L8a.4 consolidates cluster isolation in §4.109,
including degeneracy at zero controls. L6, Track A and the earlier registrations
retain their scope.

### 4.108. Quantitative exclusion of exterior real spectral levels

**Plain-English result (L8a.3).** The original certified energy gap can
be used to exclude all exterior eigenvectors from an explicit open
window while the ideal controls are active. The window shrinks with
the size of the applied bounded perturbation. Inside it, the complete
real spectrum has no levels other than the two explicit compact-plane
energies, and every eigenvector there has exactly zero leakage.

Let $g=1/128$ be the previously certified baseline gap radius,
$\rho=|\delta|+2|\eta|$ the control budget, and $H=H(\delta,\eta)$.
On the unchanged natural domain, for any $x$ orthogonal to both
compact modes and every real $e$, Lean proves

```math
(g-\rho-|e-E_*|)\|x\|\le\|Hx-ex\|.
```

Indeed, the baseline reduced-gap residual estimate gives
$g\|x\|\le\|(H_0-E_*)x\|$ for such $x$. The exact decomposition
from §4.106 gives
$(H_0-E_*)x=(H-e)x+(e-E_*)x-Bx$.
The triangle inequality and $\|Bx\|\le\rho\|x\|$ yield the stated
bound, even when its left-hand coefficient is nonpositive.

**Exterior exclusion.** Every nonzero natural-domain exterior
eigenvector at energy $e$ satisfies

```math
g\le\rho+|e-E_*|.
```

The same conclusion holds for any full eigenvector with a nonzero
leakage component, because its natural-domain $Q$-projection is a
nonzero eigenvector at the same energy by §4.107. Thus in the open
window $\rho+|e-E_*|<g$, every full eigenvector lies in the original
compact plane. The strict inequality is essential to this argument.

**Complete real spectrum, not just point spectrum.** For all real
control strengths and every real energy, Lean now proves that
membership in the full real bounded-inverse spectrum of the controlled
operator is equivalent to existence of a genuine nonzero full-domain
eigenvector. Properness and the lower bound of the concrete onsite
potential provide the compact shift; the existing full real resolvent
characterization applies with zero additional matching edges and
the entire coordinated bounded correction. There is no finite-volume
or extra spectral assumption. Combining this equivalence with §4.107
and exterior exclusion gives

```math
\rho+|e-E_*|<g\ \Longrightarrow\
\bigl(e\in\sigma_{\mathbb R}(H)\ \Longleftrightarrow\
e=\lambda_-\ \lor\ e=\lambda_+\bigr).
```

This is a conditional characterization at each energy in the
explicit open window. The inclusion of both controlled levels in
the window throughout a sufficient control range, and the uniform
positive separation from every exterior energy, are now consolidated
in §4.109 (L8a.4).

**Lean declarations.** The seven public theorems in
[AmmannBeenkerCoordinatedAxisDynamics.lean](../SpectralGeometry/AmmannBeenkerCoordinatedAxisDynamics.lean)
are:

- `coordinatedControlPerturbation_apply_norm_le`: full-space vector norm bound;
- `coordinatedComplement_residual_lower`: exterior residual lower bound;
- `coordinatedComplement_eigenvalue_distance`: exterior eigenvalue exclusion;
- `coordinatedEigenvector_complement_distance`: exclusion for any eigenvector with nonzero leakage;
- `coordinatedRealSpectrum_iff_full_eigenvector`: complete controlled real-spectrum characterization;
- `coordinatedEigenvector_leakage_zero_of_near`: all eigenvectors in the window have zero leakage;
- `coordinatedRealSpectrum_near_iff`: exact real-spectrum characterization in the open window.

**Verification and scope.** Full Lean/Mathlib verification and the
existing independent L7 Comparator passed. L8a.3 is Lean-verified,
not a new independently selected Palomar result. No spectral gap for
arbitrary strengths or robustness to imperfect controls is asserted.
The baseline gap and all earlier results retain their original scope.

### 4.109. Consolidated quantitative isolation of the controlled cluster

**Plain-English result (L8a.4).** The two controlled localized energies
are now guaranteed to stay away from every other real spectral energy
of the infinite graph if the combined control strength is sufficiently
small. The theorem gives both an explicit admissible control range and
a positive lower bound on the separation. No other eigenvector can
have a component outside the original localized plane at either
controlled energy.

Write $\rho=|\delta|+2|\eta|$ and $g=1/128$. The exact levels are
$\lambda_\pm$ of §4.107. The consolidated theorem assumes only

```math
\rho<1/256.
```

It establishes all of the following for the actual controlled
natural-domain infinite operator:

- Each plane level belongs to the complete real bounded-inverse
  spectrum and is at distance at most $\rho$ from $E_*$.
  Every full-domain eigenvector at either level has zero leakage.
- The spectrum in the **closed** radius-$\rho$ window about $E_*$
  consists exactly of the plane levels.
- For either plane level $\lambda$ and any other real spectral energy
  $e$, the explicit separation satisfies

```math
|e-\lambda|\ge 1/128-2\rho>0.
```

- The same separation holds for the energy of every full-domain
  eigenvector with nonzero leakage, even without assuming that its
  energy differs from the two plane levels.

At zero controls the set of plane energies is a singleton; its
multiplicity is exactly two by §4.78. At nonzero controls the two
energies are distinct by §4.107. No general complex-spectrum theorem
or arbitrary-strength energetic isolation is asserted.

**Proof.** For a nonzero compact-plane eigenvector $x$ at energy
$\lambda$, the original Hamiltonian satisfies $H_0x=E_*x$.
The exact bounded decomposition gives
$Bx=(\lambda-E_*)x$, so the operator bound in §4.106 implies
$|\lambda-E_*|\le\rho$. Consequently
$\rho+|\lambda-E_*|\le2\rho<g$.
The open-window characterization of §4.108 proves that both levels
are protected and that the closed radius-$\rho$ window contains
no other real spectral energies. For any eigenvector with nonzero
leakage, §4.108 gives $g\le\rho+|e-E_*|$. The triangle inequality
and the plane displacement bound give $g\le2\rho+|e-\lambda|$.
The full real-spectrum characterization likewise excludes any
other spectral point closer than $g-2\rho$ to a plane level.
The exterior residual at either plane energy is also at least
$(g-2\rho)\|x\|$ for every exterior domain vector.

**Lean declarations.** In the existing
[AmmannBeenkerCoordinatedAxisDynamics.lean](../SpectralGeometry/AmmannBeenkerCoordinatedAxisDynamics.lean):

- `CoordinatedPlaneLevel`: membership in the exact two-level set;
- `coordinatedPlaneLevel_shift_le`: displacement bound for both levels;
- `coordinatedPlaneLevel_mem_realSpectrum`: full real spectral membership;
- `coordinatedPlaneLevel_complement_residual_lower`: exterior residual at a plane level;
- `coordinatedPlaneLevel_exterior_distance`: separation for eigenvectors with leakage;
- `coordinatedPlaneLevel_otherRealSpectrum_distance`: separation from all other real spectral points;
- `coordinatedPlaneLevel_in_protected_window`: both levels in the exclusion window;
- `coordinatedCluster_isolation`: consolidated numerical theorem.

**Verification and scope.** Full Lean/Mathlib and the existing
independent L7 Comparator passed. The central L8a static spectral
protection objective is complete. This conservative theorem is
Lean-verified; the stronger centered estimate of §4.110 is the separately
selected scientific conclusion of the independently compared
spectral-protection candidate. The sufficient range here is conservative.
Further refinements remain a research opportunity. The ideal-control static gap is not a bound on
leakage under imperfect time-dependent controls. All previous results,
including the distinct L6 and Track A objectives, retain their scope.

### 4.110. Spectral protection during coordinated control

**Plain-English result.** Centering the energy scale at the exact
midpoint of the two controlled levels yields a stronger verified
guarantee of energetic isolation. The new sufficient control region
contains the entire open diamond $\rho<1/128$, which doubles the
previous guaranteed pure-axis ranges. The conservative theorem of
§4.109 is retained unchanged.

Let $R$ be the first-ring onsite projection, $M$ the coordinated
matching operator, $B=\delta R+\eta M$, $g=1/128$,
$\rho=|\delta|+2|\eta|$, $c=E_*+\delta/2+\eta$, and
$s=\sqrt{(\delta/2)^2+\eta^2}$. The exact plane energies are $c\pm s$.

**Full-space centered bound.** For every vector of the real Hilbert
space, Lean proves the exact norm identities

```math
\|(R-\tfrac12 I)x\|=\tfrac12\|x\|,\qquad
\|(M-I)x\|=\|x\|.
```

The first follows from the projection inner-product identity; the
second follows from symmetry and $M^2=2M$. Expanding squared norms
and using nonnegativity gives the stated identities, including
zero vectors. The triangle inequality then gives

```math
\|Bx-(\delta/2+\eta)x\|\le(\rho/2)\|x\|.
```

Consequently, for every natural-domain vector orthogonal to both
compact modes, the baseline residual estimate implies

```math
(g-\rho/2-|e-c|)\|x\|\le\|H(\delta,\eta)x-ex\|.
```

The reducing complement and complete real-spectrum characterization
of §§4.107–4.108 transfer this to full spectral exclusion:
every eigenvector with nonzero leakage satisfies
$g\le\rho/2+|e-c|$, and inside the open window
$\rho/2+|e-c|<g$ the complete real spectrum is exactly characterized
by membership in the two-level set.

**Consolidated strengthened theorem.** If

```math
\rho/2+s<1/128,
```

then both plane energies belong to the complete real spectrum, every
eigenvector at either has zero leakage, the spectrum in the closed
interval $[c-s,c+s]$ consists exactly of those energies, and every
other real spectral point $e$ satisfies, for each plane level $\lambda$,

```math
|e-\lambda|\ge 1/128-\rho/2-s>0.
```

The same separation holds for the energy of every eigenvector with
nonzero leakage. The proof includes zero controls without artificially
requiring two distinct energies. The scalar radius bound $s\le\rho/2$
gives the simpler sufficient condition $\rho<1/128$ and the lower
bound $1/128-\rho$. On the pure onsite axis this means
$|\delta|<1/128$; on the pure edge axis $|\eta|<1/256$.
These are sufficient ranges, not maximal thresholds.

**Lean declarations.** The eleven public theorems in
[AmmannBeenkerCoordinatedAxisDynamics.lean](../SpectralGeometry/AmmannBeenkerCoordinatedAxisDynamics.lean)
are:

- `coordinatedOnsite_centered_norm` and `coordinatedRing_centered_norm`: exact centered norms;
- `coordinatedControl_centered_apply_norm_le`: centered perturbation bound;
- `coordinatedLevelRadius_le_half_budget` and `coordinatedPlaneLevel_center_distance`: scalar radius and plane displacement;
- `coordinatedComplement_centered_residual_lower`: centered exterior residual;
- `coordinatedEigenvector_centered_complement_distance` and `coordinatedRealSpectrum_centered_near_iff`: centered exterior and full spectral exclusion;
- `coordinatedCluster_centered_isolation`: consolidated strengthened theorem;
- `coordinatedCluster_centered_condition_of_budget` and `coordinatedCluster_centered_gap_ge`: simpler sufficient condition and gap comparison.

Full Lean/Mathlib verification and the previous registered preparation
Comparator passed for the strengthened substantive proof. The new
[Mathlib-only Challenge](../palomar/spectral-protection-during-coordinated-control/Challenge.lean),
[Solution](../palomar/spectral-protection-during-coordinated-control/Solution.lean),
[Comparator](../palomar/spectral-protection-during-coordinated-control/comparator.json)
and [metadata](../palomar/spectral-protection-during-coordinated-control/formalization.yaml)
have passed full Lean verification and independent comparison of all
15 selected propositions, including NanoDa and con-ron. The result
was registered on 26 November 2026 as [PALOMAR-2026-11-26-000015 (version 1)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000015&version=1). No
independent human review is asserted. The theorem concerns
static protection for ideal controls on the specified infinite graph;
imperfect controls remain a distinct research question. The later exact
variable-duration result is established in §4.111.

### 4.111. Exact protected state preparation with arbitrarily weak controls

The previous results establish exact preparation using three unit-duration
pulses (§4.105) and centered spectral isolation for sufficiently weak ideal
controls (§4.110). Neither alone guarantees that the target can be reached
with an arbitrarily small control budget while retaining a prescribed gap.
The following theorem supplies that guarantee.

Let a,b be normalized complex dark/bright amplitudes, let `ε > 0`,
and let `0 < f < 1`. Put `g = 1/128`. The constructive Euler angles
`p,t,q` have `0 ≤ t ≤ π/2`. Define the maximum unit-duration control budget
`B = max(2|p|, 2|t|, 2|q|)`, the positive allowance
`m = min(ε, (1−f)g)`, and the common duration `k = 1 + B/m`.
Then `k ≥ 1`, and `B/k ≤ m`, including the case B = 0.

Use three successive settings `(δ,η) = (0,p/k), (−2t/k,0), (0,q/k)`,
each for duration k. Scaling strengths inversely with duration retains
the Euler rotation, with the exact common phase
`exp(i(−3kE* + t − p − q))`. The trajectory starts from dark
and ends at the desired normalized pair up to that phase at time 3k.
The clamped pulse clocks give continuity at both switches. The embedded
real and imaginary graph vectors remain on the natural domain, with
total squared norm one and exactly zero leakage for all real times.
The coupled full-graph Schrödinger equations hold on the three open
pulse intervals; no derivative at a switch is claimed.

In each setting `ρ = |δ| + 2|η| ≤ m ≤ ε` and `ρ ≤ (1−f)g < g`.
By §4.110 the two controlled levels exhaust the real spectrum in their
closed interval, every eigenvector there is in the localized plane,
and their distance from every other real spectral energy (and from
energies of eigenvectors with nonzero leakage) is at least
`g−ρ ≥ fg = f/128`. This includes coincident levels at zero control.
The separation is a sufficient bound for each active Hamiltonian, not
a dynamical noise estimate.

**Lean statements.** The variable-duration trajectory is developed in
[AmmannBeenkerCoordinatedVariableDuration.lean](../SpectralGeometry/AmmannBeenkerCoordinatedVariableDuration.lean).
The main result in
[AmmannBeenkerCoordinatedProtectedPreparation.lean](../SpectralGeometry/AmmannBeenkerCoordinatedProtectedPreparation.lean)
is `coordinatedProtocol_protected_exact_preparation`, supported by
`coordinatedDurationAngle_scaled`, `coordinatedProtocolStretch_bounds`
and `coordinatedProtectedSetting_of_budget`.

The substantive proof passed full Lean/Mathlib kernel verification.
Independent comparison for this fifth candidate and registry verification
are separate steps. The four preceding registrations are preserved.
The result does not assert a general complex propagator, optimal durations,
preparation at zero control strength for arbitrary targets, retention of
the entire certified gap, or resilience to imperfect controls.
