[← Main README and table of contents](../README.md)

<details>
<summary>Contents of this document</summary>

- [1.1. The research question](#11-the-research-question)
- [1.2. First substantive milestone: finite-coordinate observation](#12-first-substantive-milestone-finite-coordinate-observation)
- [1.3. The operator and its geometric inputs](#13-the-operator-and-its-geometric-inputs)
- [1.4. Confinement, observation and local changes](#14-confinement-observation-and-local-changes)

</details>

## 1. Research program and geometric model

### 1.1. The research question

How can a local change in an infinite geometric system be detected in an
analytic function whose zeros record its spectrum? Which finite sets of sites
observe low-energy modes, how do perturbations on those sites move the
corresponding levels, and with what error can finite patches certify that
response?

The program studies these questions for an operator with a confining onsite
potential, bounded local interactions and controlled perturbations. It then
transports the spectral information to a normalized canonical product on a
fixed complex line. The concrete application uses the centered octagonal
cut-and-project vertex graph (§§4.68–4.79). The spectral proofs use its
verified vertex and edge geometry. Polygonal tiling coverage and aperiodicity
remain open (§6.4).

The concrete Ammann–Beenker results may interest researchers in
spectral theory, localization on quasiperiodic networks, wave control and
formal verification. The [scientific audience and possible relevance](scientific-audience.md#scientific-audience-and-possible-relevance)
section explains what each community might find useful and which
conclusions are not yet established. The broader analytic-product part
of the program may also interest specialists in entire functions
associated with operator spectra.

### 1.2. First substantive milestone: finite-coordinate observation

Let
```math
H=M_V+B,\qquad
D(V)=\{\psi\in\ell^2(T):V\psi\in\ell^2(T)\},
\qquad
F_R=\{t\in T:V(t)\le R\}.
```

Here the real Hilbert space of sites may be infinite, the potential may be
unbounded, and the full correction $B$ is bounded. Under the precise
properness and resolvent hypotheses in §4.40, the proved theorem gives
```math
\lambda<R-\|B\|,\qquad \lambda\ne a
\quad\Longrightarrow\quad
\dim E_\lambda(H)\le \#F_R.
```

Its central construction is an injective linear restriction map
```math
E_\lambda(H)\longrightarrow\mathbb R^{F_R},
\qquad \psi\longmapsto\psi|_{F_R}.
```

Thus two vectors in the same fixed-eigenvalue eigenspace that agree on $F_R$
agree everywhere. The result observes the entire eigenspace, not merely one
chosen eigenvector. It concerns geometric multiplicity and does not require
the bounded correction to be symmetric.

The foundational Lean declaration is
[SpectralGeometry.infiniteLocalMatching_full_eigenspace_finrank_le_lowEnergyTiles](../SpectralGeometry/InfiniteLocalFullLowEnergyCounting.lean).
It assumes finite onsite sublevel sets, a real shift $a$ with
$V(t)-a\ge1$, the onsite resolvent $R_a^{\mathrm{on}}=(M_V-aI)^{-1}$,
the bound $\|B R_a^{\mathrm{on}}\|<1$, and the displayed restrictions on
$\lambda$. Its eigenspace is represented through the equivalent eigenspace
of the full compact shifted inverse; the source development connects that
representation to natural-domain eigenvectors.

The proof uses a quadratic-form obstruction: a vector vanishing on all sites
with $V(t)<R$ has energy at least $(R-\|B\|)\|\psi\|^2$. This is
incompatible with a nonzero eigenvector below that threshold. Applied to the
kernel of restriction, the obstruction gives injectivity and the dimension
bound.

**Role in the research program.** The theorem identifies a finite observation
sector for each sufficiently low eigenspace. Under the additional symmetry
and lower-bound assumptions, §§4.41–4.43 now prove quantitative observation of
the whole low-energy spectral subspace and a total count with multiplicities.
The variational bridge of §§4.44–4.46 turns that form inequality into
$\kappa\tau\le\lambda_n(H+\tau P_{F_R})-\lambda_n(H)\le\tau$
for the levels and parameter interval specified in §6.2, including repeated
levels. Section 4.48 transfers onsite summability to the positive full spectrum
and preserves it along this intervention. Section 4.49 now turns the exact
full spectral enumeration into an entire product whose zeros have precisely
the geometric eigenspace multiplicities. Sections 4.50–4.52 now transfer this response to the actual indexed zeros of
the two entire full spectral products, with fixed affine data and the correct
operator-specific geometric orders. Sections 4.53–4.56 now certify the total
zero multiplicity in a separated window under a small symmetric bounded
operator error. They derive all-index error bounds and use finite neighboring
level checks at the window boundaries. Sections 4.57–4.59 construct the onsite
ordering from properness and prove a stronger positive-interaction family:
the gap remains $v_0>0$, and the response coefficient becomes
$(R-E)/(R-v_0)$, with no interaction-norm penalty. Sections 4.60–4.62 add a
different kind of certificate: scalar approximation near a zero of order
$m$ preserves at least one nearby zero and bounds every zero in the certified
disk at the scale $\varepsilon^{1/m}$. The full product's geometric
multiplicities supply $m$, and inverse-square tails supply explicit product
truncation errors. Sections 4.63–4.65 now prove the disk argument principle
and Rouché's theorem, upgrading the local certificate to exactly $m$ zeros
counted with multiplicity under $\varepsilon<C\rho^m$. The approximant may
split a multiple zero. The conserved count is the original operator's
geometric multiplicity. Sections 4.66–4.67 now turn this into a numerical
worked certificate for onsite multiplication by $n+1$: radius $1/4$,
cofactor lower bound $1/5$, and a sufficient finite-product cutoff $16384$,
including a nonzero additional approximation-error budget. The same
quantitative tail estimates apply to its full spectrum with a symmetric
nonnegative bounded interaction, while the explicit cofactor and radius
are proved for the onsite model. Sections 4.68–4.70 now construct the
octagonal cut-and-project vertex graph and prove a concrete response for
its first nine ordered levels. Sections 4.71–4.72 use the geometric counting
and summability estimates to prove how the corresponding product zeros move.
For $0\le\tau\le4$, every level of $H$ and $H_\tau$ is at least one.
In either product, the order of a zero equals the geometric multiplicity of
the corresponding eigenvalue for that product's operator.

The concrete full-product response of §4.72 uses these source results under
its verified geometric hypotheses. They do not provide a numerical reconstruction
algorithm or independent control of several zeros. The relative
determinant identity in §6.5 is a separate proof obligation; it does not follow
from this theorem alone.

This is the first substantive observation milestone of the program, supported by
the operator-theoretic results catalogued in §§3–4. Its position in the program
does not assert mathematical priority, a new proof technique or an independent
research-interest assessment. The proof mechanism is a standard
quadratic-form and restriction argument. The first registered Palomar
result is documented in §4.78; the new proposal and its provenance are
described in §§4.92 and 6.8 and in [formalization.yaml](../formalization.yaml).

### 1.3. The operator and its geometric inputs

The proposed geometric family is
```math
H_\varepsilon=M_V+L_w+\varepsilon P,
```
with action, whenever the geometric interaction is defined,
```math
(H_\varepsilon\psi)(t)
=V(t)\psi(t)
+\sum_{u\ne t}w(t,u)\bigl(\psi(t)-\psi(u)\bigr)
+\varepsilon(P\psi)(t).
```

The potential $V(t)$ assigns an onsite energy. The weights describe
interactions between sites, and $P$ is a bounded controlled perturbation.
For symmetric nonnegative weights, the interaction is a graph Laplacian.
The amplitude $\psi(t)$ belongs to a state of the entire system; it is not
a prescribed eigenfunction or an intrinsic energy of an individual tile.

The Lean type named Tile is an abstract site type. In a concrete application
its elements may be tiles or vertices of a tiling; that choice must be stated.
The Ammann–Beenker application in §6.4 uses vertices. Geometric rules determine
the potential and the couplings before the spectrum is studied.

For a finite patch the construction has matrix form
```math
H_\varepsilon
=\operatorname{diag}\!\left(V_i+\sum_jw_{ij}\right)-W+\varepsilon P.
```
For infinitely many sites it acts on the natural multiplication domain
$D(V)$, with bounded corrections added on that same domain.

The formalized infinite local interaction uses finitely many matching colors:
each involutive permutation $\sigma_i$ pairs a site with at most one neighbor
of color $i$, with a constant weight for that color. Under
$0\le w_i\le W$,
```math
L_w=\sum_{i=1}^{D}w_i(I-U_{\sigma_i}),
\qquad \|L_w\|\le2DW.
```
A named tiling must be represented by such matchings, or the framework must
first be extended with a proved alternative. The existing modules do not
already establish a representation theorem for every bounded-degree graph.

### 1.4. Confinement, observation and local changes

Finite onsite sublevel sets are a genuine growth assumption. On a
finite-local-complexity tiling, a potential determined only by a finite set of
local tile types takes finitely many values and cannot by itself supply that
assumption on infinitely many sites. On the octagonal graph, the chosen
potential is $V(v)=1+|p(v)|^2$, where $p(v)$ is the physical position.
Each bounded disk contains finitely many vertices, so the onsite sublevels
are finite (§§4.68, 4.70).

Raising the onsite energies by $\tau$ on $F_R$ gives the operator
```math
H_\tau=H+\tau P_{F_R},\qquad \tau\ge0.
```
On the octagonal graph, $F_5=\{v:|p(v)|\le2\}$ is the radius-two sector.
For this intervention, §4.72 compares the zeros of the full spectral products
of $H$ and $H_\tau$ using a common center, direction and normalization.
Perturbing just the eight neighbors of the origin produces the crossing of
§4.78, with the conservative real spectral isolation proved in §4.79.
Changing the weight of the edge specified in §4.75 leaves the sum of
the two compact modes at the crossing energy.

For a more general local change, the relative-product program in §6.5
requires a proof that the operator difference has the form $\iota_S K\iota_S^*$
on a finite set $S$. A change of site sets also requires identifying the two
Hilbert spaces.

