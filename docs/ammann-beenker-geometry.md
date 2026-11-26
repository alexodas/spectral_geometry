[← Main README and table of contents](../README.md)

# 4. Infinite-dimensional geometric operators and spectral theory — §§4.68–4.79

**Chapter 4 navigation:** [4.1–4.67. Infinite-dimensional spectral theory](infinite-spectral-theory.md) · **4.68–4.79. Ammann–Beenker geometry and the compact crossing** · [4.80–4.98. Single-edge control and spectral splitting](single-edge-control.md) · [4.99–4.110. Coordinated quantum control and spectral protection](coordinated-quantum-control.md)

<details>
<summary>Contents of this document</summary>

- [4.69. Exact neighbors, parity matchings and the concrete Laplacian](#469-exact-neighbors-parity-matchings-and-the-concrete-laplacian)
- [4.70. A nonempty nine-level spectral response on the vertex graph](#470-a-nonempty-nine-level-spectral-response-on-the-vertex-graph)
- [4.71. Planar vertex counting and geometric inverse-square summability](#471-planar-vertex-counting-and-geometric-inverse-square-summability)
- [4.72. Exact geometric full products and nine-level zero response](#472-exact-geometric-full-products-and-nine-level-zero-response)
- [4.73. A radial gap and a stronger nine-level response](#473-a-radial-gap-and-a-stronger-nine-level-response)
- [4.74. Compact eigenvectors on the infinite natural domain](#474-compact-eigenvectors-on-the-infinite-natural-domain)
- [4.75. A ring crossing and a single-edge change](#475-a-ring-crossing-and-a-single-edge-change)
- [4.76. The exact central sector and its boundary](#476-the-exact-central-sector-and-its-boundary)
- [4.77. The central crossing kernel and centrally supported eigenvectors](#477-the-central-crossing-kernel-and-centrally-supported-eigenvectors)
- [4.78. Central support and exact multiplicity of the infinite crossing](#478-central-support-and-exact-multiplicity-of-the-infinite-crossing)
- [4.79. A conservative quantitative real spectral gap at the crossing](#479-a-conservative-quantitative-real-spectral-gap-at-the-crossing)

</details>

### 4.68. An explicit octagonal cut-and-project vertex set

[AmmannBeenkerCutProject.lean](../SpectralGeometry/AmmannBeenkerCutProject.lean)
defines lifts $n=(n_0,n_1,n_2,n_3)\in\mathbb Z^4$, with $\alpha=\sqrt2/2$,
and the two conjugate projections
```math
p(n)=(n_0+\alpha(n_1-n_3))+i(n_2+\alpha(n_1+n_3)),
\qquad
p^*(n)=(n_0-\alpha(n_1-n_3))+i(-n_2+\alpha(n_1+n_3)).
```
The accepted lifts satisfy the **open** centered octagonal window
```math
|u|,|v|<\tfrac12+\alpha,\qquad |u+v|,|u-v|<1+\alpha,
\qquad u+iv=p^*(n).
```
This fixes the boundary convention explicitly. These are the standard
conjugate eighth-root coordinates and unit-side octagon used for the
Ammann–Beenker vertex construction; see [Beenker's report](https://pure.tue.nl/ws/files/4269555/253166.pdf)
and the projection description in
[Topological densities of quasiperiodic structures](https://doi.org/10.1515/zkri-2025-0003).
The Lean definitions, rather than a picture or an assumed tiling predicate,
specify the set used below.

`physical_injective`, `internal_injective` and `position_injective`
prove uniqueness of the integer lift using irrationality of $\sqrt2$.
The origin and every signed standard basis lift are admitted; their
physical distances from the origin are one. `inflate` is an integer map
whose physical projection scales by $1+\sqrt2$ and whose internal
projection scales by $1-\sqrt2$. `admitted_inflate` and
`inflatedOriginNeighbor_injective` prove that the accepted vertex type is
infinite, rather than assuming infinitude.

`joint_norm_identity` identifies the sum of the squared projection norms
with $2\sum_i n_i^2$. It gives `coordinate_bound`: accepted lifts with
$|p(n)|\le R$, $R\ge0$, satisfy $|n_i|\le R+3$.
`finite_norm_sublevel` then proves finiteness of the actual vertices in
every radius sublevel, including empty sublevels. This proves local
finiteness and will supply properness. It is **not** a two-dimensional
counting rate or a uniform separation estimate. Polygonal coverage,
aperiodicity and global rotational-symmetry theorems are not asserted.

### 4.69. Exact neighbors, parity matchings and the concrete Laplacian

[AmmannBeenkerGraph.lean](../SpectralGeometry/AmmannBeenkerGraph.lean)
defines adjacency independently of the matching operators: two admitted
lifts differ by $\pm e_i$. `adjacent_irrefl`, `adjacent_symm` and
`adjacent_unit_length` prove that these are undirected unit-length edges
without loops. The converse classification of all pairs at Euclidean
distance one is not claimed here.

Direction and parity of the corresponding integer coordinate define eight
colors. Each color exchanges the two endpoints of its admitted edge and
fixes a vertex when the proposed partner is absent.
`latticeMate_involutive` and `mate_involutive` prove the involutions;
`mate_adjacent`, `adjacent_exists_mate` and `mate_color_unique` prove
that their nontrivial edges are exactly the defined edges, each occurring
in one color. `neighbors_card_le` gives degree at most eight, and
`origin_neighbors_card` proves that the center has exactly eight distinct
neighbors, all at unit distance.

With weight $1/16$ for each color, `interaction_apply` proves the exact
coordinate formula
```math
(B\psi)(x)=\frac1{16}\sum_{y\sim x}(\psi(x)-\psi(y)).
```
`interaction_nonneg`, `interaction_symmetric` and `interaction_norm_le`
give nonnegative energy, symmetry and $\|B\|\le1$ on the full real
$\ell^2$ space. This uses the existing infinite matching operator API;
fixed points do not add a diagonal term or a fictitious edge.

### 4.70. A nonempty nine-level spectral response on the vertex graph

[AmmannBeenkerOperator.lean](../SpectralGeometry/AmmannBeenkerOperator.lean)
sets $V(x)=1+|p(x)|^2$, $H=M_V+B$ on its natural domain $D(V)$, and
$S=\{x:|p(x)|\le2\}$. `potential_proper` and `potential_lower` prove
finite onsite sublevels and $V\ge1$; `sector` is proved finite and
`potential_outside_sector` gives $V\ge5$ off $S$.

`centralStar_card` proves that the center and its neighbors give nine
distinct sites. `centralStar_potential_le` bounds their onsite energies by
two. `ninth_onsite_le` places the ninth sorted onsite level below or at
two, by injecting these nine sites into any proposed initial segment.
The established variational comparison and $\|B\|\le1$ then give
$\lambda_8(H)\le3$; no nonempty spectral window is assumed.

The principal theorem `AmmannBeenker.exists_nine_level_response`
constructs complete monotone natural-domain eigenbases for $H$ and every
$H_\tau=H+\tau P_S$, $0\le\tau\le4$, and proves
```math
\lambda_n(H),\lambda_n(H_\tau)\ge1\quad(n\in\mathbb N),\qquad
\lambda_n(H)\le3\quad(0\le n<9),
```
```math
\frac\tau2\le\lambda_n(H_\tau)-\lambda_n(H)\le\tau
\quad(0\le n<9,\ 0\le\tau\le4).
```
Infinitude, properness, the central sites and the interaction bounds are
proved inputs from this explicit graph. The common-domain self-adjoint
and compact-shifted-resolvent existence package is reused, and the shift
may depend on $\tau$. Repeated levels are counted through complete
orthonormal eigenbases; simplicity is not assumed. The proof uses the
positive sector form bound and the verified min–max comparison.

This is the concrete spectral foundation for the stronger full-product
result of §4.72. Section 4.71 derives geometric inverse-square summability;
local finiteness or compact resolvent alone would not supply it. No
optimal sector, finite-patch error or new spectral technique is asserted.

### 4.71. Planar vertex counting and geometric inverse-square summability

[AmmannBeenkerSummability.lean](../SpectralGeometry/AmmannBeenkerSummability.lean)
constructs an injective `planarCode` into
$(\mathbb Z^2)\times\{-2,-1,0,1,2\}^2$. The free coordinates are
$(n_1,n_3)$; the residues subtract the integer floors of
$\alpha(n_1-n_3)$ and $\alpha(n_1+n_3)$ from $n_0$ and $n_2$.
The window bounds each residue. No uniform-separation hypothesis is supplied.

`radius_count_le` proves for every $R\ge0$, with $N=\lceil R+3\rceil$,
```math
\#\{x:|p(x)|\le R\}\le25(2N+1)^2.
```
This is an explicit quadratic upper bound, not an asymptotic density law.
`planar_energy_bound` proves
$1+n_1^2+n_3^2\le5V(x)$. Hence
```math
\frac1{V(x)^2}\le
\frac{25}{(1+n_1^2)(1+n_3^2)}.
```
The product of two convergent integer series, together with the finite
residue code, gives `potential_invSq_summable`:
$\sum_{x\in\mathrm{Vertex}}V(x)^{-2}<\infty$. This is summability of
the actual geometric potential; it assumes neither a sorted enumeration
nor a spectral growth estimate. The bound is not optimized. A separate
uniform-separation estimate is not proved or needed for this argument.

### 4.72. Exact geometric full products and nine-level zero response

[AmmannBeenkerSpectralProducts.lean](../SpectralGeometry/AmmannBeenkerSpectralProducts.lean)
proves `AmmannBeenker.exists_nine_level_fullProducts`.
For arbitrary fixed $c,d\in\mathbb C$ with $d\ne0$, it constructs
complete monotone natural-domain eigenbases for $H$ and $H_\tau=H+\tau P_S$,
with $V(x)=1+|p(x)|^2$, matching edge weight $1/16$ and $S=\{|p(x)|\le2\}$.
All baseline and perturbed levels are at least one; $\lambda_n(H)\le3$
for $n<9$. Both full spectra are inverse-square summable.

`HasExactFullSpectralProduct` is proved for each operator: its canonical
product is entire, its zeros are exactly the reflected full real
bounded-inverse spectrum, and its analytic orders are the geometric
eigenspace multiplicities of that same operator. In particular,
```math
D_\tau(s)=\prod_{n\ge0}\left(1-
\frac{(s-c)^2}{d^2\lambda_n(H_\tau)^2}\right),
\qquad z_n^\pm(\tau)=c\pm d\lambda_n(H_\tau).
```
For $0\le\tau\le4$ and $n<9$, the theorem retains the spectral bounds
$\tau/2\le\lambda_n(H_\tau)-\lambda_n(H)\le\tau$ and proves
```math
z_n^\pm(\tau)-z_n^\pm(0)
 =\pm d\bigl(\lambda_n(H_\tau)-\lambda_n(H)\bigr),
\qquad |d|\frac\tau2\le|z_n^\pm(\tau)-z_n^\pm(0)|\le|d|\tau.
```
The four indexed points are zeros of their own products, and both indexed
branches move for $\tau>0$. Repetitions and crossings are allowed: these
are nine multiplicity slots on each branch, not a claim of nine distinct
locations or disjoint zero sets at different parameters.

Only the affine data $c,d$ and $d\ne0$ are supplied. Infinitude, properness,
self-adjoint natural-domain construction, compact shifted resolvents,
positive gaps, spectral enumeration, geometric summability and the nonempty
window come from verified source results. The common domain and affine data
are unchanged along the interval; a resolvent shift may depend on $\tau$.
Normalization and reflected symmetry follow from the existing canonical
product theorems (§2.4). Uniform vertex separation, polygonal coverage,
aperiodicity, optimal constants, numerical cofactor/radius data, relative
determinants and finite-patch errors are not conclusions. Formal verification
is distinct from originality or research-interest assessment.

### 4.73. A radial gap and a stronger nine-level response

[AmmannBeenkerRadialGap.lean](../SpectralGeometry/AmmannBeenkerRadialGap.lean)
proves that the internal window has squared radius less than two. The
joint norm identity reduces the small-radius classification to 81 integer
cases. Every admitted vertex with $|p|^2<3+2\sqrt2$ has $|p|\le2$.
Thus `potential_outside_sector_sharp` gives $V\ge4+2\sqrt2$ outside the
same radius-two sector $S$ used in §4.72.

`exists_nine_level_response_sharp` reuses the baseline nine-level theorem,
constructs the perturbed eigenbases, and proves
```math
(4\sqrt2-5)\tau\le\lambda_n(H+\tau P_S)-\lambda_n(H)\le\tau,
\qquad n<9,\quad 0\le\tau\le3+2\sqrt2.
```
The coefficient is approximately $0.65685$. This sharpens the spectral
estimate for the same operator, domain and sector. The full-product
statement of §4.72 retains its original constants and interval.

### 4.74. Compact eigenvectors on the infinite natural domain

[AmmannBeenkerCompactModes.lean](../SpectralGeometry/AmmannBeenkerCompactModes.lean)
and [AmmannBeenkerCompactStates.lean](../SpectralGeometry/AmmannBeenkerCompactStates.lean)
construct alternating states $a,b$ on the eight-point orbits of
$(1,0,0,0)$ and $(1,1,0,0)$ under
$(n_0,n_1,n_2,n_3)\mapsto(-n_3,n_0,n_1,n_2)$.
Their amplitudes alternate between $+1$ and $-1$, and vanish elsewhere.
Lean checks the window decisions, all matching actions and cancellation
outside the supports. The resulting natural-domain identities are
```math
Ha=\frac{35}{16}a,\qquad Hb=\left(\frac{13}{4}+\sqrt2\right)b,
\qquad \langle a,b\rangle=0,\quad \|a\|^2=\|b\|^2=8.
```
The vectors are explicitly proved nonzero and linearly independent.
These local patterns are known type-A and type-B states; their source is
recorded in the [development notes](compact-mode-crossing.md).
The construction alone is not presented as a novelty claim.

### 4.75. A ring crossing and a single-edge change

[AmmannBeenkerCompactCrossing.lean](../SpectralGeometry/AmmannBeenkerCompactCrossing.lean)
uses $A=\operatorname{neighbors}(0)$, the first compact ring, and $K_t=H+tP_A$.
This intervention differs from the radius-two sector $S$. For every real $t$,
```math
K_ta=(35/16+t)a,\qquad K_tb=E_*b,\qquad E_*=13/4+\sqrt2.
```
At $t_*=17/16+\sqrt2$, `compact_crossing` proves the two independent
eigenvector equations at $E_*$. These equations give multiplicity **at least two**. Section 4.78 proves
that it is exactly two; §4.79 certifies a real spectral isolation interval.

The endpoints in $u=\delta_{(1,0,0,0)}-\delta_{(1,1,0,0)}$ are proved
adjacent. Hence $K_{t_*}+\varepsilon|u\rangle\langle u|$ changes an actual
edge weight. For every real $\varepsilon$, `crossing_dark_eigenvector`
proves that the nonzero vector $a+b$ remains an eigenvector at $E_*$.
For the unit vector $q=(a-b)/4$, `crossingBright_energy_response` proves
```math
\langle q,(K_{t_*}+\varepsilon|u\rangle\langle u|)q\rangle=E_*+\varepsilon/4.
```
This is an exact Rayleigh quotient identity. By itself it does not establish
another eigenvalue's value, derivative or quadratic remainder. Section 4.79
provides isolation for the **unperturbed** $K_{t_*}$; the subsequent §§4.93–4.97
establish the genuine moving level, signed shift and quadratic remainder.

### 4.76. The exact central sector and its boundary

[AmmannBeenkerCentralPatch.lean](../SpectralGeometry/AmmannBeenkerCentralPatch.lean)
proves that the radius-two sector $S$ is exactly the origin together with
the two eight-site compact rings of §4.74. `sector_eq_centralPatch` gives
an explicit indexing by `Fin 17`, and `sector_card` proves $\#S=17$.
The reverse inclusion uses the joint physical/internal norm identity to
bound the integer lift, followed by exhaustive Lean arithmetic checks.

Write the cyclic ring vertices as $A_i,B_i$, with $i\in\mathbb Z/8\mathbb Z$,
in the rotation order of §4.74. The origin is adjacent to all $A_i$ and
to no $B_i$. Neither ring has edges within itself, and
```math
A_i\sim B_j\quad\Longleftrightarrow\quad j=i\ \text{or}\ j+1=i.
```
All neighbors of the origin and of the first ring lie in $S$.
The compact-state equations recover the full graph degrees:
`firstRing_degree` gives three, and `secondRing_degree` gives four.
Each $B_i$ has exactly two neighbors inside $S$, namely $A_i,A_{i+1}$,
and exactly two outside. `mem_centralBoundaryEdges` identifies the
complete set of boundary edges, oriented from $S$ to its complement;
`centralBoundaryEdges_card` proves that this set has sixteen elements.
This counts edges, not distinct exterior vertices.

These results describe the central block and its coupling locations using
the previously proved compact states and radial barrier. Section 4.78 uses them to exclude additional eigenvectors at $E_*$.
Section 4.79 subsequently bounds the exterior-to-central coupling in norm
and proves an explicit real spectral exclusion window.

### 4.77. The central crossing kernel and centrally supported eigenvectors

[AmmannBeenkerCentralKernel.lean](../SpectralGeometry/AmmannBeenkerCentralKernel.lean)
defines the principal block of $K_{t_*}-E_*$ on the exact sector from §4.76.
Its diagonal uses the **full graph degree**, including the contribution
of edges to the exterior. The shifted diagonal is $3/2-E_*$ at the origin
and zero on both rings. The off-diagonal entries come from the actual
coordinate-step adjacency, with weight $-1/16$.

`centralCrossingBlock_kernel_iff` identifies every null
vector in the central indexing as
```math
(0,a,-a,a,-a,a,-a,a,-a,b,-b,b,-b,b,-b,b,-b).
```
The parameters are its coordinates 1 and 9. Lean also checks
that this parametrization is injective, that every such vector is in the
kernel, and that its two coordinate directions are the restrictions of
the previously constructed compact states.

`centralCrossingBlock_restriction` relates this finite block to the actual
infinite natural-domain operator for vectors that vanish outside $S$.
`crossing_eigenvector_of_central_support` then gives the explicit conclusion
```math
K_{t_*}x=E_*x,\qquad x|_{S^c}=0
\quad\Longrightarrow\quad
x=x(A_0)a+x(B_0)b,
```
where $a,b$ on the right denote the compact states of §4.74. The finite
calculation uses the second-ring equations to force alternating first-ring
amplitudes; the origin equation forces its amplitude to vanish; the
first-ring equations then force alternation on the second ring.

The support condition is a hypothesis of this lemma. Section 4.78 derives
it for every crossing eigenvector on the infinite domain.
Neither a gap nor a quantitative splitting estimate follows from this
finite-block calculation alone. The gap is established separately in
§4.79, while the one-edge splitting was subsequently established in §§4.93–4.97.

### 4.78. Central support and exact multiplicity of the infinite crossing

[AmmannBeenkerCrossingMultiplicity.lean](../SpectralGeometry/AmmannBeenkerCrossingMultiplicity.lean)
removes the support hypothesis in §4.77. For an arbitrary
natural-domain eigenvector $x$ at $E_*$, write
$L=K_{t_*}-E_*$, $p=P_Sx$ and $q=x-p$. Finite coordinate projection preserves
the natural domain, so every operator evaluation below has its domain witness.

All neighbors of a first-ring vertex lie in $S$, hence $Lq$ vanishes on
that ring. Since $Lx=0$, $Lp$ also vanishes there. The finite central-form
identity and symmetry give
```math
\langle q,Lq\rangle=\langle p,Lp\rangle
  =(3/2-E_*)|p(0)|^2\le0.
```
The previously proved exterior potential barrier and positivity of the
interaction, including the first-ring intervention, supply
```math
(3/4+\sqrt2)\|q\|^2\le\langle q,Lq\rangle.
```
The strictly positive coefficient forces $q=0$. The theorem
`crossing_eigenvector_central_support` therefore derives central support
from the full infinite eigenvector equation. `crossing_eigenvector_representation`
then reuses §4.77 to express every eigenvector in the two compact directions.

`crossingEigenspaceCoordinates` constructs a linear equivalence between
the actual eigenspace inside the natural domain and $\mathbb R^2$, using
the amplitudes at $A_0=(1,0,0,0)$ and $B_0=(1,1,0,0)$ in lift coordinates.
Together the representation and dimension theorems give
```math
\ker(K_{t_*}-E_* I)=\operatorname{span}_{\mathbb R}\{a,b\},
\qquad \dim_{\mathbb R}\ker(K_{t_*}-E_* I)=2,
```
where domain vectors are identified with their images in real $\ell^2$.
The span description uses `crossing_eigenvector_representation` together
with the eigenvector equations of §4.75; `crossingEigenspace_finrank` gives the
dimension. The exterior lower bound above is a form estimate on the
exterior component. This §4.78 argument alone gives no numerical distance
to every other spectral level; §4.79 establishes that distance conservatively.
Quantitative motion of the second level after an edge change is established separately in §§4.93–4.97.

**Palomar registration:** The exact-multiplicity result in this section, represented
by the Comparator-selected `crossingEigenspace_finrank` and
`crossing_eigenvector_representation` statements, was registered as
**PALOMAR-2026-11-06-000012 (version 1)** on 2026-11-06. The separate
spectral-gap theorems of §4.79 are not Comparator-selected statements.


### 4.79. A conservative quantitative real spectral gap at the crossing

[AmmannBeenkerCrossingGapCycle.lean](../SpectralGeometry/AmmannBeenkerCrossingGapCycle.lean),
[AmmannBeenkerCrossingGapFinite.lean](../SpectralGeometry/AmmannBeenkerCrossingGapFinite.lean)
and
[AmmannBeenkerCrossingGapOrthogonality.lean](../SpectralGeometry/AmmannBeenkerCrossingGapOrthogonality.lean)
upgrade the exact crossing of §§4.75–4.78 to a **quantitatively isolated
point of the full real spectrum**. The operator and its domain are unchanged:
$K_t=H+tP_A$ on $D(V)$, with
$t_*=17/16+\sqrt2$ and $E_*=13/4+\sqrt2$.

For a genuine eigenvector at $E\ne E_*$, set $r=|E-E_*|$ and decompose
$x=u+q$, where $u=P_Sx$ is supported on the exact 17-vertex central
sector and $q=x-u$ is exterior. Orthogonality to the two compact
crossing modes eliminates the alternating-ring kernel directions.
`crossingCentralBlock_norm_sq_lower` then gives the central finite-block
squared singular-value bound $1/576$, equivalent to a norm factor $1/24$.
The sixteen oriented boundary edges and the mixed-term estimate yield
`crossingResidual_exterior_projected_norm_le`, controlling the entire
exterior-to-central projected residual with coefficient $1/4$.

The resulting natural-domain inequalities, proved as
`crossingCentralEnergy_off_crossing_bound` and
`crossingExteriorEnergy_off_crossing_linear_bound`, are
```math
\left(\frac1{24}-r\right)\|u\|\le\frac14\|q\|,
\qquad
\left(\frac34+\sqrt2-r\right)\|q\|\le\frac14\|u\|.
```
The strict Schur margin in `crossingGapCandidate_block_no_solution`
forces both norms to vanish for $0\le r\le1/128$. Thus
`crossingGapCandidate_no_other_full_eigenvector` excludes every
nonzero full-domain eigenvector at a different energy in that window.

Crucially, the result does **not** stop at the point spectrum.
`crossingRealSpectrum_iff_full_eigenvector` applies the established
compact-resolvent real spectral-mapping theorem (§§4.21 and 4.32)
to the concrete potential, using its proved lower bound and finite
onsite sublevels. Hence `crossingGapCandidate_no_other_realSpectrum`
and `crossingGapCandidate_realSpectrum_isolated` certify
```math
\sigma_{\mathbb R}(K_{t_*})\cap
\left[E_*-\frac1{128},\,E_*+\frac1{128}\right]=\{E_*\}.
```
Here $\sigma_{\mathbb R}$ is the **real bounded-inverse spectrum on
the natural domain**, not a newly formalized complex-spectrum API.
The inclusion of $E_*$ follows from the nonzero compact-state
eigenvectors (§4.75); the exclusion of all other points follows from
§4.79. The closed interval, including its endpoints, is covered.

The value $g=1/128$ is a **certified conservative lower bound on
the isolation radius**, not the exact spectral spacing or an optimal
constant. This theorem does not assert stability of the twofold
crossing under arbitrary perturbations, identify the moving eigenvalue
after the one-edge change, or provide a derivative, remainder or
finite-patch zero certificate. The **historical first Palomar registration** selected the
exact-multiplicity statements of §4.78. The gap theorems are not
selected as separate statements in any of the four Palomar registrations (§§4.78, 4.98, 4.105, 4.110), but remain included
in the full Lean/Mathlib source build.

