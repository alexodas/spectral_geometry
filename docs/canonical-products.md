[← Main README and table of contents](../README.md)

<details>
<summary>Contents of this document</summary>

- [2.1. Verified analytic core](#21-verified-analytic-core)
- [2.2. A common analytic coordinate for geometric operators](#22-a-common-analytic-coordinate-for-geometric-operators)
- [2.3. Target: a relative product for a finite geometric defect](#23-target-a-relative-product-for-a-finite-geometric-defect)
- [2.4. Entire products, exact zeros and their orders](#24-entire-products-exact-zeros-and-their-orders)
- [2.5. Certified zero clusters from bounded operator error](#25-certified-zero-clusters-from-bounded-operator-error)
- [2.6. Scalar approximation near a multiple spectral zero](#26-scalar-approximation-near-a-multiple-spectral-zero)

</details>

## 2. Canonical product and analytic foundations

### 2.1. Verified analytic core

For positive levels $q_n$, a center $c\in\mathbb C$ and a nonzero direction
$d\in\mathbb C$, the analytic core defines
```math
D_q(s)=\prod_{n=0}^{\infty}
\left(1-\frac{(s-c)^2}{d^2q_n^2}\right).
```

[CanonicalProduct.lean](../SpectralGeometry/CanonicalProduct.lean) defines
admissibility by positivity and a summable compact-set majorant for the
deviations of these factors from one. It proves compact-uniform convergence,
zero localization on the prescribed affine line, a sufficient admissibility
criterion
```math
\sum_{n=0}^{\infty}q_n^{-2}<\infty,
```
and the existence of a zero at each positive prescribed level. The paired
factors encode symmetric locations. The extensions in §2.4 now prove entire
holomorphy, the exact zero set, and the order at every point. Repeated levels
are counted exactly; an infinite tail cannot create additional zeros.

Section 4.48 now proves positive inverse-square summability for full interacting
levels under explicit properness, onsite ordering, summability and gap
hypotheses. Its power-growth corollary reuses the onsite criterion with exponent
greater than one half. `fullSpectrum_admissible_of_positive_summable` applies the
existing admissibility criterion to these levels, including the nonnegative
finite-sector family. Section 4.57 constructs the sorted onsite bijection on
infinite proper site types. Section 4.58 gives a separate positive-interaction
transfer with $V\ge v_0>0$, retaining the gap $v_0$ regardless of the
interaction norm. The analytic theorems apply to these inputs, and §4.49
identifies repetition counts with the original full geometric multiplicities.
The new indexed-point and exact-tag bridge of §§4.50–4.52 also makes this a
quantitative analytic displacement statement for positive finite-sector
perturbations; §4.59 proves its sharper positive-interaction version.
No complex resolvent is needed for this scalar product construction; the
complex-resolvent interface required for relative determinants remains open.
For the explicit octagonal graph, §§4.71–4.72 now derive the summability
inputs and instantiate the entire full products throughout 0≤τ≤4.

### 2.2. A common analytic coordinate for geometric operators

The spectral family, now verified under the hypotheses below, is
```math
F_H(z)=\prod_{n=0}^{\infty}
\left(1-\frac{z^2}{\lambda_n(H)^2}\right),
\qquad
D_H(s)=F_H\!\left(\frac{s-c}{d}\right).
```

The positive full spectrum with exact multiplicities and inverse-square
summability is now available under §§4.44–4.48. The sufficient signed-correction
criterion requires $v_0>\|B\|$ separately from onsite growth; compact resolvent
alone does not give summability or positivity. For symmetric nonnegative $B$,
§4.58 instead proves $\lambda_n(H)\ge v_0>0$ and summability from proper,
inverse-square-summable onsite energies, without a bound on $\|B\|$.
The onsite ordering is constructed by §4.57. Each of these baseline gaps and
summability conclusions persists for nonnegative finite-sector perturbations.
Section 4.49 proves the
exact zero divisor
```math
s=c\pm d\,\lambda_n(H),\qquad D_H(c)=1,
```
with orders equal to the corresponding geometric multiplicities. Both
$F_H$ and $D_H$ are entire, and $D_H(2c-s)=D_H(s)$. The affine-coordinate
identity, normalization and symmetry are proved in §2.4. The exact sequence
interface here addresses the infinite case; finite and empty spectra are not
represented by an artificial infinite repetition of levels.

Using the same $c,d$ for every operator makes zero displacement comparable
across the family. For $c=\tfrac12$ and $d=i$, the positive zero heights
are the positive eigenvalues. The affine coordinate fixes the line; it does
not create spectral correlations or encode a preferred distribution.
For the positive finite-sector intervention of §4.52, the bound
$|d|\kappa\tau\le |z_n^\pm(\tau)-z_n^\pm(0)|\le |d|\tau$ holds for every
index $n$ with $\lambda_n(H)\le E$, throughout $0\le\tau\le R-v_0$ and for
fixed $c,d$. The coefficient is positive since $E<R-\|B\|$ and $v_0<R$.
The energy window may be empty and different indices may share a zero.
For nonnegative $B$, §4.59 proves the same type of conclusion with the sharper
$\kappa=(R-E)/(R-v_0)>0$ under $E<R$, again with the explicit interval
$0\le\tau\le R-v_0$ and without asserting a nonempty target window.
Section 4.72 supplies a concrete application with at least nine indexed
levels on each branch, coefficient $1/2$, and summability derived from the
geometric model. Different indices may coincide; nine slots do not assert
nine distinct zero locations.

### 2.3. Target: a relative product for a finite geometric defect

Suppose the self-adjoint operators $H$ and
```math
H'=H+\iota_S K\iota_S^*
```
have a strictly positive spectral gap, compact resolvent and inverse-square-summable
ordered spectra. Here $S$ is finite, $\iota_S$ is coordinate insertion and
$K$ is a finite Hermitian matrix (real symmetric in the real model).

After constructing the necessary complex resolvent interface, define the
finite Green matrix and perturbation determinant
```math
G_S(z)=\iota_S^*(H-zI)^{-1}\iota_S,
\qquad
\Delta_S(z)=\det(I+K G_S(z)).
```

The proposed identity to establish is
```math
\frac{F_{H'}(z)}{F_H(z)}
=\frac{\Delta_S(z)\Delta_S(-z)}{\Delta_S(0)^2}.
```

It must be stated away from the original spectrum, with nonvanishing
normalization at zero and a meromorphic interpretation accounting for common
zeros, poles and multiplicities. **This identity is a research target, not a
theorem currently verified in this repository.**

The determinant has finite size, but its Green-matrix entries still depend on
the infinite operator. Certified finite-patch approximation is therefore part
of the intended result, rather than a consequence of the determinant's size.
The framework of finite-rank perturbation determinants is classical; see,
for example, [Golinskii, Spectra of infinite graphs with tails](https://doi.org/10.1080/03081087.2016.1155529).
The new §4.52 indexed zero-displacement inequality compares the products'
zeros without a relative determinant; it does not establish the proposed
identity or approximate a determinant. Any originality claim must concern a
precisely identified geometric or quantitative contribution beyond that
framework.

### 2.4. Entire products, exact zeros and their orders

[CanonicalProductAnalytic.lean](../SpectralGeometry/CanonicalProductAnalytic.lean)
proves `canonicalProduct_differentiable` for every admissible positive sequence.
The proof applies the locally uniform limit theorem to finite polynomial
products. `canonicalProductAlong_differentiable` also covers every injectively
indexed subproduct, including finite and empty subproducts.

For $d\ne0$, `canonicalProduct_zero_iff` proves
```math
D_q(s)=0\quad\Longleftrightarrow\quad
\exists n,\ s=c+dq_n\ \text{or}\ s=c-dq_n.
```
Absolute summability of the factor deviations prevents a nonzero-factor tail
from acquiring an extra zero. `canonicalProduct_affine_coordinate` identifies
$D_q(s)$ with the standard-coordinate product at $(s-c)/d$.
`canonicalProduct_at_center` and `canonicalProduct_reflection` prove
$D_q(c)=1$ and $D_q(2c-s)=D_q(s)$; they do not require a choice of normalization
that varies with the operator.

[CanonicalProductZeroOrder.lean](../SpectralGeometry/CanonicalProductZeroOrder.lean)
proves that only finitely many factors vanish at any point. Each such factor
has a simple zero when the level is positive and $d\ne0$. Splitting off this
finite set leaves an entire product nonzero at the point, so
`canonicalProduct_analyticOrderAt` gives its exact order. In particular,
`canonicalProduct_order_at_signed_level` proves, for $r>0$,
```math
\operatorname{ord}_{c+dr}D_q
=\operatorname{ord}_{c-dr}D_q
=\#\{n:q_n=r\}.
```
For $d\ne0$, the fiber is finite under the admissibility hypotheses. No simple-spectrum
assumption is made. For the full spectral enumeration, §4.49 identifies this
cardinality with the previously defined geometric eigenspace dimension.
The extensions in §§4.50–4.52 prove the oriented differences and
quantitative norm estimates between corresponding indexed points for the
same fixed $c,d$. Via an explicitly constructed zero-color matching tag
enumeration and uniqueness of complete monotone domain eigenbases, the
points are zeros of the full products and their orders agree with the
respective operators' geometric multiplicities. The first statement keeps
the absolute value of the real level difference until positivity is known.
The additional bounded-error zero certificates are described in §2.5.
A relative determinant identity, a complex operator spectral theorem and
finite-patch approximation estimates remain open.

### 2.5. Certified zero clusters from bounded operator error

Sections 4.53–4.56 give a quantitative certificate using **operator error**
and **spectral boundary margins**. Let $H=M_V+B$, $\widetilde H=H+K$ on the
same natural domain, with symmetric bounded $B,K$. Under the explicit properness,
onsite-ordering and summability assumptions, require
```math
\|K\|\le\eta<v_0-\|B\|,\qquad V\ge v_0.
```
Both complete ordered spectra exist, remain positive and inverse-square
summable, and satisfy
```math
|\lambda_i(\widetilde H)-\lambda_i(H)|\le\eta,
\qquad
|z_i^\pm(\widetilde H)-z_i^\pm(H)|\le |d|\eta.
```

Write $q_i=\lambda_i(H)$. A cut at energy $t$ and index $k$ is certified by
```math
k>0\ \Longrightarrow\ q_{k-1}+\eta<t,
\qquad t+\eta<q_k.
```
At $k=0$ only the second inequality is required. For a positive window
$0<a<b$, apply these finite checks at $(a,m)$ and $(b,n)$. For both operators,
the indices in $(a,b)$ are then exactly $m,\ldots,n-1$. On **each** reflected
segment $c\pm d[a,b]$, the finite set $Z^\pm$ consists of all product zeros,
the endpoints are zero-free, and
```math
\sum_{z\in Z^\pm}\operatorname{ord}_z D=n-m.
```
The sum is over distinct complex points, weighted by their exact analytic
orders, which are the respective operators' geometric multiplicities.
Repeated levels may split or merge inside the window. Empty windows are
included; the underlying full-spectrum sequence still requires infinitely
many sites. The certificate does not assert that every chosen window has
large enough boundary margins.

Compact-uniform convergence of products alone is not used to infer these
bounds. A finite-patch application must first supply a justified comparison
of operators or resolvents and an appropriate quantitative error certificate.
A finite matrix on a different Hilbert space does not automatically satisfy
the common-domain bounded-error hypothesis. Scalar local zero-location
and exact disk-count certificates are now proved in §2.6 under a strict
circular-boundary error. Noncircular contour counts and a finite-patch
error certificate require further work.

### 2.6. Scalar approximation near a multiple spectral zero

Sections 4.60–4.65 give a local certificate for an arbitrary analytic
approximant $g$ of a full spectral product $f=D_H$. At a zero $a$ with
finite positive order $m$, the formalization constructs $\rho,C>0$ such that
```math
|f(z)|\ge C|z-a|^m\qquad (|z-a|\le\rho).
```
The reference disk contains only the distinct zero $a$, with its full
multiplicity $m$. Suppose $g$ is analytic on a neighborhood of the closed
disk and, on its boundary,
```math
|g(z)-f(z)|\le\varepsilon,\qquad
\varepsilon\ge0,\qquad \varepsilon<C\rho^m.
```
Then $g$ has exactly $m$ zeros in the open disk **counting analytic
multiplicities**, has none on its boundary,
and every zero $z$ in the closed disk satisfies
```math
|z-a|^m\le\varepsilon/C,
\qquad |z-a|\le(\varepsilon/C)^{1/m}.
```
For the full spectral product, $m$ is the original geometric eigenspace
multiplicity. A linear location estimate is obtained when $m=1$; no
simple-spectrum assumption is imposed in the general result. The location
bound uses local analytic factorization and the maximum modulus principle;
the exact count uses the disk argument principle and Rouché's theorem.
The earlier existence/location theorem with $2\varepsilon<C\rho^m$
remains available unchanged in §4.60. An arbitrary approximant's zeros may
split and may lie off the prescribed line; their total order is conserved.

More generally, if $f,g$ are analytic near any closed disk of radius $R>0$
and $|g-f|<|f|$ on its circular boundary, their total interior zero orders
are equal (§§4.63–4.64). The strict inequality proves that neither function
vanishes on the boundary. The reference disk need not isolate a single
zero; zero-free disks and disks containing several distinct or repeated
zeros are covered. This statement concerns circular contours, not arbitrary
Jordan curves.

The scalar error can be certified from a finite product
$P_N=\prod_{n<N}(1-((z-c)/d)^2/q_n^2)$. For positive $q_n$ with
$S=\sum_nq_n^{-2}<\infty$, put $T_N=\sum_{k\ge0}q_{k+N}^{-2}$.
On any set with $|(z-c)/d|^2\le A$, $A\ge0$, the proved bound is
```math
|D_q(z)-P_N(z)|\le e^{AS}(e^{AT_N}-1).
```
The right side tends to zero; certified upper bounds for $S,T_N$ can
replace the infinite sums. An additional error $\eta$ in approximating
$P_N$ adds to this bound. The estimate remains valid at zeros of $P_N$
and includes $N=0$. With $\varepsilon=E_N(A)+\eta<C\rho^m$, §4.65
certifies the exact local count as well as the location bound. Since
$E_N(A)\to0$, every sufficiently long exact partial product has the full
local count; a numerical cutoff still requires a numerical tail bound.
These are truncations of one fixed spectral sequence. Neither a
finite-patch operator error nor numerical values for the local
constants $C,\rho$ are supplied by the abstract existence theorem.

Sections 4.66–4.67 now supply a worked numerical instance. For
$q_n=n+1$, $c=0$, $d=1$, $a=1$, the full onsite spectral product has an
explicit entire cofactor $G$ with $F(z)=(z-1)G(z)$ and
```math
|G(z)|\ge\frac15\quad (|z-1|\le\tfrac14),\qquad
\sum_nq_n^{-2}\le2,\qquad
\sum_{k\ge0}q_{k+N}^{-2}\le\frac1N\quad(N\ge1).
```
For any sequence with $q_n\ge n+1$, the existing error budget satisfies
$E_N(A)\le324/N$ when $0\le A\le2$ and $N\ge2$. On the displayed disk,
$A=25/16$, so every $N\ge16384$ gives $|F-P_N|\le1/50$.
If an analytic $g$ has boundary error $|g-P_N|\le1/100$, then
$|g-F|\le3/100<1/20=C\rho$. The proved certificate gives total zero
order **one**, no boundary zeros, and $|z-1|\le3/20$ for every zero
in the disk. The cutoff is sufficient, not asserted minimal. This is an
infinite diagonal operator on its natural domain, not a finite-patch or
a named tiling construction; the complete spectral identification is
proved in §4.67.

