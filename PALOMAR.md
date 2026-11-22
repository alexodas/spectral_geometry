# Second Palomar candidate — exact protection of a dark mode and bright-mode feedback on an infinite octagonal graph

**Status: draft candidate; not submitted or registered.** The first
Palomar registration `PALOMAR-2026-11-06-000012` (v1, 2026-11-06)
remains historically unchanged. This repository's current
[`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean),
[`comparator.json`](comparator.json), and
[`formalization.yaml`](formalization.yaml) prepare a **new
scientific selection**. The full 104-module source containing the
original 14 bright-amplitude lemmas was reported Lean green by the
maintainer on PR #86; the newly bundled theorem and its independent
Comparator configuration have **not yet been verified**.

## The proposed one-theorem statement

The source declaration is
`SpectralGeometry.AmmannBeenker.crossingOneEdgeDarkBrightResponse`
in [`AmmannBeenkerBrightAmplitude.lean`](SpectralGeometry/AmmannBeenkerBrightAmplitude.lean).
It conjoins **three related clauses** about one and the same rank-one
edge perturbation. They form one new selected scientific theorem, not
three separately registered statements.

Use the concrete infinite, centered, open-window Ammann–Beenker
cut-and-project vertex graph with quadratic confinement
`V(v)=1+|p(v)|²`. The natural domain is
`D(V)={x∈ℓ²:Vx∈ℓ²}`; the physical graph Laplacian has weight `1/16`
per edge and an eight-neighbor tuning `t_*=17/16+√2`.
At energy `E_*=13/4+√2`, let `a,b` be the two already classified
alternating eight-site compact modes (squared norms `8`).
Choose the actual adjacent endpoints
`u=(1,0,0,0)`, `v=(1,1,0,0)` and
`W=|δ_u-δ_v⟩⟨δ_u-δ_v|`. Write
`H_ε=K_*+εW`, `D=(a+b)/4`, `F=(a-b)/4`, and let `Q`
project orthogonally away from `span{a,b}`.

**For every real edge strength `ε` and every `x∈D(V)`,**
the candidate asserts

```math
H_\varepsilon D=E_*D,\qquad
\langle F,H_\varepsilon x\rangle
=\left(E_*+\frac{\varepsilon}{4}\right)\langle F,x\rangle
 +\varepsilon\langle F,WQx\rangle,
```

and the explicit compression-error inequality

```math
\left|\langle F,H_\varepsilon x\rangle
 -\left(E_*+\frac{\varepsilon}{4}\right)\langle F,x\rangle\right|
\le2|\varepsilon|\,\|Qx\|.
```

These are **full-space real operator statements**. The dark state is
an exact eigenvector for all strengths, not a consequence of
truncating to two levels. The bright matrix element has a generally
nonzero coupling to the external modes. In particular, the coefficient
`ε/4` is **not** claimed to be a shifted eigenvalue, and the theorem
does **not** construct a complex Schrödinger propagator, prove
adiabatic dynamics, or establish state preparation.

## Why it might interest researchers

For **mathematical spectral and functional analysis**, the notable
feature is a quantitative, exactly defined protected/coupled
decomposition for a local rank-one perturbation of an unbounded
self-adjoint operator on a concrete infinite graph, including an
explicit external-mode error. This may be relevant to mathematical
physicists working on discrete Schrödinger operators, localized
eigenvectors, perturbation theory and aperiodic geometry.

For **theoretical condensed-matter and photonic lattice physics**,
the result distinguishes a robust dark compact mode from a bright
combination that can excite modes outside a two-level truncation.
Potential audiences include Ammann–Beenker quasicrystal
tight-binding specialists, compact localized state and flat-band
researchers, and theorists of resonator or photonic networks.
Relevant antecedents include
[M. Ö. Oktel, *Phys. Rev. B* 104, 014204 (2021)](https://doi.org/10.1103/PhysRevB.104.014204)
and
[M. Röntgen, C. V. Morfonios and P. Schmelcher, *Phys. Rev. B* 97, 035161 (2018)](https://doi.org/10.1103/PhysRevB.97.035161).
The patterns, dark-state phenomena and elementary rank-one
perturbation methods are not claimed as newly discovered.
**Novelty, priority, independent research interest and experimental
realization remain unestablished.**

## Independent Challenge and next verification

The new `Challenge.lean` imports **only Mathlib** and is about
**488 lines, approximately 15 KiB** (below Palomar's 1,000-line and
100-KiB hard caps). Its selected theorem names include **one
scientific conclusion** and six **model-construction proposition
witnesses**: `admitted_zero`, `mate_involutive`,
`compactA_mem_domain`, `compactB_mem_domain`,
`compactSiteA_admitted`, and `compactSiteB_admitted`.
Those witnesses allow definition of the actual graph, natural-domain
vectors and edge endpoints; they are not six more research claims.
The Challenge intentionally uses proposition placeholders, while the
substantive source contains no new `sorry` or axioms. Definitions
are to be compared transitively, with no definition holes.

Before any actual Palomar submission we must obtain a green
**full Lean build and independent Comparator verification**, including
the mandatory kernels, on this precise new package, then pin an
immutable public 40-character commit. A green build on the
**earlier fourteen-lemma source** does not establish that the newly
prepared Challenge/Comparator selection passes. Palomar registration
requires a separate submitter action after review.

---

# Historical Palomar registration — exact multiplicity of a compact crossing on an infinite octagonal graph

**Registration:** `PALOMAR-2026-11-06-000012` (version 1), 2026-11-06.
The following historical record describes the **previously registered** result.
The distinct one-edge dark/bright result has since been proposed as a **new
candidate**, not submitted or registered. The old proof and its original
registry record remain unchanged.

The principal theorem is `SpectralGeometry.AmmannBeenker.crossingEigenspace_finrank`.
The companion `SpectralGeometry.AmmannBeenker.crossing_eigenvector_representation`
identifies every vector in that eigenspace. Both are proved in
[AmmannBeenkerCrossingMultiplicity.lean](SpectralGeometry/AmmannBeenkerCrossingMultiplicity.lean)
and described in [README §4.78](README.md#478-central-support-and-exact-multiplicity-of-the-infinite-crossing).

## Mathematical statement

Vertices are the admitted integer lifts in the centered open octagonal
cut-and-project window of README §4.68. The boundary is excluded; two
vertices are adjacent when their lifts differ by a signed coordinate step.
On real $\ell^2$ of this infinite graph, let $p(v)$ be physical position,
$V(v)=1+|p(v)|^2$, and $D(V)=\{x\in\ell^2:Vx\in\ell^2\}$. Let $A$ be the
eight neighbors of the origin. On $D(V)$ define
```math
(K_t x)(v)=(V(v)+t\,\mathbf{1}_A(v))x(v)
  +\tfrac1{16}\sum_{w\sim v}\bigl(x(v)-x(w)\bigr).
```
The alternating states $a,b$ have amplitudes $+1,-1$ in cyclic order on
their respective eight-site rings and vanish elsewhere. Their first sites
are $A_0=(1,0,0,0)$ and $B_0=(1,1,0,0)$ in lift coordinates. The source
proves that their eigenvalues are $35/16+t$ and $13/4+\sqrt2$, respectively.
Set $t_*=17/16+\sqrt2$ and $E_*=13/4+\sqrt2$. The selected conclusions are
```math
\dim_{\mathbb R}\ker(K_{t_*}-E_* I)=2,\qquad
K_{t_*}x=E_*x\ \Longrightarrow\ x=x(A_0)a+x(B_0)b\quad(x\in D(V)).
```
Thus, identifying domain vectors with their images in $\ell^2$, the kernel
is precisely $\operatorname{span}_{\mathbb R}\{a,b\}$. Support is a
conclusion: no eigenvector at this energy can extend beyond the two rings.

## Why the infinite graph matters

Two independent compact eigenvectors would only give a lower bound of two.
Even a complete calculation on a finite patch would not rule out another
eigenvector with an exterior component. The proof does rule this out.
Let $S=\{v:|p(v)|\le2\}$, consisting of the origin and the two rings, and
write $x=u+q$ with $u=P_Sx$. For $L=K_{t_*}-E_* I$, locality of the first
ring, the central block identity and symmetry give
```math
\langle q,Lq\rangle=\langle u,Lu\rangle=(3/2-E_*)|u(0)|^2\le0.
```
The exterior onsite barrier and the nonnegative interaction also give
$(3/4+\sqrt2)\|q\|^2\le\langle q,Lq\rangle$, hence $q=0$. The central
block retains the full graph degrees, including edges to the exterior;
its kernel gives precisely the two alternating directions. The amplitudes
at the two first sites give a linear equivalence with $\mathbb R^2$.

## Research interest, sources and limits

For researchers studying localization in quasicrystals, the question is
whether two familiar local patterns account for a whole spectral level, or
merely coexist with other states at the same energy. The theorem answers
that question exactly for a specified confined operator on an infinite
octagonal graph. The Comparator-selected result may also interest theoretical
condensed-matter physicists studying compact localized states and
quasicrystal localization: beyond constructing two degenerate compact modes,
it excludes any additional eigenstate at their energy, including one
extending outside the central finite patch. This classification **may be
new for this model**. Priority has not been established.

- M. Ö. Oktel, [*Strictly localized states in the octagonal Ammann–Beenker
  quasicrystal*](https://doi.org/10.1103/PhysRevB.104.014204), §IV (2021):
  source of the type-A and type-B patterns for the vertex tight-binding
  model. The patterns themselves are not claimed as new.
- M. Röntgen, C. V. Morfonios and P. Schmelcher, [*Compact localized states
  and flat bands from local symmetry partitioning*](https://doi.org/10.1103/PhysRevB.97.035161)
  (2018): background on constructing and tuning compact states by local symmetry.
- F. P. M. Beenker, [*Algebraic theory of non-periodic tilings of the plane
  by two simple building blocks: a square and a rhombus*](https://pure.tue.nl/ws/files/4269555/253166.pdf)
  (1982): geometric background.

The Comparator-selected result concerns the centered graph, the quadratic
potential, the specified ring intervention, and one crossing energy. Its
exact-multiplicity statements do not themselves assert a spectral gap.
Separately, the full-project theorem
`crossingGapCandidate_no_other_realSpectrum`
([README §4.79](README.md#479-a-conservative-quantitative-real-spectral-gap-at-the-crossing))
certifies that no other point of the real bounded-inverse spectrum of this
same unperturbed infinite operator lies within the closed radius $1/128$
of $E_*$. That conservative isolation bound is **not** an additional
Comparator-selected statement. A quantitative law for the eigenvalue
that may move under a one-edge change remains open. The exterior energy
estimate above, on its own, is not the quantitative gap proof.

## Human origin and AI-assisted development

Alessandro Odasso originated the informal project idea, directs the work
and is the responsible maintainer. He does not identify as a mathematician;
his stated interest is exploring LLMs in scientific research. According to
his account, OpenAI GPT-6 assisted throughout the GitHub/Lean development.
No human mathematical peer review or exhaustive priority assessment is claimed.
[formalization.yaml](formalization.yaml) records the contributor roles,
sources and correspondence between the statements and the Lean declarations.

## Independent statement verification

The [pre-change Challenge](https://github.com/alexodas/spectral_geometry/blob/d6234b0d0d4f06827fb741599a492449d9265ee2/Challenge.lean)
imports only Mathlib and specifies the graph, operator, domain, compact
modes, sites and eigenspace. The corresponding
[pre-change Solution](https://github.com/alexodas/spectral_geometry/blob/d6234b0d0d4f06827fb741599a492449d9265ee2/Solution.lean)
imports the old substantive proof module. The
[pre-change Comparator](https://github.com/alexodas/spectral_geometry/blob/d6234b0d0d4f06827fb741599a492449d9265ee2/comparator.json)
selects the two crossing conclusions and three model witnesses
used to define the model: `admitted_zero`, `mate_involutive` and `centralLift_admitted`.
Only these five statements had placeholders in the historical Challenge;
all are proved in the source. Definitions are compared transitively with no definition
holes. Challenge groups declarations by source module to preserve the names
of Lean's generated proof terms. The independent checks use Lean and the
bundled NanoDa and con-ron kernels; the full library is built separately.

```sh
python3 scripts/check-palomar-layout.py
python3 scripts/check-lean-sources.py
python3 scripts/check-unified-comparator.py
python3 scripts/check-full-proof-coverage.py
python3 scripts/check-no-proof-holes.py
ruby scripts/validate-formalization.rb
lake exe cache get
lake build SpectralGeometry Challenge Solution
bash scripts/verify-comparator.sh
```

This historical verification package is shown at the **post-PR #85
pre-change project checkpoint** above; its commit is not asserted to be the
original Palomar registration commit. The 2026 registered selection remains
at the immutable commit retained by Palomar. The current root
Challenge/Solution/Comparator files prepare a **different selection**;
passing CI or preparing files does not register it.
