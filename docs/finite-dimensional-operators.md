[← Main README and table of contents](../README.md)

<details>
<summary>Contents of this document</summary>

- [3.1. Symmetry under controlled perturbations](#31-symmetry-under-controlled-perturbations)
- [3.2. Positivity under controlled perturbations](#32-positivity-under-controlled-perturbations)
- [3.3. Nonnegative energy from geometry](#33-nonnegative-energy-from-geometry)
- [3.4. Strictly positive energies and eigenvalues](#34-strictly-positive-energies-and-eigenvalues)

</details>

## 3. Finite-dimensional geometric operators

### 3.1. Symmetry under controlled perturbations

The first theorem about our geometric operator is formalized in **[`SpectralGeometry/FinitePerturbation.lean`](../SpectralGeometry/FinitePerturbation.lean)** and checked by Lean.

**In simple terms:** imagine a finite collection of tiles. Each tile has its own energy, pairs of tiles interact with symmetric weights, and we add a perturbation matrix `P` whose influence is controlled by `ε`. If both the interaction weights and `P` are symmetric, **the complete matrix remains symmetric whatever real value we choose for `ε`**:

```math
w(t,u)=w(u,t),\quad P_{tu}=P_{ut}
\quad\Longrightarrow\quad
(H_{\varepsilon})_{tu}=(H_{\varepsilon})_{ut}
\quad\text{for every }\varepsilon\in\mathbb R.
```

The file also proves that setting `ε=0` recovers exactly the unperturbed geometric matrix. This is useful because real symmetric finite matrices have real eigenvalues, so changing a symmetric perturbation cannot destroy that structural feature.

**Scope of this module:** the verified theorem concerns a *finite* matrix; symmetry alone does not imply positive eigenvalues or any infinite-dimensional spectral conclusions. Later §§4.20–4.30 establish conditional self-adjointness, compact resolvent, and isolation and local finiteness of genuine real eigenvalues for the abstract infinite matching-family operator. Conditional real-spectrum enumeration with exact geometric multiplicities is established later in §§4.36–4.37, qualitative divergence in §4.38, and a positive real spectral gap under explicit assumptions in §4.39. Quantitative index-wise comparison and sufficient full-spectrum inverse-square summability are proved under the additional hypotheses in §§4.44–4.48.

### 3.2. Positivity under controlled perturbations

The next theorem is formalized in **[`SpectralGeometry/FinitePositiveEnergy.lean`](../SpectralGeometry/FinitePositiveEnergy.lean)**. It concerns the *quadratic energy* of the very same finite matrix defined in the preceding file. For a state `ψ`, define:

```math
Q_M(\psi)=\sum_{t,u}\psi(t)\,M_{tu}\,\psi(u).
```

The formalized identity says that the perturbed energy separates exactly into two parts:

```math
Q_{H_\varepsilon}(\psi)=Q_{H_0}(\psi)+\varepsilon Q_P(\psi).
```

**In simple terms:** if the original geometric operator has nonnegative energy for every configuration, and the chosen perturbation also has nonnegative energy, then turning on that perturbation with `ε\ge0` cannot make the total energy negative:

```math
\bigl(Q_{H_0}(\psi)\ge0,\ Q_P(\psi)\ge0,\ \varepsilon\ge0\bigr)
\quad\Longrightarrow\quad Q_{H_\varepsilon}(\psi)\ge0.
```

The Lean file also proves that **strictly positive** base energy on every nonzero configuration stays strictly positive under the same assumptions. These results concern all tile-amplitude configurations, not a selection of eigenfunctions.

**Scope of the second result:** this finite-dimensional theorem proves *stability* of positivity, assuming positivity of the original and perturbation energies. The following section derives a sufficient condition for the original energy from the geometric inputs themselves. The distinct infinite-operator results, including conditional self-adjointness, compact resolvent and locally finite real point spectrum, are proved later in §§4.20–4.30. Under additional hypotheses, the full interacting real spectrum is subsequently enumerated with exact geometric multiplicities (§4.37) and its ordered eigenvalues are proved to tend to `+∞` (§4.38). Quantitative growth comparison and sufficient inverse-square summability are proved under the additional hypotheses in §§4.46–4.48.

### 3.3. Nonnegative energy from geometry

The third geometric result is developed in **[`SpectralGeometry/FiniteGeometricEnergy.lean`](../SpectralGeometry/FiniteGeometricEnergy.lean)**. It answers the natural question left open by the previous section: *when do the tile energies and interaction weights themselves guarantee nonnegative energy?*

For a finite set of tiles, assume the individual energies are nonnegative, the pair weights are symmetric and nonnegative, and self-interaction weights vanish (`w(t,t)=0`, consistent with summing only over `u\ne t`). The quadratic energy of the unperturbed matrix can then be rewritten as a **sum of squares**:

```math
Q_{H_0}(\psi)=
\sum_t V(t)\psi(t)^2+
\frac12\sum_{t,u}w(t,u)\bigl(\psi(t)-\psi(u)\bigr)^2.
```

Each summand is nonnegative. Thus **the geometry alone forces `Q_{H_0}(\psi)\ge0` for every real tile-amplitude configuration**. The factor `1/2` compensates for counting each pair of distinct tiles in both directions.

Combining this with the preceding perturbation theorem also gives nonnegative energy for `H_\varepsilon=H_0+\varepsilon P` whenever `\varepsilon\ge0` and the quadratic energy of `P` is nonnegative.

**Scope:** this is a statement about finite quadratic forms. Nonnegative energy allows *zero* eigenvalues; it does not itself establish strictly positive eigenvalues, an infinite self-adjoint operator, compact resolvent, or the inverse-square spectral summability needed for the canonical product.

### 3.4. Strictly positive energies and eigenvalues

The next step is formalized in **[`SpectralGeometry/FiniteStrictPositivity.lean`](../SpectralGeometry/FiniteStrictPositivity.lean)**. The preceding theorem ruled out *negative* quadratic energy, but still allowed energy equal to zero. Here we prove a sufficient condition that excludes zero for every nonzero configuration.

Assume **every tile has strictly positive individual energy** (`V(t)>0`), while interactions have symmetric nonnegative weights (`w(t,u)=w(u,t)\ge0`, with `w(t,t)=0`). Then the established sum-of-squares identity gives:

```math
\psi\ne0 \quad\Longrightarrow\quad
Q_{H_0}(\psi)=
\sum_t V(t)\psi(t)^2+
\frac12\sum_{t,u}w(t,u)(\psi(t)-\psi(u))^2>0.
```

**Why is it strictly positive?** For a nonzero configuration there is at least one tile where `\psi(t)\ne0`. Since `V(t)>0`, the individual-energy term for that tile is strictly positive, and every other term is nonnegative.

The same conclusion holds for the perturbed operator `H_\varepsilon=H_0+\varepsilon P` if `\varepsilon\ge0` and `Q_P(\psi)\ge0` for every configuration. The Lean file additionally proves the corresponding **real eigenvalue positivity**: for every real eigenpair `H_\varepsilon\psi=\lambda\psi` with `\psi\ne0`, we have `\lambda>0`. Indeed, on an eigenvector:

```math
Q_{H_\varepsilon}(\psi)=
\lambda\sum_t\psi(t)^2>0
\quad\Longrightarrow\quad \lambda>0.
```

Together with the **symmetry theorem** (when `P` is symmetric), this means every eigenvalue of the real symmetric *finite* perturbed matrix is strictly positive under these hypotheses.

**Scope:** the result is finite-dimensional; the hypothesis `V(t)>0` for every tile is sufficient, not necessarily optimal. This finite-dimensional theorem does not itself construct the infinite operator or establish a uniform gap across growing patches. The later abstract infinite-operator construction appears in §4; sufficient inverse-square summability for the interacting spectrum is proved in §4.48 under explicit growth, ordering and positive-gap hypotheses.

