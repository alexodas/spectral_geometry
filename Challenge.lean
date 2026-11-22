module

public import Mathlib

public section

/-!
# Signed splitting of two localized energies on an infinite octagonal graph

This Mathlib-only Challenge defines the same concrete infinite
Ammann--Beenker vertex graph, confining potential, two compact localized
modes and one selected edge as the verified proof library.

The one selected scientific theorem states that a sufficiently small
nonzero change to this edge leaves the dark eigenvalue and its simple
eigenspace fixed while producing exactly one other simple eigenvalue in
a precisely stated neighborhood. It gives the sign and quantitative
second-order error of the moving energy and controls its true
infinite-dimensional eigenvector outside the original localized plane.

All conclusions concern real eigenvalues and the original natural
domain of the full infinite operator. No complex quantum evolution,
two-state approximation or state-preparation theorem is asserted.

Six supporting proposition placeholders are needed to define the
concrete graph and its compact modes; they are not additional selected
scientific results. All definitions remain concrete, with no holes.
-/

namespace SpectralGeometry

noncomputable section

-- Source module: SpectralGeometry.InfiniteOnsite
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

@[expose] abbrev TileHilbert (Tile : Type*) : Type _ :=
  lp (fun _ : Tile => ℝ) 2

variable {Tile : Type*}

@[expose] noncomputable def infiniteOnsiteDomain
    (V : Tile → ℝ) : Submodule ℝ (TileHilbert Tile) where
  carrier := {ψ | Memℓp (fun t : Tile => V t * ψ t) 2}
  zero_mem' := by
    have hz : Memℓp (fun _ : Tile => (0 : ℝ)) 2 := zero_mem_ℓp'
    simpa using hz
  add_mem' := by
    intro f g hf hg
    have h : Memℓp
        ((fun t : Tile => V t * f t) + fun t : Tile => V t * g t) 2 :=
      hf.add hg
    change Memℓp (fun t : Tile => V t * (f + g) t) 2
    have heq :
        (fun t : Tile => V t * (f + g) t) =
          ((fun t : Tile => V t * f t) + fun t : Tile => V t * g t) := by
      funext t
      simp [mul_add]
    rw [heq]
    exact h
  smul_mem' := by
    intro a f hf
    have h : Memℓp (fun t : Tile => a * (V t * f t)) 2 :=
      hf.const_mul a
    change Memℓp (fun t : Tile => V t * (a • f) t) 2
    have heq :
        (fun t : Tile => V t * (a • f) t) =
          (fun t : Tile => a * (V t * f t)) := by
      funext t
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact h

@[expose] noncomputable def infiniteOnsiteOperator
    (V : Tile → ℝ) :
    (infiniteOnsiteDomain V) →ₗ[ℝ] TileHilbert Tile where
  toFun := fun ψ =>
    ⟨(fun t : Tile => V t * ψ.1 t : PreLp (fun _ : Tile => ℝ)), ψ.2⟩
  map_add' := by
    intro f g
    apply lp.ext
    funext t
    change V t * (f.1 t + g.1 t) =
      V t * f.1 t + V t * g.1 t
    ring
  map_smul' := by
    intro a f
    apply lp.ext
    funext t
    change V t * (a * f.1 t) = a * (V t * f.1 t)
    ring

end

-- Source module: SpectralGeometry.InfiniteOnsiteDensity
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

-- A small Mathlib-only proof of the domain membership of a single-site
-- state, needed to reconstruct the source's domainLatticeSingle definition.
-- This is a supporting proof, not an additional Palomar selection.
section

variable {Tile : Type*} [DecidableEq Tile]

theorem infiniteOnsiteDomain_single
    (V : Tile → ℝ) (i : Tile) (a : ℝ) :
    lp.single (2 : ENNReal) i a ∈ infiniteOnsiteDomain V := by
  classical
  have heq :
      (fun t : Tile => V t *
        (lp.single (2 : ENNReal) i a : TileHilbert Tile) t) =
        (fun t : Tile =>
          (lp.single (2 : ENNReal) i (V i * a) : TileHilbert Tile) t) := by
    funext t
    by_cases hti : t = i
    · subst t
      simp
    · simp only [lp.single_apply, Pi.single_eq_of_ne hti, mul_zero]
  have hmem : Memℓp
      (fun t : Tile => V t *
        (lp.single (2 : ENNReal) i a : TileHilbert Tile) t) 2 := by
    rw [heq]
    exact (lp.single (2 : ENNReal) i (V i * a) : TileHilbert Tile).property
  exact hmem

end

-- Source module: SpectralGeometry.InfiniteOnsiteCompactResolvent
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*}

@[expose] noncomputable def infiniteOnsiteDiagonalContraction
    (c : Tile → ℝ) (hc : ∀ t : Tile, ‖c t‖ ≤ 1) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile := by
  let F : TileHilbert Tile →ₗ[ℝ] TileHilbert Tile :=
    { toFun := fun f =>
        ⟨(fun t : Tile => c t * f t : PreLp (fun _ : Tile => ℝ)),
          f.property.mono' (fun t => by
            calc
              ‖c t * f t‖ = ‖c t‖ * ‖f t‖ := norm_mul _ _
              _ ≤ 1 * ‖f t‖ :=
                mul_le_mul_of_nonneg_right (hc t) (norm_nonneg _)
              _ = ‖f t‖ := one_mul _)⟩
      map_add' := by
        intro f g
        apply lp.ext
        funext t
        change c t * (f t + g t) = c t * f t + c t * g t
        ring
      map_smul' := by
        intro r f
        apply lp.ext
        funext t
        change c t * (r * f t) = r * (c t * f t)
        ring }
  exact F.mkContinuous 1 (fun f => by
    calc
      ‖F f‖ ≤ ‖f‖ := lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun t => by
        change ‖c t * f t‖ ≤ ‖f t‖
        calc
          ‖c t * f t‖ = ‖c t‖ * ‖f t‖ := norm_mul _ _
          _ ≤ 1 * ‖f t‖ :=
            mul_le_mul_of_nonneg_right (hc t) (norm_nonneg _)
          _ = ‖f t‖ := one_mul _)
      _ = 1 * ‖f‖ := (one_mul _).symm)

end

-- Source module: SpectralGeometry.InfiniteLocalMatching
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*} [DecidableEq Tile]

@[expose] noncomputable def infiniteTileReindex (σ : Tile ≃ Tile) :
    TileHilbert Tile →ₗᵢ[ℝ] TileHilbert Tile where
  toFun := fun ψ => by
    refine ⟨(fun t => ψ (σ t) : PreLp (fun _ : Tile => ℝ)), ?_⟩
    have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
    have hsum : Summable (fun t : Tile => ‖ψ t‖ ^ (2 : ENNReal).toReal) :=
      (memℓp_gen_iff hp).mp ψ.property
    have hsum' :
        Summable (fun t : Tile => ‖ψ (σ t)‖ ^ (2 : ENNReal).toReal) :=
      (σ.summable_iff).mpr hsum
    exact (memℓp_gen_iff hp).mpr hsum'
  map_add' := by
    intro ψ φ
    apply lp.ext
    funext t
    rfl
  map_smul' := by
    intro c ψ
    apply lp.ext
    funext t
    rfl
  norm_map' := by
    intro ψ
    have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
    let φ : TileHilbert Tile :=
      ⟨(fun t => ψ (σ t) : PreLp (fun _ : Tile => ℝ)),
        (memℓp_gen_iff hp).mpr
          ((σ.summable_iff).mpr ((memℓp_gen_iff hp).mp ψ.property))⟩
    change ‖φ‖ = ‖ψ‖
    have hsum :
        (∑' t, ‖φ t‖ ^ (2 : ENNReal).toReal) =
          (∑' t, ‖ψ t‖ ^ (2 : ENNReal).toReal) := by
      change (∑' t, ‖ψ (σ t)‖ ^ (2 : ENNReal).toReal) =
        (∑' t, ‖ψ t‖ ^ (2 : ENNReal).toReal)
      exact σ.tsum_eq (fun t : Tile => ‖ψ t‖ ^ (2 : ENNReal).toReal)
    calc
      ‖φ‖ =
          (∑' t, ‖φ t‖ ^ (2 : ENNReal).toReal) ^
            (1 / (2 : ENNReal).toReal) :=
        lp.norm_eq_tsum_rpow hp φ
      _ = (∑' t, ‖ψ t‖ ^ (2 : ENNReal).toReal) ^
            (1 / (2 : ENNReal).toReal) := by rw [hsum]
      _ = ‖ψ‖ := (lp.norm_eq_tsum_rpow hp ψ).symm

@[expose] noncomputable def infiniteMatchingLaplacian (σ : Tile ≃ Tile) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  ContinuousLinearMap.id ℝ (TileHilbert Tile) -
    (infiniteTileReindex σ).toContinuousLinearMap

end

-- Source module: SpectralGeometry.InfiniteLocalBoundedDegree
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*} [DecidableEq Tile]

@[expose] noncomputable def infiniteLocalMatchingLaplacian (D : ℕ)
    (σ : Fin D → Tile ≃ Tile) (w : Fin D → ℝ) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  ∑ i : Fin D, w i • infiniteMatchingLaplacian (σ i)

end

-- Source module: SpectralGeometry.InfiniteLowEnergyObservation
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*} [DecidableEq Tile]

@[expose] def finiteSectorProjection (F : Finset Tile) :
    TileHilbert Tile →L[ℝ] TileHilbert Tile :=
  infiniteOnsiteDiagonalContraction (fun t => if t ∈ F then 1 else 0)
    (fun t => by split_ifs <;> norm_num)

@[expose] def onsitePlusBounded (V : Tile → ℝ) (B : TileHilbert Tile →L[ℝ] TileHilbert Tile) :
    infiniteOnsiteDomain V →ₗ[ℝ] TileHilbert Tile :=
  infiniteOnsiteOperator V + B.toLinearMap.comp (infiniteOnsiteDomain V).subtype

end

-- Source module: SpectralGeometry.InfiniteFiniteEdgeInteraction
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {Tile : Type*} [DecidableEq Tile]

@[expose] noncomputable def infiniteEdgeVector (a b : Tile) : TileHilbert Tile :=
  lp.single (2 : ENNReal) a (1 : ℝ) -
    lp.single (2 : ENNReal) b (1 : ℝ)

end

-- Source module: SpectralGeometry.DomainSpectralSubspace
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (d : Submodule ℝ H) (A : d →ₗ[ℝ] H)

@[expose] def domainEigenspace (ev : ℝ) : Submodule ℝ d :=
  LinearMap.ker (A - ev • d.subtype)

end

namespace AmmannBeenker

-- Source module: SpectralGeometry.AmmannBeenkerCutProject
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

abbrev Lattice := Fin 4 → ℤ

@[expose] def alpha : ℝ := Real.sqrt 2 / 2

@[expose] def physical (n : Lattice) : ℂ :=
  ⟨n 0 + alpha * (n 1 - n 3), n 2 + alpha * (n 1 + n 3)⟩

@[expose] def internal (n : Lattice) : ℂ :=
  ⟨n 0 - alpha * (n 1 - n 3), -(n 2 : ℝ) + alpha * (n 1 + n 3)⟩

@[expose] def Window (z : ℂ) : Prop :=
  |z.re| < 1 / 2 + alpha ∧ |z.im| < 1 / 2 + alpha ∧
    |z.re + z.im| < 1 + alpha ∧ |z.re - z.im| < 1 + alpha

@[expose] def Admitted (n : Lattice) : Prop := Window (internal n)

@[expose] def Vertex := {n : Lattice // Admitted n}

instance : DecidableEq Vertex := Classical.decEq _

@[expose] def position (v : Vertex) : ℂ := physical v.val

theorem admitted_zero : Admitted 0 := by
  sorry

@[expose] def origin : Vertex := ⟨0, admitted_zero⟩

@[expose] def basis (i : Fin 4) : Lattice := Pi.single i 1

end

-- Source module: SpectralGeometry.AmmannBeenkerGraph
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

abbrev Color := Fin 4 × Fin 2

@[expose] def latticeMate (c : Color) (n : Lattice) : Lattice :=
  n + if n c.1 % 2 = (c.2 : ℕ) then basis c.1 else -basis c.1

@[expose] def mate (c : Color) (v : Vertex) : Vertex :=
  by
    classical
    exact if h : Admitted (latticeMate c v.val) then ⟨latticeMate c v.val, h⟩ else v

theorem mate_involutive (c : Color) : Function.Involutive (mate c) := by
  sorry

@[expose] def matching (c : Color) : Vertex ≃ Vertex :=
  ⟨mate c, mate c, mate_involutive c, mate_involutive c⟩

@[expose] def neighbors (v : Vertex) : Finset Vertex :=
  (Finset.univ.image (fun c : Color => mate c v)).erase v

@[expose] def matching8 (i : Fin 8) : Vertex ≃ Vertex :=
  matching (finProdFinEquiv.symm i)

@[expose] def interaction : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  infiniteLocalMatchingLaplacian 8 matching8 (fun _ => 1 / 16)

end

-- Source module: SpectralGeometry.AmmannBeenkerOperator
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

@[expose] def potential (v : Vertex) : ℝ := 1 + ‖position v‖ ^ 2

end

-- Source module: SpectralGeometry.AmmannBeenkerCompactModes
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

open scoped Classical

@[expose] def latticeSingle (n : Lattice) : TileHilbert Vertex :=
  if h : Admitted n then lp.single (α := Vertex) (E := fun _ => ℝ) (2 : ENNReal) (⟨n, h⟩ : Vertex) 1 else 0

theorem latticeSingle_mem_domain (n : Lattice) :
    latticeSingle n ∈ infiniteOnsiteDomain potential := by
  unfold latticeSingle
  split_ifs
  · exact infiniteOnsiteDomain_single _ _ _
  · exact Submodule.zero_mem _

@[expose] def compactA : TileHilbert Vertex :=
  latticeSingle ![1, 0, 0, 0]
    - latticeSingle ![0, 1, 0, 0]
    + latticeSingle ![0, 0, 1, 0]
    - latticeSingle ![0, 0, 0, 1]
    + latticeSingle ![-1, 0, 0, 0]
    - latticeSingle ![0, -1, 0, 0]
    + latticeSingle ![0, 0, -1, 0]
    - latticeSingle ![0, 0, 0, -1]

@[expose] def compactB : TileHilbert Vertex :=
  latticeSingle ![1, 1, 0, 0]
    - latticeSingle ![0, 1, 1, 0]
    + latticeSingle ![0, 0, 1, 1]
    - latticeSingle ![-1, 0, 0, 1]
    + latticeSingle ![-1, -1, 0, 0]
    - latticeSingle ![0, -1, -1, 0]
    + latticeSingle ![0, 0, -1, -1]
    - latticeSingle ![1, 0, 0, -1]

theorem compactA_mem_domain : compactA ∈ infiniteOnsiteDomain potential := by
  sorry

theorem compactB_mem_domain : compactB ∈ infiniteOnsiteDomain potential := by
  sorry

end

-- Source module: SpectralGeometry.AmmannBeenkerCompactStates
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

open scoped Classical

@[expose] def latticeVertex (n : Lattice) (hn : Admitted n) : Vertex := ⟨n, hn⟩

@[expose] def domainLatticeSingle (n : Lattice) : infiniteOnsiteDomain potential :=
  ⟨latticeSingle n, latticeSingle_mem_domain n⟩

theorem compactSiteA_admitted : Admitted (![1, 0, 0, 0] : Lattice) := by
  sorry

theorem compactSiteB_admitted : Admitted (![1, 1, 0, 0] : Lattice) := by
  sorry

@[expose] def domainCompactA : infiniteOnsiteDomain potential :=
  ⟨compactA, compactA_mem_domain⟩

@[expose] def domainCompactB : infiniteOnsiteDomain potential :=
  ⟨compactB, compactB_mem_domain⟩

@[expose] def compactSiteA : Vertex :=
  latticeVertex ![1, 0, 0, 0] compactSiteA_admitted

@[expose] def compactSiteB : Vertex :=
  latticeVertex ![1, 1, 0, 0] compactSiteB_admitted

end

-- Source module: SpectralGeometry.AmmannBeenkerCompactCrossing
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

@[expose] def ringInteraction (t : ℝ) : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  interaction + t • finiteSectorProjection (neighbors origin)

@[expose] def crossingParameter : ℝ := 17 / 16 + 2 * alpha

@[expose] def crossingEnergy : ℝ := 13 / 4 + 2 * alpha

@[expose] def crossingEdge : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  InnerProductSpace.rankOne ℝ
    (infiniteEdgeVector compactSiteA compactSiteB)
    (infiniteEdgeVector compactSiteA compactSiteB)

@[expose] def crossingBright : TileHilbert Vertex :=
  (1 / 4 : ℝ) • (compactA - compactB)

end

-- Source module: SpectralGeometry.AmmannBeenkerEdgeControl
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

@[expose] def crossingDark : TileHilbert Vertex :=
  (1 / 4 : ℝ) • (compactA + compactB)

@[expose] def domainCrossingDark : infiniteOnsiteDomain potential :=
  (1 / 4 : ℝ) • (domainCompactA + domainCompactB)

end

-- Source module: SpectralGeometry.AmmannBeenkerQubitLeakage
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

@[expose] def crossingCoeffA (ψ : TileHilbert Vertex) : ℝ :=
  inner ℝ compactA ψ / 8

@[expose] def crossingCoeffB (ψ : TileHilbert Vertex) : ℝ :=
  inner ℝ compactB ψ / 8

@[expose] def crossingQubitPart (ψ : TileHilbert Vertex) : TileHilbert Vertex :=
  crossingCoeffA ψ • compactA + crossingCoeffB ψ • compactB

@[expose] def crossingLeakage (ψ : TileHilbert Vertex) : TileHilbert Vertex :=
  ψ - crossingQubitPart ψ

end

-- Source module: SpectralGeometry.AmmannBeenkerBrightSpectralSplitting
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

section

/-- The proposed scientific theorem: a small change to one edge of the
specified infinite octagonal graph preserves one simple localized energy
and produces one other simple nearby energy. The new energy moves in the
direction of the edge change, with an explicit quadratic error bound;
the true moving eigenvector has a nonzero bright part and a controlled
exterior component. All claims concern the original infinite operator
and its natural domain. The six other selected propositions are
necessary model witnesses, not separate scientific submissions. -/
theorem crossing_final_signed_bright_spectral_splitting
    (ε : ℝ) (hε : ε ≠ 0) (hsmall : |ε| ≤ 1 / 1024) :
    ∃ (energy : ℝ) (x : infiniteOnsiteDomain potential),
      energy ≠ crossingEnergy ∧
      |energy - crossingEnergy| ≤ 2 * |ε| ∧
      (x : TileHilbert Vertex) ≠ 0 ∧
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x =
        energy • (x : TileHilbert Vertex) ∧
      (0 < ε → crossingEnergy < energy) ∧
      (ε < 0 → energy < crossingEnergy) ∧
      |energy - (crossingEnergy + ε / 4)| ≤ 112 * ε ^ 2 ∧
      inner ℝ crossingDark (x : TileHilbert Vertex) = 0 ∧
      inner ℝ crossingBright (x : TileHilbert Vertex) ≠ 0 ∧
      crossingQubitPart (x : TileHilbert Vertex) =
        (inner ℝ crossingBright (x : TileHilbert Vertex)) • crossingBright ∧
      ‖crossingLeakage (x : TileHilbert Vertex)‖ ≤
        256 * |ε| *
          |inner ℝ crossingBright (x : TileHilbert Vertex)| *
          ‖crossingLeakage (crossingEdge crossingBright)‖ ∧
      (∀ (t : ℝ) (y : infiniteOnsiteDomain potential),
        (y : TileHilbert Vertex) ≠ 0 →
        onsitePlusBounded potential
            (ringInteraction crossingParameter + ε • crossingEdge) y =
          t • (y : TileHilbert Vertex) →
        |t - crossingEnergy| ≤ 1 / 256 →
        t = crossingEnergy ∨ t = energy) ∧
      (∀ y : infiniteOnsiteDomain potential,
        onsitePlusBounded potential
            (ringInteraction crossingParameter + ε • crossingEdge) y =
          energy • (y : TileHilbert Vertex) →
        ∃ c : ℝ, (y : TileHilbert Vertex) = c • (x : TileHilbert Vertex)) ∧
      (∀ y : infiniteOnsiteDomain potential,
        onsitePlusBounded potential
            (ringInteraction crossingParameter + ε • crossingEdge) y =
          crossingEnergy • (y : TileHilbert Vertex) →
        ∃ c : ℝ, (y : TileHilbert Vertex) = c • crossingDark) := by
  sorry

end

end AmmannBeenker
end
end SpectralGeometry
