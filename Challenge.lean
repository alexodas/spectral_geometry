module
public import Mathlib
public section
/-!
# Exact Double Eigenvalue and Spectral Isolation on an Infinite Ammann--Beenker Graph with a Bounded Plateau Potential
Standalone concrete graph, compact modes and bounded operators. Only selected propositions have proof placeholders.
-/
namespace SpectralGeometry
noncomputable section
@[expose] abbrev TileHilbert (Tile : Type*) : Type _ := lp (fun _ : Tile => ℝ) 2
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
theorem finite_norm_sublevel (R : ℝ) : {v : Vertex | ‖position v‖ ≤ R}.Finite := by
  sorry
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
@[expose] def sector : Finset Vertex := (finite_norm_sublevel 2).toFinset
end
-- Source module: SpectralGeometry.AmmannBeenkerCompactModes
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
section
open scoped Classical
@[expose] def latticeSingle (n : Lattice) : TileHilbert Vertex :=
  if h : Admitted n then lp.single (α := Vertex) (E := fun _ => ℝ) (2 : ENNReal) (⟨n, h⟩ : Vertex) 1 else 0
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
end
-- Source module: SpectralGeometry.AmmannBeenkerCompactCrossing
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
section
@[expose] def ringInteraction (t : ℝ) : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  interaction + t • finiteSectorProjection (neighbors origin)
@[expose] def crossingParameter : ℝ := 17 / 16 + 2 * alpha
@[expose] def crossingEnergy : ℝ := 13 / 4 + 2 * alpha
end
-- Source module: SpectralGeometry.AmmannBeenkerPlateauOperator
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
section
@[expose] def plateauPotential (C : ℝ) (v : Vertex) : ℝ := min (potential v) C
@[expose] def canonicalPlateauHeight : ℝ := 4 + 4 * alpha
theorem canonicalPlateauHeight_ge_five : 5 ≤ canonicalPlateauHeight := by
  sorry
theorem canonicalPlateauPotential_outside (v : Vertex) (hv : v ∉ sector) :
    plateauPotential canonicalPlateauHeight v = canonicalPlateauHeight := by
  sorry
theorem plateauPotential_normalized_norm_le (C : ℝ) (hC : 1 ≤ C)
    (v : Vertex) : ‖plateauPotential C v / C‖ ≤ 1 := by
  sorry
@[expose] def plateauOnsite (C : ℝ) (hC : 1 ≤ C) :
    TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  C • infiniteOnsiteDiagonalContraction
    (fun v => plateauPotential C v / C)
    (plateauPotential_normalized_norm_le C hC)
@[expose] def plateauHamiltonian (C : ℝ) (hC : 1 ≤ C) :
    TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  plateauOnsite C hC + ringInteraction crossingParameter
end
-- Source module: SpectralGeometry.AmmannBeenkerCentralPatch
section
theorem sector_card : sector.card = 17 := by
  sorry
end
-- Source module: SpectralGeometry.AmmannBeenkerCompactStates
section
theorem compactA_inner_self : inner ℝ compactA compactA = 8 := by
  sorry
theorem compactB_inner_self : inner ℝ compactB compactB = 8 := by
  sorry
theorem compactA_inner_compactB : inner ℝ compactA compactB = 0 := by
  sorry
end
-- Source module: SpectralGeometry.AmmannBeenkerPlateauSpectrum
section
theorem plateauHamiltonian_realSpectrum_gap (C : ℝ) (hC : 1 ≤ C)
    (hheight : canonicalPlateauHeight ≤ C) (energy : ℝ)
    (hspec : energy ∈ spectrum ℝ (plateauHamiltonian C hC))
    (hne : energy ≠ crossingEnergy) :
    (1 / 122 : ℝ) ≤ |energy - crossingEnergy| := by
  sorry
end
-- Source module: SpectralGeometry.AmmannBeenkerPlateauBulk
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
section
@[expose] def plateauBulk (C : ℝ) : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  C • ContinuousLinearMap.id ℝ (TileHilbert Vertex) + interaction
@[expose] def canonicalPlateauHamiltonian : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  plateauHamiltonian canonicalPlateauHeight
    (le_trans (by norm_num : (1 : ℝ) ≤ 5) canonicalPlateauHeight_ge_five)
@[expose] def canonicalPlateauDefect : TileHilbert Vertex →L[ℝ] TileHilbert Vertex :=
  canonicalPlateauHamiltonian - plateauBulk canonicalPlateauHeight
theorem canonicalPlateauDefect_zero_outside (x : TileHilbert Vertex)
    (v : Vertex) (hv : v ∉ sector) :
    canonicalPlateauDefect x v = 0 := by
  sorry
theorem canonicalPlateau_isolated_double_eigenvalue :
    IsSelfAdjoint canonicalPlateauHamiltonian ∧
    LinearIndependent ℝ ![compactA, compactB] ∧
    canonicalPlateauHamiltonian compactA = crossingEnergy • compactA ∧
    canonicalPlateauHamiltonian compactB = crossingEnergy • compactB ∧
    Module.finrank ℝ
      (Module.End.eigenspace canonicalPlateauHamiltonian.toLinearMap crossingEnergy) = 2 ∧
    (∀ energy ∈ spectrum ℝ canonicalPlateauHamiltonian,
      energy ≠ crossingEnergy → (1 / 122 : ℝ) ≤ |energy - crossingEnergy|) ∧
    crossingEnergy < canonicalPlateauHeight ∧
    spectrum ℝ (plateauBulk canonicalPlateauHeight) ⊆
      Set.Icc canonicalPlateauHeight (canonicalPlateauHeight + 1) ∧
    FiniteDimensional ℝ canonicalPlateauDefect.toLinearMap.range ∧
    Module.finrank ℝ canonicalPlateauDefect.toLinearMap.range ≤ 17 := by
  sorry
end
end AmmannBeenker
end
end SpectralGeometry
