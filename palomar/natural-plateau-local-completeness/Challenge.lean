module
public import Mathlib
public section
/-!
# Exact local completeness and infinite global multiplicity of compact eigenstates
The same concrete Ammann–Beenker graph and canonical bounded plateau as the earlier results.
The statements classify eigenvectors supported in each seventeen-site remote recurrent cell, establish infinite-dimensional global eigenspaces, and rule out individual residual gaps. All model definitions are concrete; theorem holes are independently compared with Solution.
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
end
-- Source module: SpectralGeometry.AmmannBeenkerCompactStates
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
section
open scoped Classical
@[expose] def latticeVertex (n : Lattice) (hn : Admitted n) : Vertex := ⟨n, hn⟩
end
-- Source module: SpectralGeometry.AmmannBeenkerCentralPatch
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
section
@[expose] def centralLift (i : Fin 17) : Lattice :=
  ![![0, 0, 0, 0],
    ![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1],
    ![-1, 0, 0, 0],
    ![0, -1, 0, 0],
    ![0, 0, -1, 0],
    ![0, 0, 0, -1],
    ![1, 1, 0, 0],
    ![0, 1, 1, 0],
    ![0, 0, 1, 1],
    ![-1, 0, 0, 1],
    ![-1, -1, 0, 0],
    ![0, -1, -1, 0],
    ![0, 0, -1, -1],
    ![1, 0, 0, -1]] i
theorem centralLift_admitted (i : Fin 17) : Admitted (centralLift i) := by
  sorry
@[expose] def centralLifts : Finset Lattice := Finset.univ.image centralLift
@[expose] def centralVertex (i : Fin 17) : Vertex :=
  latticeVertex (centralLift i) (centralLift_admitted i)
@[expose] def centralPatch : Finset Vertex := Finset.univ.image centralVertex
theorem centralPatch_card : centralPatch.card = 17 := by
  sorry
end
-- Source module: SpectralGeometry.AmmannBeenkerPatchNeighborhood
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
section
@[expose] def patchNeighborhoodLifts (F : Finset Lattice) : Finset Lattice := by
  classical
  exact F ∪ F.biUnion (fun n =>
    (Finset.univ.image (fun i : Fin 4 => n + basis i)) ∪
    (Finset.univ.image (fun i : Fin 4 => n - basis i)))
@[expose] def centralRecurrenceLifts : Finset Lattice :=
  patchNeighborhoodLifts (patchNeighborhoodLifts centralLifts)
end
-- Source module: SpectralGeometry.AmmannBeenkerTranslatedModes
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
section
open scoped Classical
@[expose] def patchTranslateVertex (t : Lattice) (v : Vertex) : Vertex :=
  if h : Admitted (v.val + t) then ⟨v.val + t, h⟩ else v
@[expose] def translateFiniteState (F : Finset Vertex) (t : Lattice)
    (x : TileHilbert Vertex) : TileHilbert Vertex :=
  ∑ v ∈ F, x v • latticeSingle (v.val + t)
@[expose] def translatedCompactA (t : Lattice) : TileHilbert Vertex :=
  translateFiniteState centralPatch t compactA
@[expose] def translatedCompactB (t : Lattice) : TileHilbert Vertex :=
  translateFiniteState centralPatch t compactB
theorem translatedCompactA_eigenvector (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) :
    interaction (translatedCompactA t) = (3 / 16 : ℝ) • translatedCompactA t := by
  sorry
theorem translatedCompactB_eigenvector (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) :
    interaction (translatedCompactB t) = (1 / 4 : ℝ) • translatedCompactB t := by
  sorry
end

-- Source module: SpectralGeometry.AmmannBeenkerNaturalPlateauPairs
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
section
open scoped Classical
theorem canonicalPlateau_eq_bulk_of_exterior_support
    (x : TileHilbert Vertex) (hx : ∀ v ∈ sector, x v = 0) :
    canonicalPlateauHamiltonian x = plateauBulk canonicalPlateauHeight x := by
  sorry
theorem naturalPlateauPair_eigenvectors (v : Vertex)
    (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n) :
    canonicalPlateauHamiltonian (translatedCompactA v.val) =
      (canonicalPlateauHeight + 3 / 16) • translatedCompactA v.val ∧
    canonicalPlateauHamiltonian (translatedCompactB v.val) =
      (canonicalPlateauHeight + 1 / 4) • translatedCompactB v.val := by
  sorry
theorem exact_recurrent_natural_plateau_pairs (R D : ℝ) (hD : 0 ≤ D) (N : ℕ) :
    ∃ S : Finset Vertex, S.card = N ∧
      (∀ v ∈ S, R < ‖position v‖ ∧ 4 < ‖position v‖ ∧
        (∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n) ∧
        canonicalPlateauHamiltonian (translatedCompactA v.val) =
          (canonicalPlateauHeight + 3 / 16) • translatedCompactA v.val ∧
        canonicalPlateauHamiltonian (translatedCompactB v.val) =
          (canonicalPlateauHeight + 1 / 4) • translatedCompactB v.val ∧
        inner ℝ (translatedCompactA v.val) (translatedCompactA v.val) = 8 ∧
        inner ℝ (translatedCompactB v.val) (translatedCompactB v.val) = 8 ∧
        inner ℝ (translatedCompactA v.val) (translatedCompactB v.val) = 0) ∧
      (∀ v ∈ S, ∀ w ∈ S, v ≠ w →
        D < dist (position v) (position w) ∧
        (∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
          n + v.val ≠ m + w.val) ∧
        inner ℝ (translatedCompactA v.val) (translatedCompactA w.val) = 0 ∧
        inner ℝ (translatedCompactA v.val) (translatedCompactB w.val) = 0 ∧
        inner ℝ (translatedCompactB v.val) (translatedCompactA w.val) = 0 ∧
        inner ℝ (translatedCompactB v.val) (translatedCompactB w.val) = 0) := by
  sorry
end

-- Source module: SpectralGeometry.AmmannBeenkerNaturalCellCompleteness
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
section
open scoped Classical
theorem naturalCell_supported_eigenvector_classification
    (x : TileHilbert Vertex) (hx : ∀ v : Vertex, v ∉ sector → x v = 0)
    (c : ℝ) (he : interaction x = c • x) (hn : x ≠ 0) :
    (c = 3 / 16 ∧ ∃ a : ℝ, a ≠ 0 ∧ x = a • compactA) ∨
      (c = 1 / 4 ∧ ∃ b : ℝ, b ≠ 0 ∧ x = b • compactB) := by
  sorry
end

-- Source module: SpectralGeometry.AmmannBeenkerNaturalRemoteCompleteness
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
section
open scoped Classical
@[expose] def naturalRemoteCell (t : Lattice) : Finset Vertex :=
  centralPatch.image (patchTranslateVertex t)
theorem naturalRemoteCell_card (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) :
    (naturalRemoteCell t).card = 17 := by
  sorry
theorem naturalRemoteCell_plateau_classification (v : Vertex)
    (hr : 4 < ‖position v‖)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (x : TileHilbert Vertex)
    (hx : ∀ w : Vertex, w ∉ naturalRemoteCell v.val → x w = 0)
    (e : ℝ) (he : canonicalPlateauHamiltonian x = e • x) (hn : x ≠ 0) :
    (e = canonicalPlateauHeight + 3 / 16 ∧
      ∃ a : ℝ, a ≠ 0 ∧ x = a • translatedCompactA v.val) ∨
    (e = canonicalPlateauHeight + 1 / 4 ∧
      ∃ b : ℝ, b ≠ 0 ∧ x = b • translatedCompactB v.val) := by
  sorry
end

-- Source module: SpectralGeometry.AmmannBeenkerNaturalMultiplicity
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
section
open scoped Classical
theorem canonicalPlateau_natural_eigenspaces_infinite :
    (¬ FiniteDimensional ℝ (Module.End.eigenspace canonicalPlateauHamiltonian.toLinearMap
      (canonicalPlateauHeight + 3 / 16))) ∧
    (¬ FiniteDimensional ℝ (Module.End.eigenspace canonicalPlateauHamiltonian.toLinearMap
      (canonicalPlateauHeight + 1 / 4))) := by
  sorry
theorem plateauBulk_natural_eigenspaces_infinite (C : ℝ) :
    (¬ FiniteDimensional ℝ (Module.End.eigenspace (plateauBulk C).toLinearMap
      (C + 3 / 16))) ∧
    (¬ FiniteDimensional ℝ (Module.End.eigenspace (plateauBulk C).toLinearMap
      (C + 1 / 4))) := by
  sorry
end

-- Source module: SpectralGeometry.AmmannBeenkerNaturalIsolationObstruction
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
section
open scoped Classical
theorem naturalPlateauPair_orthogonal_partners (v : Vertex)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (R D : ℝ) (hD : 0 ≤ D) :
    ∃ w : Vertex, R < ‖position w‖ ∧ 4 < ‖position w‖ ∧
      D < dist (position v) (position w) ∧
      (∀ n ∈ centralRecurrenceLifts, Admitted (n + w.val) ↔ Admitted n) ∧
      (∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
        n + v.val ≠ m + w.val) ∧
      canonicalPlateauHamiltonian (translatedCompactA w.val) =
        (canonicalPlateauHeight + 3 / 16) • translatedCompactA w.val ∧
      canonicalPlateauHamiltonian (translatedCompactB w.val) =
        (canonicalPlateauHeight + 1 / 4) • translatedCompactB w.val ∧
      inner ℝ (translatedCompactA w.val) (translatedCompactA w.val) = 8 ∧
      inner ℝ (translatedCompactB w.val) (translatedCompactB w.val) = 8 ∧
      inner ℝ (translatedCompactA v.val) (translatedCompactA w.val) = 0 ∧
      inner ℝ (translatedCompactA v.val) (translatedCompactB w.val) = 0 ∧
      inner ℝ (translatedCompactB v.val) (translatedCompactA w.val) = 0 ∧
      inner ℝ (translatedCompactB v.val) (translatedCompactB w.val) = 0 := by
  sorry
theorem naturalPlateauPair_no_individual_residual_gap (v : Vertex)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (e g : ℝ) (he : e = canonicalPlateauHeight + 3 / 16 ∨
      e = canonicalPlateauHeight + 1 / 4) (hg : 0 < g) :
    ¬ (∀ x : TileHilbert Vertex,
      inner ℝ (translatedCompactA v.val) x = 0 →
      inner ℝ (translatedCompactB v.val) x = 0 →
      g * ‖x‖ ≤ ‖canonicalPlateauHamiltonian x - e • x‖) := by
  sorry
end

-- Source module: SpectralGeometry.AmmannBeenkerNaturalCollectiveSpectrum
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
section
open scoped Classical
@[expose] def naturalCollectiveResidualBound
    (T : TileHilbert Vertex →L[ℝ] TileHilbert Vertex) (e g : ℝ) : Prop :=
  ∀ x : TileHilbert Vertex,
    (∀ y : TileHilbert Vertex, T y = e • y → inner ℝ y x = 0) →
    g * ‖x‖ ≤ ‖T x - e • x‖
theorem plateauBulk_collectiveResidualBound_iff (C e g : ℝ) :
    naturalCollectiveResidualBound (plateauBulk C) (C + e) g ↔
      naturalCollectiveResidualBound interaction e g := by
  sorry
theorem canonicalPlateau_collectiveResidualBound_le (e g : ℝ)
    (he : e = canonicalPlateauHeight + 3 / 16 ∨
      e = canonicalPlateauHeight + 1 / 4)
    (hg : naturalCollectiveResidualBound canonicalPlateauHamiltonian e g) :
    g ≤ 1 / 16 := by
  sorry
end

-- Source module: SpectralGeometry.AmmannBeenkerNaturalDefectComparison
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
section
open scoped Classical
theorem canonicalPlateau_eigenspace_bound_outside_bulk (e : ℝ)
    (he : e ∉ spectrum ℝ (plateauBulk canonicalPlateauHeight)) :
    FiniteDimensional ℝ (Module.End.eigenspace canonicalPlateauHamiltonian.toLinearMap e) ∧
      Module.finrank ℝ (Module.End.eigenspace canonicalPlateauHamiltonian.toLinearMap e) ≤ 17 := by
  sorry
end
end AmmannBeenker
end
end SpectralGeometry
