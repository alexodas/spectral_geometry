module
public import Mathlib
public section
/-!
# Exact Recurrence and Spatial Replication of Compact Localized Eigenstates on an Infinite Ammann--Beenker Graph
Standalone concrete graph, finite lift neighborhoods and replicated compact modes.
Only selected propositions have proof placeholders.
-/
namespace SpectralGeometry
noncomputable section
@[expose] abbrev TileHilbert (Tile : Type*) : Type _ := lp (fun _ : Tile => ℝ) 2
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
theorem interaction_apply (f : TileHilbert Vertex) (v : Vertex) :
    interaction f v = (1 / 16 : ℝ) * ∑ w ∈ neighbors v, (f v - f w) := by
  sorry
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
-- Source module: SpectralGeometry.AmmannBeenkerPatchRecurrence
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
section
theorem internal_window_boundary_avoided (n : Lattice) :
    |(internal n).re| ≠ 1 / 2 + alpha ∧
      |(internal n).im| ≠ 1 / 2 + alpha ∧
      |(internal n).re + (internal n).im| ≠ 1 + alpha ∧
      |(internal n).re - (internal n).im| ≠ 1 + alpha := by
  sorry
theorem finite_pattern_recurrence (F : Finset Lattice) (R : ℝ) :
    ∃ v : Vertex, R < ‖position v‖ ∧
      ∀ n ∈ F, Admitted (n + v.val) ↔ Admitted n := by
  sorry
theorem finite_pattern_disjoint_copies (F : Finset Lattice) (R D : ℝ)
    (hD : 0 ≤ D) (N : ℕ) :
    ∃ S : Finset Vertex, S.card = N ∧
      (∀ v ∈ S, R < ‖position v‖ ∧
        ∀ n ∈ F, Admitted (n + v.val) ↔ Admitted n) ∧
      (∀ v ∈ S, ∀ w ∈ S, v ≠ w →
        D < dist (position v) (position w) ∧
          ∀ n ∈ F, ∀ m ∈ F, n + v.val ≠ m + w.val) := by
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
theorem central_recurrence_neighbors_exact (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (v v' : Vertex) (hv : v.val ∈ patchNeighborhoodLifts centralLifts)
    (hv' : v'.val = v.val + t) (w' : Vertex) :
    w' ∈ neighbors v' ↔ ∃ w ∈ neighbors v, w'.val = w.val + t := by
  sorry
theorem central_recurrence_disjoint_copies (R D : ℝ) (hD : 0 ≤ D) (N : ℕ) :
    ∃ S : Finset Vertex, S.card = N ∧
      (∀ v ∈ S, R < ‖position v‖ ∧
        ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n) ∧
      (∀ v ∈ S, ∀ w ∈ S, v ≠ w →
        D < dist (position v) (position w) ∧
          ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
            n + v.val ≠ m + w.val) := by
  sorry
end
-- Source module: SpectralGeometry.AmmannBeenkerTranslatedModes
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
section
open scoped Classical
@[expose] def translateFiniteState (F : Finset Vertex) (t : Lattice)
    (x : TileHilbert Vertex) : TileHilbert Vertex :=
  ∑ v ∈ F, x v • latticeSingle (v.val + t)
theorem central_translate_eigenvector (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n)
    (x : TileHilbert Vertex) (hx : ∀ v : Vertex, v ∉ centralPatch → x v = 0)
    (c : ℝ) (heig : interaction x = c • x) :
    interaction (translateFiniteState centralPatch t x) =
      c • translateFiniteState centralPatch t x := by
  sorry
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
-- Source module: SpectralGeometry.AmmannBeenkerReplicatedPairs
section
theorem translatedCompact_inner_products (t : Lattice)
    (hrec : ∀ n ∈ centralRecurrenceLifts, Admitted (n + t) ↔ Admitted n) :
    inner ℝ (translatedCompactA t) (translatedCompactA t) = 8 ∧
    inner ℝ (translatedCompactB t) (translatedCompactB t) = 8 ∧
    inner ℝ (translatedCompactA t) (translatedCompactB t) = 0 := by
  sorry
theorem central_translate_support (t : Lattice) (x : TileHilbert Vertex)
    (w : Vertex) (hw : translateFiniteState centralPatch t x w ≠ 0) :
    ∃ n ∈ centralLifts, w.val = n + t := by
  sorry
theorem exact_recurrent_compact_mode_pairs (R D : ℝ) (hD : 0 ≤ D) (N : ℕ) :
    ∃ S : Finset Vertex, S.card = N ∧
      (∀ v ∈ S, R < ‖position v‖ ∧
        (∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n) ∧
        interaction (translatedCompactA v.val) = (3 / 16 : ℝ) • translatedCompactA v.val ∧
        interaction (translatedCompactB v.val) = (1 / 4 : ℝ) • translatedCompactB v.val ∧
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
end AmmannBeenker
end
end SpectralGeometry
