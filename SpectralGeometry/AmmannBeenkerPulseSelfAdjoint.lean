module

public import SpectralGeometry.AmmannBeenkerPulseIntertwining
public import SpectralGeometry.InfiniteLocalSelfAdjointPMap
public import SpectralGeometry.InfiniteBoundedSpectralStability

public section

/-!
# Self-adjointness of the selected-edge pulse Hamiltonian

The selected edge is the actual graph edge between the two
Ammann–Beenker compact rings. The full real onsite-plus-interaction
operator, with any real strength ε on this edge, is an unbounded
self-adjoint operator on the original natural onsite domain.

This is not a finite-volume Hamiltonian and does not assume
boundedness of the onsite potential. The proof specializes the
existing self-adjoint LinearPMap theorem to an empty matching
family, with the complete bounded ring-plus-edge correction.

This result is a concrete analytic prerequisite for a physical
complex Schrödinger group; the complexification and Stone
functional calculus have NOT yet been formalized here.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- The unbounded real Hamiltonian during a fixed pulse,
as a Mathlib partial linear operator. Empty matching colors
mean all bounded interactions are included in the correction,
with no finite-volume truncation. -/
@[expose] noncomputable def crossingEdgePulsePMap (ε : ℝ) :
    TileHilbert Vertex →ₗ.[ℝ] TileHilbert Vertex :=
  infiniteLocalShiftedPerturbedPMap 0 potential
    (fun i : Fin 0 => Fin.elim0 i) (fun _ => 0)
    (ringInteraction crossingParameter + ε • crossingEdge) 1 0

/-- The full pulse Hamiltonian has exactly the original natural
onsite domain, regardless of edge strength. -/
theorem crossingEdgePulsePMap_domain (ε : ℝ) :
    (crossingEdgePulsePMap ε).domain = infiniteOnsiteDomain potential := rfl

/-- The Mathlib partial operator has precisely the graph
Hamiltonian action used in our eigenvector and leakage results. -/
theorem crossingEdgePulsePMap_apply (ε : ℝ)
    (x : infiniteOnsiteDomain potential) :
    crossingEdgePulsePMap ε x =
      onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge) x := by
  let σ : Fin 0 → Vertex ≃ Vertex := fun i => Fin.elim0 i
  let w : Fin 0 → ℝ := fun _ => 0
  let B := ringInteraction crossingParameter + ε • crossingEdge
  have hzero : infiniteLocalBoundedCorrection 0 σ w B 1 0 = B :=
    zeroMatching_correction B
  have hoperator :
      infiniteLocalShiftedPerturbedOperator 0 potential σ w B 1 0 =
        onsitePlusBounded potential B := by
    have h := (onsitePlusBounded_eq_local 0 potential σ w B 1 0).symm
    simpa only [hzero] using h
  change infiniteLocalShiftedPerturbedOperator 0 potential σ w B 1 0 x =
    onsitePlusBounded potential B x
  rw [hoperator]

/-- The selected rank-one edge correction is symmetric on the
*full* infinite Hilbert space. -/
theorem crossingEdge_symmetric_full :
    ∀ x y : TileHilbert Vertex,
      inner ℝ (crossingEdge x) y = inner ℝ x (crossingEdge y) := by
  intro x y
  rw [real_inner_comm y (crossingEdge x), crossingEdge_inner,
    crossingEdge_inner]
  ring

/-- The complete bounded pulse correction is symmetric for
every real ε; a negative pulse strength is also allowed. -/
theorem crossingEdgePulseCorrection_symmetric (ε : ℝ) :
    ∀ x y : TileHilbert Vertex,
      inner ℝ
        ((ringInteraction crossingParameter + ε • crossingEdge) x) y =
      inner ℝ x
        ((ringInteraction crossingParameter + ε • crossingEdge) y) := by
  have hring :
      ∀ x y : TileHilbert Vertex,
        inner ℝ ((ringInteraction crossingParameter) x) y =
          inner ℝ x ((ringInteraction crossingParameter) y) := by
    simpa only [ringInteraction] using
      (finiteSectorCorrection_symmetric interaction interaction_symmetric
        (neighbors origin) crossingParameter)
  have hedge :
      ∀ x y : TileHilbert Vertex,
        inner ℝ ((ε • crossingEdge) x) y =
          inner ℝ x ((ε • crossingEdge) y) := by
    intro x y
    simp only [smul_apply,
      real_inner_smul_left, real_inner_smul_right]
    rw [crossingEdge_symmetric_full x y]
  exact boundedCorrection_add_symmetric
    (ringInteraction crossingParameter) (ε • crossingEdge) hring hedge

/-- The exact infinite-graph pulse Hamiltonian is an
unbounded **self-adjoint real** operator on the original
natural domain, for EVERY real strength ε of the chosen edge. -/
theorem crossingEdgePulsePMap_isSelfAdjoint (ε : ℝ) :
    IsSelfAdjoint (crossingEdgePulsePMap ε) := by
  change IsSelfAdjoint
    (infiniteLocalShiftedPerturbedPMap 0 potential
      (fun i : Fin 0 => Fin.elim0 i) (fun _ => 0)
      (ringInteraction crossingParameter + ε • crossingEdge) 1 0)
  apply infiniteLocalShiftedPerturbedPMap_isSelfAdjoint
  · intro i t
    exact Fin.elim0 i
  · intro x y
    exact (crossingEdgePulseCorrection_symmetric ε x y).symm

end
end SpectralGeometry.AmmannBeenker
