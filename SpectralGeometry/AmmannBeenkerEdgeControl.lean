module

public import SpectralGeometry.AmmannBeenkerCompactCrossing

public section

/-!
# Exact compact-mode coupling under a single-edge perturbation

The edge joining the two compact rings has a nonzero off-diagonal
matrix element between the two localized modes. On their two-dimensional
span its quadratic form depends only on the difference of the amplitudes.
The equal-amplitude ("dark") mode is invisible to the edge.

These are algebraic statements for the real infinite-graph Hilbert space,
not quantum time-evolution or state-preparation theorems. In particular,
the single-edge perturbation need not preserve the two-mode subspace.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- The selected edge couples the two compact modes: the off-diagonal
matrix element is nonzero. -/
theorem crossingEdge_compactA_compactB :
    inner ℝ compactA (crossingEdge compactB) = -1 := by
  rw [crossingEdge_inner]
  norm_num only [compactB_siteA, compactB_siteB, compactA_siteA, compactA_siteB]

/-- Exact two-mode compression of the single-edge quadratic form. No
invariance of the two-mode subspace under the full edge operator is assumed. -/
theorem crossingEdge_two_mode_form (r s u v : ℝ) :
    inner ℝ (r • compactA + s • compactB)
      (crossingEdge (u • compactA + v • compactB)) =
        (r - s) * (u - v) := by
  rw [crossingEdge_inner]
  change
    (u * compactA compactSiteA + v * compactB compactSiteA -
      (u * compactA compactSiteB + v * compactB compactSiteB)) *
    (r * compactA compactSiteA + s * compactB compactSiteA -
      (r * compactA compactSiteB + s * compactB compactSiteB)) =
      (r - s) * (u - v)
  simp only [compactA_siteA, compactB_siteA, compactA_siteB, compactB_siteB]
  ring

/-- A normalized equal-amplitude combination of the compact modes. -/
@[expose] def crossingDark : TileHilbert Vertex :=
  (1 / 4 : ℝ) • (compactA + compactB)

theorem crossingDark_norm_sq : ‖crossingDark‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq]
  have hba : inner ℝ compactB compactA = 0 := by
    rw [real_inner_comm, compactA_inner_compactB]
  simp only [crossingDark, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_add_right, compactA_inner_self, compactB_inner_self,
    compactA_inner_compactB, hba]
  norm_num

/-- The dark mode has zero matrix element with the edge perturbation
against *every* state, including states outside the compact-mode plane. -/
theorem crossingDark_edge_inner_zero (x : TileHilbert Vertex) :
    inner ℝ crossingDark (crossingEdge x) = 0 := by
  rw [crossingEdge_inner]
  have hd : crossingDark compactSiteA - crossingDark compactSiteB = 0 := by
    change (1 / 4 : ℝ) * (compactA compactSiteA + compactB compactSiteA) -
      (1 / 4 : ℝ) * (compactA compactSiteB + compactB compactSiteB) = 0
    simp only [compactA_siteA, compactB_siteA, compactA_siteB, compactB_siteB]
    norm_num
  rw [hd, mul_zero]

/-- The initial unnormalized first-ring mode has a fixed nonzero
overlap with the normalized dark direction. -/
theorem crossingDark_inner_compactA :
    inner ℝ crossingDark compactA = 2 := by
  have hba : inner ℝ compactB compactA = 0 := by
    rw [real_inner_comm, compactA_inner_compactB]
  simp only [crossingDark, real_inner_smul_left, inner_add_left,
    compactA_inner_self, hba]
  norm_num

/-- The other compact mode has the same overlap with the dark state. -/
theorem crossingDark_inner_compactB :
    inner ℝ crossingDark compactB = 2 := by
  simp only [crossingDark, real_inner_smul_left, inner_add_left,
    compactA_inner_compactB, compactB_inner_self]
  norm_num


/-- The edge acts trivially on the normalized dark state, not merely
after compression to the two-dimensional compact-mode space. -/
theorem crossingEdge_dark_zero : crossingEdge crossingDark = 0 := by
  simp only [crossingDark, map_smul, crossingEdge_dark, smul_zero]

/-- The dark vector belongs to the original natural onsite domain. -/
@[expose] def domainCrossingDark : infiniteOnsiteDomain potential :=
  (1 / 4 : ℝ) • (domainCompactA + domainCompactB)

/-- The normalized dark state is a genuine infinite-domain eigenstate
for every real edge perturbation. This upgrades the prior unnormalized
`crossing_dark_eigenvector` and is *not* a two-mode approximation. -/
theorem crossingDark_full_eigenvector (ε : ℝ) :
    onsitePlusBounded potential (ringInteraction crossingParameter + ε • crossingEdge)
      domainCrossingDark = crossingEnergy • crossingDark := by
  simp only [domainCrossingDark, map_smul, crossing_dark_eigenvector, crossingDark]
  module

/-- The exact edge energy of any combination of the two compact modes
depends only on their amplitude difference. -/
theorem crossingEdge_two_mode_energy (r s : ℝ) :
    inner ℝ (r • compactA + s • compactB)
      (crossingEdge (r • compactA + s • compactB)) =
      (r - s) ^ 2 := by
  rw [crossingEdge_two_mode_form]
  ring

/-- The edge quadratic form is nonnegative on the compact-mode plane. -/
theorem crossingEdge_two_mode_nonneg (r s : ℝ) :
    0 ≤ inner ℝ (r • compactA + s • compactB)
      (crossingEdge (r • compactA + s • compactB)) := by
  rw [crossingEdge_two_mode_energy]
  exact sq_nonneg _

end
end SpectralGeometry.AmmannBeenker
