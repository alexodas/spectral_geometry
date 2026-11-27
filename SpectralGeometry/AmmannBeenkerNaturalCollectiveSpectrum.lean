module

public import SpectralGeometry.AmmannBeenkerNaturalIsolationObstruction

public section

/-!
# Uniform spectral shifts and collective residual bounds

Uniform onsite energy is a scalar shift, not a source of spectral gaps.
The canonical plateau also has a central finite-rank defect, so the
uniform shift statement alone does not classify its other spectral
points. The other natural level bounds any collective residual gap
around either full eigenspace from above.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

/-- Full operator identity, including the bounded-inverse residual. -/
theorem plateauBulk_shifted_residual (C e : ℝ) :
    plateauBulk C - (C + e) • (1 : TileHilbert Vertex →L[ℝ] TileHilbert Vertex) =
      interaction - e • (1 : TileHilbert Vertex →L[ℝ] TileHilbert Vertex) := by
  apply ContinuousLinearMap.ext
  intro x
  change C • x + interaction x - (C + e) • x = interaction x - e • x
  module

/-- Exact translation of the real spectrum of the uniform bulk.
In particular, uniform height cannot open or close a spectral gap. -/
theorem plateauBulk_mem_realSpectrum_iff (C e : ℝ) :
    C + e ∈ spectrum ℝ (plateauBulk C) ↔ e ∈ spectrum ℝ interaction := by
  have h : C + e ∉ spectrum ℝ (plateauBulk C) ↔ e ∉ spectrum ℝ interaction := by
    simp only [spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one]
    have he := congrArg Neg.neg (plateauBulk_shifted_residual C e)
    rw [neg_sub, neg_sub] at he
    rw [he]
  simpa only [not_not] using not_congr h

/-- The shifted eigenvector equation is equivalent in both directions. -/
theorem plateauBulk_eigenvector_iff (C e : ℝ) (x : TileHilbert Vertex) :
    plateauBulk C x = (C + e) • x ↔ interaction x = e • x := by
  have h := congrArg (fun T : TileHilbert Vertex →L[ℝ] TileHilbert Vertex => T x)
    (plateauBulk_shifted_residual C e)
  change plateauBulk C x - (C + e) • x = interaction x - e • x at h
  constructor
  · intro he
    rw [he, sub_self] at h
    exact sub_eq_zero.mp h.symm
  · intro he
    rw [he, sub_self] at h
    exact sub_eq_zero.mp h

/-- Even for infinite-dimensional eigenspaces, self-adjointness makes
eigenvectors at distinct real energies mutually orthogonal. -/
theorem natural_distinct_eigenvectors_orthogonal
    (T : TileHilbert Vertex →L[ℝ] TileHilbert Vertex) (hT : IsSelfAdjoint T)
    (e f : ℝ) (hne : e ≠ f) (x y : TileHilbert Vertex)
    (hx : T x = e • x) (hy : T y = f • y) :
    inner ℝ x y = 0 := by
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) x y
  rw [hx, hy, real_inner_smul_left, real_inner_smul_right] at hs
  have hp : (e - f) * inner ℝ x y = 0 := by linarith only [hs]
  exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hne)

/-- A collective residual gap is a lower bound on the orthogonal
complement of the entire eigenspace, rather than a selected cell. -/
@[expose] def naturalCollectiveResidualBound
    (T : TileHilbert Vertex →L[ℝ] TileHilbert Vertex) (e g : ℝ) : Prop :=
  ∀ x : TileHilbert Vertex,
    (∀ y : TileHilbert Vertex, T y = e • y → inner ℝ y x = 0) →
    g * ‖x‖ ≤ ‖T x - e • x‖

/-- Uniform bulk and Laplacian have identical collective residual bounds. -/
theorem plateauBulk_collectiveResidualBound_iff (C e g : ℝ) :
    naturalCollectiveResidualBound (plateauBulk C) (C + e) g ↔
      naturalCollectiveResidualBound interaction e g := by
  unfold naturalCollectiveResidualBound
  have h (x : TileHilbert Vertex) :
      plateauBulk C x - (C + e) • x = interaction x - e • x := by
    exact congrArg (fun T : TileHilbert Vertex →L[ℝ] TileHilbert Vertex => T x)
      (plateauBulk_shifted_residual C e)
  simp only [plateauBulk_eigenvector_iff C e, h]

/-- The existence of a different nonzero eigenvector bounds any collective
residual lower bound by the distance between the two energies. -/
theorem naturalCollectiveResidualBound_le_of_other_eigenvector
    (T : TileHilbert Vertex →L[ℝ] TileHilbert Vertex) (hT : IsSelfAdjoint T)
    (e f g : ℝ) (hne : e ≠ f) (x : TileHilbert Vertex)
    (hx : T x = f • x) (hn : x ≠ 0)
    (hg : naturalCollectiveResidualBound T e g) : g ≤ |f - e| := by
  have hb := hg x (fun y hy =>
    natural_distinct_eigenvectors_orthogonal T hT e f hne y x hy hx)
  rw [hx, ← sub_smul, norm_smul, Real.norm_eq_abs] at hb
  exact (mul_le_mul_right (norm_pos_iff.mpr hn)).mp hb

/-- At either natural level, any collective gap of the canonical plateau
is at most the splitting 1/16. This is not a positive lower bound. -/
theorem canonicalPlateau_collectiveResidualBound_le (e g : ℝ)
    (he : e = canonicalPlateauHeight + 3 / 16 ∨
      e = canonicalPlateauHeight + 1 / 4)
    (hg : naturalCollectiveResidualBound canonicalPlateauHamiltonian e g) :
    g ≤ 1 / 16 := by
  obtain ⟨w, hw, hrec⟩ := finite_pattern_recurrence centralRecurrenceLifts 4
  obtain ⟨ha, hb⟩ := naturalPlateauPair_eigenvectors w hw hrec
  obtain ⟨hna, hnb, _⟩ := translatedCompact_inner_products w.val hrec
  have hT := canonicalPlateau_isolated_double_eigenvalue.1
  have hA : translatedCompactA w.val ≠ 0 := by
    intro hz
    rw [hz, inner_zero_left] at hna
    norm_num at hna
  have hB : translatedCompactB w.val ≠ 0 := by
    intro hz
    rw [hz, inner_zero_left] at hnb
    norm_num at hnb
  rcases he with rfl | rfl
  · have h := naturalCollectiveResidualBound_le_of_other_eigenvector
      canonicalPlateauHamiltonian hT _ _ g (by linarith) _ hb hB hg
    rw [show canonicalPlateauHeight + 1 / 4 -
      (canonicalPlateauHeight + 3 / 16) = (1 / 16 : ℝ) by ring,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16)] at h
    exact h
  · have h := naturalCollectiveResidualBound_le_of_other_eigenvector
      canonicalPlateauHamiltonian hT _ _ g (by linarith) _ ha hA hg
    rw [show canonicalPlateauHeight + 3 / 16 -
      (canonicalPlateauHeight + 1 / 4) = -(1 / 16 : ℝ) by ring,
      abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16)] at h
    exact h

end
end SpectralGeometry.AmmannBeenker
