module

public import SpectralGeometry.AmmannBeenkerNaturalCollectiveSpectrum

public section

/-!
# Eigenspace comparison for the finite central defect

Outside the real spectrum of the uniform bulk, a plateau eigenvector
is determined injectively by its image under the finite-rank defect.
This bounds the full eigenspace dimension by seventeen. The converse
comparison uses the same defect, without introducing any additional
potential. These results do not assert equality of essential spectra
or exclude additional spectral energies inside the bulk enclosure.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

/-- Apply the defect to a vector in an arbitrary eigenspace. -/
@[expose] def naturalEigenspaceDefectMap
    (T D : TileHilbert Vertex →L[ℝ] TileHilbert Vertex) (e : ℝ) :
    Module.End.eigenspace T.toLinearMap e →ₗ[ℝ] D.toLinearMap.range where
  toFun x := ⟨D x.val, ⟨x.val, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    change D (x.val + y.val) = D x.val + D y.val
    exact map_add D _ _
  map_smul' a x := by
    apply Subtype.ext
    change D (a • x.val) = a • D x.val
    exact map_smul D _ _

/-- A real resolvent energy makes the shifted bounded operator injective. -/
theorem natural_resolvent_injective
    (T : TileHilbert Vertex →L[ℝ] TileHilbert Vertex) (e : ℝ)
    (he : e ∉ spectrum ℝ T) :
    Function.Injective (fun x : TileHilbert Vertex => e • x - T x) := by
  have hu := spectrum.notMem_iff.mp he
  rw [Algebra.algebraMap_eq_smul_one] at hu
  have hi := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
  exact hi

/-- If the comparison operator has a bounded inverse at e, the image
under the perturbation determines every eigenvector at e. -/
theorem naturalEigenspaceDefectMap_injective
    (T U D : TileHilbert Vertex →L[ℝ] TileHilbert Vertex) (e : ℝ)
    (h : ∀ x : TileHilbert Vertex, T x = U x + D x)
    (he : e ∉ spectrum ℝ U) :
    Function.Injective (naturalEigenspaceDefectMap T D e) := by
  intro x y hxy
  have hd : D x.val = D y.val :=
    congrArg (fun z : D.toLinearMap.range => z.val) hxy
  have hx := Module.End.mem_eigenspace_iff.mp x.property
  have hy := Module.End.mem_eigenspace_iff.mp y.property
  change T x.val = e • x.val at hx
  change T y.val = e • y.val at hy
  rw [h] at hx hy
  apply Subtype.ext
  apply natural_resolvent_injective U e he
  calc
    e • x.val - U x.val = D x.val := by rw [← hx]; abel
    _ = D y.val := hd
    _ = e • y.val - U y.val := by rw [← hy]; abel

/-- The perturbation rank bounds the dimension of every eigenspace
whose energy belongs to the comparison resolvent. -/
theorem natural_finiteDefect_eigenspace_bound
    (T U D : TileHilbert Vertex →L[ℝ] TileHilbert Vertex) (e : ℝ)
    (h : ∀ x : TileHilbert Vertex, T x = U x + D x)
    (he : e ∉ spectrum ℝ U)
    (hD : FiniteDimensional ℝ D.toLinearMap.range) :
    FiniteDimensional ℝ (Module.End.eigenspace T.toLinearMap e) ∧
      Module.finrank ℝ (Module.End.eigenspace T.toLinearMap e) ≤
        Module.finrank ℝ D.toLinearMap.range := by
  letI := hD
  have hi := naturalEigenspaceDefectMap_injective T U D e h he
  have hf := FiniteDimensional.of_injective (naturalEigenspaceDefectMap T D e) hi
  letI := hf
  exact ⟨hf, LinearMap.finrank_le_finrank_of_injective _ hi⟩

/-- The actual plateau cannot have an infinite-dimensional eigenspace
at an energy outside the real spectrum of its uniform bulk. -/
theorem canonicalPlateau_eigenspace_bound_outside_bulk (e : ℝ)
    (he : e ∉ spectrum ℝ (plateauBulk canonicalPlateauHeight)) :
    FiniteDimensional ℝ (Module.End.eigenspace canonicalPlateauHamiltonian.toLinearMap e) ∧
      Module.finrank ℝ (Module.End.eigenspace canonicalPlateauHamiltonian.toLinearMap e) ≤ 17 := by
  have h (x : TileHilbert Vertex) :
      canonicalPlateauHamiltonian x = plateauBulk canonicalPlateauHeight x +
        canonicalPlateauDefect x := by
    change canonicalPlateauHamiltonian x = plateauBulk canonicalPlateauHeight x +
      (canonicalPlateauHamiltonian x - plateauBulk canonicalPlateauHeight x)
    abel
  obtain ⟨hf, hr⟩ := natural_finiteDefect_eigenspace_bound
    canonicalPlateauHamiltonian (plateauBulk canonicalPlateauHeight)
    canonicalPlateauDefect e h he canonicalPlateauDefect_finiteDimensional
  exact ⟨hf, hr.trans canonicalPlateauDefect_finrank_le⟩

/-- In particular, every plateau eigenspace outside the certified bulk
enclosure has finite dimension at most seventeen. -/
theorem canonicalPlateau_eigenspace_bound_outside_enclosure (e : ℝ)
    (he : e < canonicalPlateauHeight ∨ canonicalPlateauHeight + 1 < e) :
    FiniteDimensional ℝ (Module.End.eigenspace canonicalPlateauHamiltonian.toLinearMap e) ∧
      Module.finrank ℝ (Module.End.eigenspace canonicalPlateauHamiltonian.toLinearMap e) ≤ 17 := by
  apply canonicalPlateau_eigenspace_bound_outside_bulk
  intro hs
  have h := plateauBulk_realSpectrum_subset canonicalPlateauHeight hs
  change canonicalPlateauHeight ≤ e ∧ e ≤ canonicalPlateauHeight + 1 at h
  rcases he with hl | hu
  · exact (not_le_of_gt hl) h.1
  · exact (not_le_of_gt hu) h.2

theorem canonicalPlateau_infinite_eigenspace_mem_bulk (e : ℝ)
    (he : ¬ FiniteDimensional ℝ
      (Module.End.eigenspace canonicalPlateauHamiltonian.toLinearMap e)) :
    e ∈ spectrum ℝ (plateauBulk canonicalPlateauHeight) := by
  by_contra hn
  exact he (canonicalPlateau_eigenspace_bound_outside_bulk e hn).1

end
end SpectralGeometry.AmmannBeenker
