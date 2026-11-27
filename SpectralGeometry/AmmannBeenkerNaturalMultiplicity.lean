module

public import SpectralGeometry.AmmannBeenkerNaturalRemoteCompleteness

public section

/-!
# Infinite global multiplicity of the two natural plateau energies

Local completeness concerns vectors supported in one seventeen-site
cell. The same two energies recur in arbitrarily many orthogonal cells.
Each global eigenspace therefore fails to be finite-dimensional.
The result does not decide isolation of either full eigenspace from
the remaining spectral energies.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

/-- Arbitrarily large finite orthogonal families of nonzero eigenvectors
exclude finite-dimensionality of the full eigenspace. -/
theorem not_finiteDimensional_of_orthogonal_eigenfamilies
    (T : TileHilbert Vertex →L[ℝ] TileHilbert Vertex) (e : ℝ)
    (h : ∀ N : ℕ, ∃ S : Finset Vertex, S.card = N ∧
      ∃ f : S → TileHilbert Vertex,
        (∀ i, T (f i) = e • f i) ∧
        (∀ i, inner ℝ (f i) (f i) = 8) ∧
        (∀ i j, i ≠ j → inner ℝ (f i) (f j) = 0)) :
    ¬ FiniteDimensional ℝ (Module.End.eigenspace T.toLinearMap e) := by
  intro hfin
  letI := hfin
  let P := Module.End.eigenspace T.toLinearMap e
  obtain ⟨S, hc, f, he, hnorm, ho⟩ := h (Module.finrank ℝ P + 1)
  let g : S → P := fun i => ⟨f i, Module.End.mem_eigenspace_iff.mpr (he i)⟩
  have hg (i : S) : g i ≠ 0 := by
    intro hz
    have hzero : f i = 0 := congrArg (fun x : P => (x : TileHilbert Vertex)) hz
    have hi := hnorm i
    rw [hzero, inner_zero_left] at hi
    norm_num at hi
  have horth : Pairwise (fun i j : S => inner ℝ (g i) (g j) = 0) := by
    intro i j hij
    change inner ℝ (f i) (f j) = 0
    exact ho i j hij
  have hli : LinearIndependent ℝ g :=
    linearIndependent_of_ne_zero_of_inner_eq_zero hg horth
  have hb : Fintype.card S ≤ Module.finrank ℝ P := hli.fintype_card_le_finrank
  rw [Fintype.card_coe, hc] at hb
  omega

/-- Both replicated energies have infinite global multiplicity on the
actual canonical plateau, with its original central defect. -/
theorem canonicalPlateau_natural_eigenspaces_infinite :
    (¬ FiniteDimensional ℝ (Module.End.eigenspace canonicalPlateauHamiltonian.toLinearMap
      (canonicalPlateauHeight + 3 / 16))) ∧
    (¬ FiniteDimensional ℝ (Module.End.eigenspace canonicalPlateauHamiltonian.toLinearMap
      (canonicalPlateauHeight + 1 / 4))) := by
  constructor
  · apply not_finiteDimensional_of_orthogonal_eigenfamilies
    intro N
    obtain ⟨S, hc, hp, hs⟩ := exact_recurrent_natural_plateau_pairs 0 0 le_rfl N
    refine ⟨S, hc, (fun i => translatedCompactA i.val.val), ?_, ?_, ?_⟩
    · intro i
      exact (hp i.val i.property).2.2.2.1
    · intro i
      exact (hp i.val i.property).2.2.2.2.2.1
    · intro i j hij
      have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      exact (hs i.val i.property j.val j.property hne).2.2.1
  · apply not_finiteDimensional_of_orthogonal_eigenfamilies
    intro N
    obtain ⟨S, hc, hp, hs⟩ := exact_recurrent_natural_plateau_pairs 0 0 le_rfl N
    refine ⟨S, hc, (fun i => translatedCompactB i.val.val), ?_, ?_, ?_⟩
    · intro i
      exact (hp i.val i.property).2.2.2.2.1
    · intro i
      exact (hp i.val i.property).2.2.2.2.2.2.1
    · intro i j hij
      have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      exact (hs i.val i.property j.val j.property hne).2.2.2.2.2

/-- The same infinite multiplicities hold at every uniform height,
including zero. No trapping potential is needed for these modes. -/
theorem plateauBulk_natural_eigenspaces_infinite (C : ℝ) :
    (¬ FiniteDimensional ℝ (Module.End.eigenspace (plateauBulk C).toLinearMap
      (C + 3 / 16))) ∧
    (¬ FiniteDimensional ℝ (Module.End.eigenspace (plateauBulk C).toLinearMap
      (C + 1 / 4))) := by
  constructor
  · apply not_finiteDimensional_of_orthogonal_eigenfamilies
    intro N
    obtain ⟨S, hc, hp, hs⟩ := exact_recurrent_compact_mode_pairs 0 0 le_rfl N
    refine ⟨S, hc, (fun i => translatedCompactA i.val.val), ?_, ?_, ?_⟩
    · intro i
      exact plateauBulk_eigenvector_of_interaction C _ _
        (hp i.val i.property).2.2.1
    · intro i
      exact (hp i.val i.property).2.2.2.2.1
    · intro i j hij
      have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      exact (hs i.val i.property j.val j.property hne).2.2.1
  · apply not_finiteDimensional_of_orthogonal_eigenfamilies
    intro N
    obtain ⟨S, hc, hp, hs⟩ := exact_recurrent_compact_mode_pairs 0 0 le_rfl N
    refine ⟨S, hc, (fun i => translatedCompactB i.val.val), ?_, ?_, ?_⟩
    · intro i
      exact plateauBulk_eigenvector_of_interaction C _ _
        (hp i.val i.property).2.2.2.1
    · intro i
      exact (hp i.val i.property).2.2.2.2.2.1
    · intro i j hij
      have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      exact (hs i.val i.property j.val j.property hne).2.2.2.2.2

end
end SpectralGeometry.AmmannBeenker
