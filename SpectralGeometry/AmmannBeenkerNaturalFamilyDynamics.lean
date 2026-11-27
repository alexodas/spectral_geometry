module

public import SpectralGeometry.AmmannBeenkerNaturalExactPreparation

public section

/-!
# Independent dynamics under the common finite-family Hamiltonian

The selected compact planes reduce the same bounded infinite operator.
A local trajectory therefore solves the actual simultaneous-control
equation, regardless of the amplitudes on the other selected cells.
A spectator with zero controls evolves with its original distinct
energies. Linearity permits addition of component trajectories without
identifying the resulting direct sum with a tensor-product register.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open scoped Classical

/-- Equality on a selected compact plane, not equality of the operators
on the entire infinite space. -/
theorem naturalFamilyHamiltonian_agrees_local (S : Finset Vertex)
    (hp : ∀ v ∈ S, 4 < ‖position v‖ ∧
      ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (hd : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
        n + v.val ≠ m + w.val)
    (δ η : Vertex → ℝ) (v : Vertex) (hv : v ∈ S) (a b : ℝ) :
    naturalFamilyHamiltonian S δ η
        (a • translatedCompactA v.val + b • translatedCompactB v.val) =
      naturalRemoteDriven v.val (δ v) (η v)
        (a • translatedCompactA v.val + b • translatedCompactB v.val) := by
  rw [naturalFamilyHamiltonian_pair_action S hp hd δ η v hv]
  unfold naturalRemoteDriven
  rw [naturalRemoteControls_pair_action v (hp v hv).1 (hp v hv).2]

theorem naturalFamilyHamiltonian_agrees_state (S : Finset Vertex)
    (hp : ∀ v ∈ S, 4 < ‖position v‖ ∧
      ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (hd : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
        n + v.val ≠ m + w.val)
    (δ η : Vertex → ℝ) (v : Vertex) (hv : v ∈ S) (w : ℂ × ℂ) :
    naturalFamilyHamiltonian S δ η (naturalStateReal v.val w) =
      naturalRemoteDriven v.val (δ v) (η v) (naturalStateReal v.val w) ∧
    naturalFamilyHamiltonian S δ η (naturalStateImag v.val w) =
      naturalRemoteDriven v.val (δ v) (η v) (naturalStateImag v.val w) := by
  have hD : naturalFamilyHamiltonian S δ η (naturalRemoteDark v.val) =
      naturalRemoteDriven v.val (δ v) (η v) (naturalRemoteDark v.val) := by
    unfold naturalRemoteDark
    rw [smul_add]
    exact naturalFamilyHamiltonian_agrees_local S hp hd δ η v hv _ _
  have hF : naturalFamilyHamiltonian S δ η (naturalRemoteBright v.val) =
      naturalRemoteDriven v.val (δ v) (η v) (naturalRemoteBright v.val) := by
    have he : naturalRemoteBright v.val =
        (1 / 4 : ℝ) • translatedCompactA v.val + (-1 / 4 : ℝ) • translatedCompactB v.val := by
      unfold naturalRemoteBright
      module
    rw [he]
    exact naturalFamilyHamiltonian_agrees_local S hp hd δ η v hv _ _
  constructor <;> simp only [naturalStateReal, naturalStateImag, map_add, map_smul, hD, hF]

/-- Coupled real and imaginary equations with a specified full-space
Hamiltonian at the time of evaluation. -/
@[expose] def naturalFullSolvesAt (H : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (r i : ℝ → TileHilbert Vertex) (τ : ℝ) : Prop :=
  HasDerivAt r (H (i τ)) τ ∧ HasDerivAt i (-(H (r τ))) τ

theorem naturalFullSolvesAt_add (H : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (r i u j : ℝ → TileHilbert Vertex) (τ : ℝ)
    (h : naturalFullSolvesAt H r i τ) (k : naturalFullSolvesAt H u j τ) :
    naturalFullSolvesAt H (fun s => r s + u s) (fun s => i s + j s) τ := by
  unfold naturalFullSolvesAt at h k ⊢
  constructor
  · rw [map_add]
    exact h.1.add k.1
  · have he : -(H (r τ + u τ)) = -(H (r τ)) + -(H (u τ)) := by
      rw [map_add]
      abel
    rw [he]
    exact h.2.add k.2

/-- The other selected cells may be driven with arbitrary strengths:
only the controls on this cell appear in its own trajectory. -/
theorem naturalFamilySolvesAt_of_local (S : Finset Vertex)
    (hp : ∀ v ∈ S, 4 < ‖position v‖ ∧
      ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (hd : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
        n + v.val ≠ m + w.val)
    (δ η : Vertex → ℝ) (v : Vertex) (hv : v ∈ S)
    (f : ℝ → ℂ × ℂ) (τ : ℝ)
    (h : naturalSolvesAt v.val (δ v) (η v) f τ) :
    naturalFullSolvesAt (naturalFamilyHamiltonian S δ η)
      (fun s => naturalStateReal v.val (f s))
      (fun s => naturalStateImag v.val (f s)) τ := by
  obtain ⟨hR, hI⟩ := naturalFamilyHamiltonian_agrees_state S hp hd δ η v hv (f τ)
  unfold naturalFullSolvesAt
  rw [hI, hR]
  exact h

theorem naturalFamily_spectator_eigenpair (S : Finset Vertex)
    (hp : ∀ v ∈ S, 4 < ‖position v‖ ∧
      ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (hd : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
        n + v.val ≠ m + w.val)
    (δ η : Vertex → ℝ) (v : Vertex) (hv : v ∈ S)
    (hδ : δ v = 0) (hη : η v = 0) :
    naturalFamilyHamiltonian S δ η (translatedCompactA v.val) =
      (canonicalPlateauHeight + 3 / 16) • translatedCompactA v.val ∧
    naturalFamilyHamiltonian S δ η (translatedCompactB v.val) =
      (canonicalPlateauHeight + 1 / 4) • translatedCompactB v.val := by
  have hA := naturalFamilyHamiltonian_pair_action S hp hd δ η v hv 1 0
  have hB := naturalFamilyHamiltonian_pair_action S hp hd δ η v hv 0 1
  constructor
  · simpa only [hδ, hη, one_smul, zero_smul, add_zero, zero_add, mul_one, mul_zero,
      zero_mul, sub_zero] using hA
  · simpa only [hδ, hη, one_smul, zero_smul, add_zero, zero_add, mul_one, mul_zero,
      zero_mul, sub_zero] using hB

@[expose] def naturalSpectatorReal (v : Vertex) (a b : ℂ) : ℝ → TileHilbert Vertex :=
  naturalPairReal (translatedCompactA v.val) (translatedCompactB v.val)
    (canonicalPlateauHeight + 3 / 16) (canonicalPlateauHeight + 1 / 4) a b

@[expose] def naturalSpectatorImag (v : Vertex) (a b : ℂ) : ℝ → TileHilbert Vertex :=
  naturalPairImag (translatedCompactA v.val) (translatedCompactB v.val)
    (canonicalPlateauHeight + 3 / 16) (canonicalPlateauHeight + 1 / 4) a b

/-- A spectator follows its unperturbed phase evolution under the same
full operator that drives the other cells. -/
theorem naturalFamily_spectator_solvesAt (S : Finset Vertex)
    (hp : ∀ v ∈ S, 4 < ‖position v‖ ∧
      ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (hd : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
        n + v.val ≠ m + w.val)
    (δ η : Vertex → ℝ) (v : Vertex) (hv : v ∈ S)
    (hδ : δ v = 0) (hη : η v = 0) (a b : ℂ) (τ : ℝ) :
    naturalFullSolvesAt (naturalFamilyHamiltonian S δ η)
      (naturalSpectatorReal v a b) (naturalSpectatorImag v a b) τ := by
  obtain ⟨ha, hb⟩ := naturalFamily_spectator_eigenpair S hp hd δ η v hv hδ hη
  exact naturalPair_Schrodinger _ _ _ _ _ ha hb a b τ

theorem naturalFamily_driven_with_spectator (S : Finset Vertex)
    (hp : ∀ v ∈ S, 4 < ‖position v‖ ∧
      ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (hd : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
        n + v.val ≠ m + w.val)
    (δ η : Vertex → ℝ) (v w : Vertex) (hv : v ∈ S) (hw : w ∈ S)
    (hδ : δ w = 0) (hη : η w = 0)
    (f : ℝ → ℂ × ℂ) (a b : ℂ) (τ : ℝ)
    (h : naturalSolvesAt v.val (δ v) (η v) f τ) :
    naturalFullSolvesAt (naturalFamilyHamiltonian S δ η)
      (fun s => naturalStateReal v.val (f s) + naturalSpectatorReal w a b s)
      (fun s => naturalStateImag v.val (f s) + naturalSpectatorImag w a b s) τ := by
  exact naturalFullSolvesAt_add _ _ _ _ _ _
    (naturalFamilySolvesAt_of_local S hp hd δ η v hv f τ h)
    (naturalFamily_spectator_solvesAt S hp hd δ η w hw hδ hη a b τ)

/-- Two independently driven trajectories are compatible with one
common Hamiltonian, including when their natural energies coincide. -/
theorem naturalFamily_two_driven (S : Finset Vertex)
    (hp : ∀ v ∈ S, 4 < ‖position v‖ ∧
      ∀ n ∈ centralRecurrenceLifts, Admitted (n + v.val) ↔ Admitted n)
    (hd : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ∀ n ∈ centralRecurrenceLifts, ∀ m ∈ centralRecurrenceLifts,
        n + v.val ≠ m + w.val)
    (δ η : Vertex → ℝ) (v w : Vertex) (hv : v ∈ S) (hw : w ∈ S)
    (f g : ℝ → ℂ × ℂ) (τ : ℝ)
    (hf : naturalSolvesAt v.val (δ v) (η v) f τ)
    (hg : naturalSolvesAt w.val (δ w) (η w) g τ) :
    naturalFullSolvesAt (naturalFamilyHamiltonian S δ η)
      (fun s => naturalStateReal v.val (f s) + naturalStateReal w.val (g s))
      (fun s => naturalStateImag v.val (f s) + naturalStateImag w.val (g s)) τ := by
  exact naturalFullSolvesAt_add _ _ _ _ _ _
    (naturalFamilySolvesAt_of_local S hp hd δ η v hv f τ hf)
    (naturalFamilySolvesAt_of_local S hp hd δ η w hw g τ hg)

end
end SpectralGeometry.AmmannBeenker
