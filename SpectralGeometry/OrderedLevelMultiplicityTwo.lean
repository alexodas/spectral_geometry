module

public import SpectralGeometry.InfiniteFullSpectralProduct
public import Mathlib.SetTheory.Cardinal.Finite

public section

/-!
# Two adjacent slots for an exactly double ordered spectral level

An ordered sequence in which a level occurs exactly twice must carry
that level at consecutive indices. This elementary interface allows
geometric eigenvalue multiplicity statements to locate the only two
ordered positions where a spectral perturbation can move levels.
-/

namespace SpectralGeometry

/-- If the fiber of a monotone real sequence has exactly two members,
they are adjacent natural-number indices and exhaust the fiber. -/
theorem ordered_levelMultiplicity_two_consecutive
    (ev : ℕ → ℝ) (r : ℝ) (hmono : Monotone ev)
    (hcount : levelMultiplicity ev r = 2) :
    ∃ n : ℕ,
      ev n = r ∧ ev (n + 1) = r ∧
        ∀ k : ℕ, ev k = r → k = n ∨ k = n + 1 := by
  classical
  have hcard : Nat.card {n : ℕ // ev n = r} = 2 := hcount
  obtain ⟨i, j, hne, hcover⟩ := Nat.card_eq_two_iff.mp hcard
  have hindices : i.1 ≠ j.1 := by
    intro h
    exact hne (Subtype.ext h)
  have hordered (i j : {n : ℕ // ev n = r})
      (hij : i.1 < j.1)
      (hcover : ({i, j} : Set {n : ℕ // ev n = r}) = Set.univ) :
      ∃ n : ℕ,
        ev n = r ∧ ev (n + 1) = r ∧
          ∀ k : ℕ, ev k = r → k = n ∨ k = n + 1 := by
    have hmid : ev (i.1 + 1) = r := by
      apply le_antisymm
      · calc
          ev (i.1 + 1) ≤ ev j.1 := hmono (Nat.succ_le_of_lt hij)
          _ = r := j.property
      · calc
          r = ev i.1 := i.property.symm
          _ ≤ ev (i.1 + 1) := hmono (Nat.le_succ _)
    have hsucc : i.1 + 1 = j.1 := by
      have hmem :
          (⟨i.1 + 1, hmid⟩ : {n : ℕ // ev n = r}) ∈
            ({i, j} : Set {n : ℕ // ev n = r}) := by
        rw [hcover]
        exact Set.mem_univ _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with hi | hj
      · have hh := congrArg Subtype.val hi
        omega
      · exact congrArg Subtype.val hj
    refine ⟨i.1, i.property, hmid, ?_⟩
    intro k hk
    have hmem :
        (⟨k, hk⟩ : {n : ℕ // ev n = r}) ∈
          ({i, j} : Set {n : ℕ // ev n = r}) := by
      rw [hcover]
      exact Set.mem_univ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with hi | hj
    · exact Or.inl (congrArg Subtype.val hi)
    · exact Or.inr ((congrArg Subtype.val hj).trans hsucc.symm)
  rcases lt_or_gt_of_ne hindices with hij | hji
  · exact hordered i j hij hcover
  · apply hordered j i hji
    simpa only [Set.insert_comm] using hcover

end SpectralGeometry
