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
  have hordered (u v : {n : ℕ // ev n = r})
      (huv : u.1 < v.1)
      (hcoverUV : ({u, v} : Set {n : ℕ // ev n = r}) = Set.univ) :
      ∃ n : ℕ,
        ev n = r ∧ ev (n + 1) = r ∧
          ∀ k : ℕ, ev k = r → k = n ∨ k = n + 1 := by
    have hmid : ev (u.1 + 1) = r := by
      apply le_antisymm
      · calc
          ev (u.1 + 1) ≤ ev v.1 := hmono (Nat.succ_le_of_lt huv)
          _ = r := v.property
      · calc
          r = ev u.1 := u.property.symm
          _ ≤ ev (u.1 + 1) := hmono (Nat.le_succ _)
    have hsucc : u.1 + 1 = v.1 := by
      have hmem :
          (⟨u.1 + 1, hmid⟩ : {n : ℕ // ev n = r}) ∈
            ({u, v} : Set {n : ℕ // ev n = r}) := by
        rw [hcoverUV]
        exact Set.mem_univ _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with hu | hv
      · have hbad : u.1 + 1 = u.1 := congrArg Subtype.val hu
        omega
      · exact congrArg Subtype.val hv
    refine ⟨u.1, u.property, hmid, ?_⟩
    intro k hk
    have hmem :
        (⟨k, hk⟩ : {n : ℕ // ev n = r}) ∈
          ({u, v} : Set {n : ℕ // ev n = r}) := by
      rw [hcoverUV]
      exact Set.mem_univ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with hu | hv
    · exact Or.inl (congrArg Subtype.val hu)
    · exact Or.inr ((congrArg Subtype.val hv).trans hsucc.symm)
  rcases lt_or_gt_of_ne hindices with hij | hji
  · exact hordered i j hij hcover
  · apply hordered j i hji
    calc
      ({j, i} : Set {n : ℕ // ev n = r}) = {i, j} := Set.pair_comm j i
      _ = Set.univ := hcover
end SpectralGeometry
