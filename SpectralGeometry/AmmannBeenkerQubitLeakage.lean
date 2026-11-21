module

public import SpectralGeometry.AmmannBeenkerTwoControlAlgebra

public section

/-!
# An exact qubit/leakage decomposition at the infinite-graph crossing

The two compact states have squared norm eight and are orthogonal. Every
state of the real infinite-graph Hilbert space therefore decomposes into
its two compact-mode amplitudes and an orthogonal remainder.

The norm identity is a static, full-space statement and does NOT assume
that a transient edge perturbation preserves the compact-mode plane.
When the original operator is restored, the compact-mode component
again belongs to the exact energy eigenspace. Its orthogonal remainder
need not vanish merely because the Hamiltonian was restored.

The quantities here are real-Hilbert-space squared norms. Modeling
complex quantum probabilities, unitary pulse propagators and dynamical
leakage bounds is separate work.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- Coefficient of the first unnormalized compact mode in the orthogonal
two-mode projection. The denominator is its exact squared norm. -/
@[expose] def crossingCoeffA (ψ : TileHilbert Vertex) : ℝ :=
  inner ℝ compactA ψ / 8

/-- Coefficient of the second unnormalized compact mode. -/
@[expose] def crossingCoeffB (ψ : TileHilbert Vertex) : ℝ :=
  inner ℝ compactB ψ / 8

/-- The component of an arbitrary full-space state in the two-mode plane. -/
@[expose] def crossingQubitPart (ψ : TileHilbert Vertex) : TileHilbert Vertex :=
  crossingCoeffA ψ • compactA + crossingCoeffB ψ • compactB

/-- The component outside the original two-mode crossing eigenspace. -/
@[expose] def crossingLeakage (ψ : TileHilbert Vertex) : TileHilbert Vertex :=
  ψ - crossingQubitPart ψ

/-- Every state is the sum of its compact-mode component and its leakage. -/
theorem crossingQubitPart_add_leakage (ψ : TileHilbert Vertex) :
    crossingQubitPart ψ + crossingLeakage ψ = ψ := by
  simp only [crossingLeakage]
  abel

/-- The leakage has no component along the first compact mode. -/
theorem crossingLeakage_inner_compactA (ψ : TileHilbert Vertex) :
    inner ℝ compactA (crossingLeakage ψ) = 0 := by
  simp only [crossingLeakage, crossingQubitPart, crossingCoeffA, crossingCoeffB,
    inner_sub_right, inner_add_right, real_inner_smul_right,
    compactA_inner_self, compactA_inner_compactB]
  ring

/-- The leakage has no component along the second compact mode. -/
theorem crossingLeakage_inner_compactB (ψ : TileHilbert Vertex) :
    inner ℝ compactB (crossingLeakage ψ) = 0 := by
  have hba : inner ℝ compactB compactA = 0 := by
    rw [real_inner_comm, compactA_inner_compactB]
  simp only [crossingLeakage, crossingQubitPart, crossingCoeffA, crossingCoeffB,
    inner_sub_right, inner_add_right, real_inner_smul_right,
    compactB_inner_self, hba]
  ring

/-- The compact-mode projection and the residual component are orthogonal. -/
theorem crossingQubitPart_inner_leakage (ψ : TileHilbert Vertex) :
    inner ℝ (crossingQubitPart ψ) (crossingLeakage ψ) = 0 := by
  simp only [crossingQubitPart, inner_add_left, real_inner_smul_left,
    crossingLeakage_inner_compactA, crossingLeakage_inner_compactB]
  ring

/-- The squared norm in the compact plane is the sum of the two
unnormalized-mode amplitude squares, each weighted by eight. -/
theorem crossingQubitPart_norm_sq (ψ : TileHilbert Vertex) :
    ‖crossingQubitPart ψ‖ ^ 2 =
      8 * (crossingCoeffA ψ ^ 2 + crossingCoeffB ψ ^ 2) := by
  have hba : inner ℝ compactB compactA = 0 := by
    rw [real_inner_comm, compactA_inner_compactB]
  rw [← real_inner_self_eq_norm_sq]
  simp only [crossingQubitPart, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    compactA_inner_self, compactB_inner_self, compactA_inner_compactB, hba]
  ring

/-- Exact Pythagorean decomposition in the full infinite Hilbert space.
No spectral gap or perturbative approximation is used. -/
theorem crossingQubitPart_leakage_norm_sq (ψ : TileHilbert Vertex) :
    ‖ψ‖ ^ 2 =
      ‖crossingQubitPart ψ‖ ^ 2 + ‖crossingLeakage ψ‖ ^ 2 := by
  have hcomm :
      inner ℝ (crossingLeakage ψ) (crossingQubitPart ψ) = 0 := by
    rw [real_inner_comm, crossingQubitPart_inner_leakage]
  calc
    ‖ψ‖ ^ 2 = inner ℝ ψ ψ := by rw [real_inner_self_eq_norm_sq]
    _ = inner ℝ (crossingQubitPart ψ + crossingLeakage ψ)
        (crossingQubitPart ψ + crossingLeakage ψ) := by
          simp only [crossingQubitPart_add_leakage]
    _ = ‖crossingQubitPart ψ‖ ^ 2 + ‖crossingLeakage ψ‖ ^ 2 := by
          simp only [inner_add_left, inner_add_right,
            crossingQubitPart_inner_leakage, hcomm,
            real_inner_self_eq_norm_sq]
          ring

/-- For a unit-norm real state, the two compact-mode weights and the
external weight exhaust the total squared norm exactly. -/
theorem crossingProbability_budget (ψ : TileHilbert Vertex)
    (hunit : ‖ψ‖ = 1) :
    8 * (crossingCoeffA ψ ^ 2 + crossingCoeffB ψ ^ 2) +
      ‖crossingLeakage ψ‖ ^ 2 = 1 := by
  have h := crossingQubitPart_leakage_norm_sq ψ
  rw [hunit, one_pow, crossingQubitPart_norm_sq] at h
  linarith

/-- A prescribed small leakage weight is equivalent to a compact-mode
weight close to one, provided the input is normalized. -/
theorem crossingProbability_leakage_eq (ψ : TileHilbert Vertex)
    (hunit : ‖ψ‖ = 1) :
    ‖crossingLeakage ψ‖ ^ 2 =
      1 - 8 * (crossingCoeffA ψ ^ 2 + crossingCoeffB ψ ^ 2) := by
  have h := crossingProbability_budget ψ hunit
  linarith

/-- A leakage threshold turns into a rigorous lower bound on the
total squared weight of the two selected compact modes. -/
theorem crossingProbability_qubit_at_least (ψ : TileHilbert Vertex)
    (hunit : ‖ψ‖ = 1) (η : ℝ)
    (hleak : ‖crossingLeakage ψ‖ ^ 2 ≤ η) :
    1 - η ≤
      8 * (crossingCoeffA ψ ^ 2 + crossingCoeffB ψ ^ 2) := by
  have h := crossingProbability_budget ψ hunit
  linarith

/-- No leakage is equivalent to the state lying exactly in its
two-mode projection. -/
theorem crossingLeakage_eq_zero_iff (ψ : TileHilbert Vertex) :
    crossingLeakage ψ = 0 ↔ ψ = crossingQubitPart ψ := by
  simp only [crossingLeakage, sub_eq_zero]

/-- After the controls are returned to the crossing configuration,
the compact-mode component of ANY final state is again an exact
full-natural-domain eigenvector at the original crossing energy.
This says nothing about the generally nonzero leakage component. -/
theorem crossingQubitPart_restored_eigenvector (ψ : TileHilbert Vertex) :
    onsitePlusBounded potential (ringInteraction crossingParameter)
      (crossingCoeffA ψ • domainCompactA +
        crossingCoeffB ψ • domainCompactB) =
      crossingEnergy • crossingQubitPart ψ := by
  simpa [crossingQubitPart] using
    (detuning_two_mode_action 0 (crossingCoeffA ψ) (crossingCoeffB ψ))

end
end SpectralGeometry.AmmannBeenker
