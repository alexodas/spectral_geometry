module

public import SpectralGeometry.AmmannBeenkerDarkSchrodinger

public section

/-!
# Exact bright-amplitude forcing for the selected edge

We work on the full, infinite, real Ammann--Beenker Hilbert space
and the original natural onsite domain. Let P be the exact
orthogonal projection onto the compact A/B crossing plane and
Q = I - P. The bright F = (a-b)/4 is normalized, but W F
does not belong to the crossing plane.

For every domain vector x and every real edge strength epsilon,
the exact matrix element of the full Hamiltonian satisfies

  <F, (K_* + epsilon W) x>
    = (E_* + epsilon/4) <F,x> + epsilon <F,W Qx>.

The second term is the *external-mode feedback*, not a remainder
that may be discarded. It is bounded by
  2 |epsilon| ||Qx||
using the certified edge norm. The dark D instead obeys
  <D, (K_* + epsilon W) x> = E_* <D,x>.

These are generator identities, not an asserted propagator, an
adiabatic statement, a time-dependent ramp estimate, or a
Schrodinger evolution for arbitrary initial states.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- The original full-graph Hamiltonian has the normalized
bright vector as a crossing eigenvector. This ceases to hold
for the edge-perturbed Hamiltonian in general. -/
theorem crossingBright_original_eigen :
    onsitePlusBounded potential (ringInteraction crossingParameter)
        domainCrossingBright =
      crossingEnergy • crossingBright := by
  simp only [domainCrossingBright, map_smul, map_sub,
    compact_crossing.2.1, compact_crossing.2.2, crossingBright]
  module

/-- The selected-edge pulse acts on the bright state by its
original eigenvalue plus the FULL edge force. The right-hand
side is not generally a scalar multiple of bright. -/
theorem crossingBright_pulse_action (ε : ℝ) :
    onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge)
        domainCrossingBright =
      crossingEnergy • crossingBright +
        ε • crossingEdge crossingBright := by
  rw [crossingEdge_perturbation_identity,
    crossingBright_original_eigen]
  have hcoe :
      (domainCrossingBright : TileHilbert Vertex) = crossingBright := by
    rfl
  rw [hcoe]

theorem crossingBright_norm_one : ‖crossingBright‖ = 1 := by
  have h := crossingBright_norm_sq
  nlinarith [norm_nonneg crossingBright]

/-- The bright direction is exactly orthogonal to every
off-plane component, with no support or finite-volume
assumption on the supplied state. -/
theorem crossingBright_inner_leakage (ψ : TileHilbert Vertex) :
    inner ℝ crossingBright (crossingLeakage ψ) = 0 := by
  simp only [crossingBright, real_inner_smul_left, inner_sub_left,
    crossingLeakage_inner_compactA, crossingLeakage_inner_compactB]
  ring

theorem crossingBright_inner_compactA :
    inner ℝ crossingBright compactA = 2 := by
  have hba : inner ℝ compactB compactA = 0 := by
    rw [real_inner_comm, compactA_inner_compactB]
  simp only [crossingBright, real_inner_smul_left, inner_sub_left,
    compactA_inner_self, hba]
  norm_num

theorem crossingBright_inner_compactB :
    inner ℝ crossingBright compactB = -2 := by
  simp only [crossingBright, real_inner_smul_left, inner_sub_left,
    compactA_inner_compactB, compactB_inner_self]
  norm_num

/-- The exact bright amplitude is determined by its orthogonal
two-mode projection; the external component contributes zero
to this particular inner product. -/
theorem crossingBright_inner_eq_qubitPart (ψ : TileHilbert Vertex) :
    inner ℝ crossingBright ψ =
      inner ℝ crossingBright (crossingQubitPart ψ) := by
  have h := congrArg (fun z : TileHilbert Vertex => inner ℝ crossingBright z)
    (crossingQubitPart_add_leakage ψ)
  rw [inner_add_right, crossingBright_inner_leakage, add_zero] at h
  exact h.symm

/-- The chosen edge produces an exact bright overlap of 1/2
on the unnormalized first compact mode. -/
theorem crossingBright_edge_compactA :
    inner ℝ crossingBright (crossingEdge compactA) = 1 / 2 := by
  rw [crossingEdge_inner]
  simp only [crossingBright_apply, compactA_siteA, compactB_siteA,
    compactA_siteB, compactB_siteB]
  norm_num

/-- The edge compression along the bright state is 1/4.
This identity only concerns P W P, not invariance of P. -/
theorem crossingBright_edge_qubitPart (ψ : TileHilbert Vertex) :
    inner ℝ crossingBright (crossingEdge (crossingQubitPart ψ)) =
      (1 / 4 : ℝ) * inner ℝ crossingBright ψ := by
  have hpart :
      inner ℝ crossingBright (crossingQubitPart ψ) =
        2 * (crossingCoeffA ψ - crossingCoeffB ψ) := by
    simp only [crossingQubitPart, inner_add_right, real_inner_smul_right,
      crossingBright_inner_compactA, crossingBright_inner_compactB]
    ring
  calc
    inner ℝ crossingBright (crossingEdge (crossingQubitPart ψ)) =
        (crossingCoeffA ψ - crossingCoeffB ψ) * (1 / 2 : ℝ) := by
      rw [crossingQubitPart, crossingEdge_two_mode_action,
        real_inner_smul_right, crossingBright_edge_compactA]
    _ = (1 / 4 : ℝ) * inner ℝ crossingBright ψ := by
      rw [crossingBright_inner_eq_qubitPart ψ, hpart]
      ring

/-- Exact decomposition of the edge's bright matrix element.
The second summand is the feedback from the orthogonal complement
and is not assumed to vanish. -/
theorem crossingBright_edge_full_split (ψ : TileHilbert Vertex) :
    inner ℝ crossingBright (crossingEdge ψ) =
      (1 / 4 : ℝ) * inner ℝ crossingBright ψ +
        inner ℝ crossingBright (crossingEdge (crossingLeakage ψ)) := by
  calc
    inner ℝ crossingBright (crossingEdge ψ) =
        inner ℝ crossingBright
          (crossingEdge (crossingQubitPart ψ + crossingLeakage ψ)) := by
      rw [crossingQubitPart_add_leakage]
    _ = inner ℝ crossingBright (crossingEdge (crossingQubitPart ψ)) +
        inner ℝ crossingBright (crossingEdge (crossingLeakage ψ)) := by
      rw [map_add, inner_add_right]
    _ = (1 / 4 : ℝ) * inner ℝ crossingBright ψ +
        inner ℝ crossingBright (crossingEdge (crossingLeakage ψ)) := by
      rw [crossingBright_edge_qubitPart]

/-- Exact full-Hamiltonian bright-amplitude generator identity.
The leakage term must be retained. The identity holds for every
real epsilon, including the degenerate endpoint epsilon = 0. -/
theorem crossingBright_pulse_amplitude (ε : ℝ)
    (x : infiniteOnsiteDomain potential) :
    inner ℝ crossingBright
      (onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge) x) =
      (crossingEnergy + ε / 4) *
          inner ℝ crossingBright (x : TileHilbert Vertex) +
        ε * inner ℝ crossingBright
          (crossingEdge (crossingLeakage (x : TileHilbert Vertex))) := by
  have hsymm :
      inner ℝ crossingBright
          (onsitePlusBounded potential
            (ringInteraction crossingParameter + ε • crossingEdge) x) =
        inner ℝ
          (onsitePlusBounded potential
            (ringInteraction crossingParameter + ε • crossingEdge)
            domainCrossingBright)
          (x : TileHilbert Vertex) :=
    (onsitePlusBounded_symmetric potential
      (ringInteraction crossingParameter + ε • crossingEdge)
      (crossingEdgePulseCorrection_symmetric ε)
      domainCrossingBright x).symm
  calc
    inner ℝ crossingBright
        (onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x) =
      inner ℝ
        (onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge)
          domainCrossingBright)
        (x : TileHilbert Vertex) := hsymm
    _ = inner ℝ
        (crossingEnergy • crossingBright + ε • crossingEdge crossingBright)
        (x : TileHilbert Vertex) := by rw [crossingBright_pulse_action]
    _ = crossingEnergy * inner ℝ crossingBright (x : TileHilbert Vertex) +
          ε * inner ℝ crossingBright
            (crossingEdge (x : TileHilbert Vertex)) := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
        crossingEdge_symmetric_full crossingBright (x : TileHilbert Vertex)]
    _ = (crossingEnergy + ε / 4) *
          inner ℝ crossingBright (x : TileHilbert Vertex) +
        ε * inner ℝ crossingBright
          (crossingEdge (crossingLeakage (x : TileHilbert Vertex))) := by
      rw [crossingBright_edge_full_split]
      ring

/-- For comparison: the dark amplitude has no external-mode
forcing term, for any real strength of the very same edge. -/
theorem crossingDark_pulse_amplitude (ε : ℝ)
    (x : infiniteOnsiteDomain potential) :
    inner ℝ crossingDark
      (onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge) x) =
      crossingEnergy * inner ℝ crossingDark (x : TileHilbert Vertex) := by
  calc
    inner ℝ crossingDark
        (onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x) =
      inner ℝ
        (onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge)
          domainCrossingDark)
        (x : TileHilbert Vertex) :=
        (onsitePlusBounded_symmetric potential
          (ringInteraction crossingParameter + ε • crossingEdge)
          (crossingEdgePulseCorrection_symmetric ε)
          domainCrossingDark x).symm
    _ = crossingEnergy * inner ℝ crossingDark (x : TileHilbert Vertex) := by
      rw [crossingDark_full_eigenvector, real_inner_smul_left]

/-- A normalized bright vector has absolute inner product at most
the norm of the other full-space vector. -/
theorem crossingBright_abs_inner_le_norm (z : TileHilbert Vertex) :
    |inner ℝ crossingBright z| ≤ ‖z‖ := by
  have hu : inner ℝ crossingBright z ≤ ‖z‖ := by
    simpa only [crossingBright_norm_one, one_mul] using
      (real_inner_le_norm crossingBright z)
  have hl : -(inner ℝ crossingBright z) ≤ ‖z‖ := by
    have h := real_inner_le_norm crossingBright (-z)
    simpa only [crossingBright_norm_one, one_mul,
      inner_neg_right, norm_neg] using h
  exact abs_le.mpr ⟨by linarith, hu⟩

/-- Quantitative, full-infinite-graph bound on the error made by
the compressed bright frequency E_* + epsilon/4. It depends on
the ACTUAL leakage of x, and has exact zero error when Qx=0.
It is an instantaneous generator estimate, not an integrated
phase-error or ramp estimate. -/
theorem crossingBright_pulse_amplitude_error_bound (ε : ℝ)
    (x : infiniteOnsiteDomain potential) :
    |inner ℝ crossingBright
        (onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x) -
      (crossingEnergy + ε / 4) *
        inner ℝ crossingBright (x : TileHilbert Vertex)| ≤
      2 * |ε| * ‖crossingLeakage (x : TileHilbert Vertex)‖ := by
  have hid :
      inner ℝ crossingBright
          (onsitePlusBounded potential
            (ringInteraction crossingParameter + ε • crossingEdge) x) -
        (crossingEnergy + ε / 4) *
          inner ℝ crossingBright (x : TileHilbert Vertex) =
      ε * inner ℝ crossingBright
        (crossingEdge (crossingLeakage (x : TileHilbert Vertex))) := by
    rw [crossingBright_pulse_amplitude]
    ring
  rw [hid, abs_mul]
  calc
    |ε| *
      |inner ℝ crossingBright
        (crossingEdge (crossingLeakage (x : TileHilbert Vertex)))| ≤
      |ε| * ‖crossingEdge (crossingLeakage (x : TileHilbert Vertex))‖ :=
        mul_le_mul_of_nonneg_left
          (crossingBright_abs_inner_le_norm _) (abs_nonneg ε)
    _ ≤ |ε| * (2 * ‖crossingLeakage (x : TileHilbert Vertex)‖) :=
        mul_le_mul_of_nonneg_left
          (crossingEdge_apply_norm_le_two _) (abs_nonneg ε)
    _ = 2 * |ε| * ‖crossingLeakage (x : TileHilbert Vertex)‖ := by ring

/-- One compact full-graph control theorem selected for a possible
second Palomar comparison. The first clause is an exact eigenstate,
the second retains full exterior feedback, and the third bounds the
generator-level error from replacing the bright response by its
two-mode compression. No time evolution or spectral splitting is
claimed. -/
theorem crossingOneEdgeDarkBrightResponse (ε : ℝ)
    (x : infiniteOnsiteDomain potential) :
    onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge)
        domainCrossingDark = crossingEnergy • crossingDark ∧
      (inner ℝ crossingBright
          (onsitePlusBounded potential
            (ringInteraction crossingParameter + ε • crossingEdge) x) =
        (crossingEnergy + ε / 4) *
            inner ℝ crossingBright (x : TileHilbert Vertex) +
          ε * inner ℝ crossingBright
            (crossingEdge (crossingLeakage (x : TileHilbert Vertex)))) ∧
      |inner ℝ crossingBright
          (onsitePlusBounded potential
            (ringInteraction crossingParameter + ε • crossingEdge) x) -
        (crossingEnergy + ε / 4) *
          inner ℝ crossingBright (x : TileHilbert Vertex)| ≤
        2 * |ε| * ‖crossingLeakage (x : TileHilbert Vertex)‖ := by
  exact ⟨crossingDark_full_eigenvector ε,
    crossingBright_pulse_amplitude ε x,
    crossingBright_pulse_amplitude_error_bound ε x⟩

end
end SpectralGeometry.AmmannBeenker
