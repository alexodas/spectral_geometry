module

public import SpectralGeometry.AmmannBeenkerPulseSelfAdjoint

public section

/-!
# A selected-edge pulse followed by free evolution

The previous results concern a fixed-strength pulse on the full
real infinite Ammann–Beenker graph. A physical protocol also
switches the selected edge *off*. Conservation of the residual
for the pulse Hamiltonian does not automatically imply
conservation of that residual after the switch.

Here we formalize the correct two-segment argument: while the
edge is active, conserve the residual of K_* + εW; after it
is switched off, conserve the residual of K_* instead. At the
switching instant, the two residuals differ by the bounded
edge term, whose exact operator norm is 2.

For an initial crossing eigenvector, both stages together
still have leakage ≤ 512|ε| times its initial norm, without
any factor involving either elapsed duration.

All state and evolution hypotheses are explicit. The
physical complex Schrödinger propagator is NOT constructed
by the real Hilbert-space statements in this module.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- Zero edge strength recovers the original crossing residual. -/
theorem crossingEdgePulseResidual_zero
    (x : infiniteOnsiteDomain potential) :
    crossingEdgePulseResidual 0 x =
      onsitePlusBounded potential (ringInteraction crossingParameter) x -
        crossingEnergy • (x : TileHilbert Vertex) := by
  simpa only [zero_smul, add_zero] using
    (crossingEdgePulseResidual_eq 0 x)

/-- The residual for a switched-on edge is small on every
original crossing eigenvector, without any evolution assumption. -/
theorem crossingEdgePulseResidual_initial_bound
    (ε : ℝ) (x : infiniteOnsiteDomain potential)
    (hx : onsitePlusBounded potential
        (ringInteraction crossingParameter) x =
          crossingEnergy • (x : TileHilbert Vertex)) :
    ‖crossingEdgePulseResidual ε x‖ ≤
      2 * |ε| * ‖(x : TileHilbert Vertex)‖ := by
  rw [crossingEdgePulseResidual_of_crossing_eigenvector ε x hx,
    norm_smul, Real.norm_eq_abs]
  calc
    |ε| * ‖crossingEdge (x : TileHilbert Vertex)‖ ≤
        |ε| * (2 * ‖(x : TileHilbert Vertex)‖) :=
      mul_le_mul_of_nonneg_left
        (crossingEdge_apply_norm_le_two (x : TileHilbert Vertex))
        (abs_nonneg ε)
    _ = 2 * |ε| * ‖(x : TileHilbert Vertex)‖ := by ring

/-- On switching the edge off, the original (unperturbed)
residual is at most 4|ε| times the initial norm.
This step uses the full actual graph and the exact edge norm;
there is no finite-dimensional truncation. -/
theorem crossingEdgePulse_switch_off_residual_bound
    (ε : ℝ) (x y : infiniteOnsiteDomain potential)
    (hx : onsitePlusBounded potential
        (ringInteraction crossingParameter) x =
          crossingEnergy • (x : TileHilbert Vertex))
    (hnorm : ‖(y : TileHilbert Vertex)‖ =
      ‖(x : TileHilbert Vertex)‖)
    (hpulse : ‖crossingEdgePulseResidual ε y‖ =
      ‖crossingEdgePulseResidual ε x‖) :
    ‖crossingEdgePulseResidual 0 y‖ ≤
      4 * |ε| * ‖(x : TileHilbert Vertex)‖ := by
  have hfinalEdge :
      |ε| * ‖crossingEdge (y : TileHilbert Vertex)‖ ≤
        2 * |ε| * ‖(x : TileHilbert Vertex)‖ := by
    calc
      |ε| * ‖crossingEdge (y : TileHilbert Vertex)‖ ≤
          |ε| * (2 * ‖(y : TileHilbert Vertex)‖) :=
        mul_le_mul_of_nonneg_left
          (crossingEdge_apply_norm_le_two (y : TileHilbert Vertex))
          (abs_nonneg ε)
      _ = 2 * |ε| * ‖(x : TileHilbert Vertex)‖ := by
        rw [hnorm]
        ring
  calc
    ‖crossingEdgePulseResidual 0 y‖ =
        ‖onsitePlusBounded potential
            (ringInteraction crossingParameter) y -
          crossingEnergy • (y : TileHilbert Vertex)‖ := by
      rw [crossingEdgePulseResidual_zero]
    _ ≤ ‖crossingEdgePulseResidual ε y‖ +
        |ε| * ‖crossingEdge (y : TileHilbert Vertex)‖ :=
      crossingOriginalResidual_le_pulseResidual ε y
    _ ≤ (2 * |ε| * ‖(x : TileHilbert Vertex)‖) +
        (2 * |ε| * ‖(x : TileHilbert Vertex)‖) := by
      apply add_le_add
      · calc
          ‖crossingEdgePulseResidual ε y‖ =
              ‖crossingEdgePulseResidual ε x‖ := hpulse
          _ ≤ 2 * |ε| * ‖(x : TileHilbert Vertex)‖ :=
            crossingEdgePulseResidual_initial_bound ε x hx
      · exact hfinalEdge
    _ = 4 * |ε| * ‖(x : TileHilbert Vertex)‖ := by ring

/-- After the edge is switched off, any subsequent free
evolution that conserves the *unperturbed* shifted-residual
norm retains the same full-graph leakage bound.

The norm and the perturbed residual are conserved during
the controlled segment; the unperturbed residual is conserved
during the free segment. No bound on the lengths of either
segment is imposed. -/
theorem crossingEdgePulse_then_free_leakage_bound
    (ε : ℝ) (x y z : infiniteOnsiteDomain potential)
    (hx : onsitePlusBounded potential
        (ringInteraction crossingParameter) x =
          crossingEnergy • (x : TileHilbert Vertex))
    (hnorm : ‖(y : TileHilbert Vertex)‖ =
      ‖(x : TileHilbert Vertex)‖)
    (hpulse : ‖crossingEdgePulseResidual ε y‖ =
      ‖crossingEdgePulseResidual ε x‖)
    (hfree : ‖crossingEdgePulseResidual 0 z‖ =
      ‖crossingEdgePulseResidual 0 y‖) :
    ‖crossingLeakage (z : TileHilbert Vertex)‖ ≤
      512 * |ε| * ‖(x : TileHilbert Vertex)‖ := by
  have hgap :
      crossingGapCandidate *
          ‖crossingLeakage (z : TileHilbert Vertex)‖ ≤
        ‖crossingEdgePulseResidual 0 z‖ := by
    simpa only [crossingEdgePulseResidual_zero] using
      (crossingReducedGapResidualEstimate_full z)
  have htotal :
      crossingGapCandidate *
          ‖crossingLeakage (z : TileHilbert Vertex)‖ ≤
        4 * |ε| * ‖(x : TileHilbert Vertex)‖ := by
    calc
      crossingGapCandidate *
          ‖crossingLeakage (z : TileHilbert Vertex)‖ ≤
          ‖crossingEdgePulseResidual 0 z‖ := hgap
      _ = ‖crossingEdgePulseResidual 0 y‖ := hfree
      _ ≤ 4 * |ε| * ‖(x : TileHilbert Vertex)‖ :=
        crossingEdgePulse_switch_off_residual_bound
          ε x y hx hnorm hpulse
  change (1 / 128 : ℝ) *
      ‖crossingLeakage (z : TileHilbert Vertex)‖ ≤
    4 * |ε| * ‖(x : TileHilbert Vertex)‖ at htotal
  nlinarith

/-- A supplied family of norm-preserving, domain-preserving,
unperturbed-Hamiltonian-intertwining real maps models the
post-pulse free segment. Its residual conservation follows
from intertwining rather than being separately assumed.

The result applies at *every* free evolution time τ, still
without constructing the complex Schrödinger propagator. -/
theorem crossingEdgePulse_then_free_family_leakage_bound
    (ε : ℝ) (x y : infiniteOnsiteDomain potential)
    (hx : onsitePlusBounded potential
        (ringInteraction crossingParameter) x =
          crossingEnergy • (x : TileHilbert Vertex))
    (hnorm : ‖(y : TileHilbert Vertex)‖ =
      ‖(x : TileHilbert Vertex)‖)
    (hpulse : ‖crossingEdgePulseResidual ε y‖ =
      ‖crossingEdgePulseResidual ε x‖)
    (Ufree : ℝ → TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hdom : ∀ τ : ℝ, ∀ v : infiniteOnsiteDomain potential,
      Ufree τ (v : TileHilbert Vertex) ∈ infiniteOnsiteDomain potential)
    (hcomm : ∀ τ : ℝ, ∀ v : infiniteOnsiteDomain potential,
      onsitePlusBounded potential
          (ringInteraction crossingParameter)
          ⟨Ufree τ (v : TileHilbert Vertex), hdom τ v⟩ =
        Ufree τ (onsitePlusBounded potential
          (ringInteraction crossingParameter) v))
    (hiso : ∀ τ : ℝ, ∀ v : TileHilbert Vertex,
      ‖Ufree τ v‖ = ‖v‖)
    (τ : ℝ) :
    ‖crossingLeakage (Ufree τ (y : TileHilbert Vertex))‖ ≤
      512 * |ε| * ‖(x : TileHilbert Vertex)‖ := by
  have hcomm0 :
      ∀ v : infiniteOnsiteDomain potential,
        onsitePlusBounded potential
          (ringInteraction crossingParameter + (0 : ℝ) • crossingEdge)
          ⟨Ufree τ (v : TileHilbert Vertex), hdom τ v⟩ =
        Ufree τ (onsitePlusBounded potential
          (ringInteraction crossingParameter + (0 : ℝ) • crossingEdge) v) := by
    intro v
    simpa only [zero_smul, add_zero] using hcomm τ v
  let z : infiniteOnsiteDomain potential :=
    ⟨Ufree τ (y : TileHilbert Vertex), hdom τ y⟩
  have hfree :
      ‖crossingEdgePulseResidual 0 z‖ =
        ‖crossingEdgePulseResidual 0 y‖ :=
    crossingPulseResidual_norm_conserved
      0 (Ufree τ) (hdom τ) hcomm0 (hiso τ) y
  exact crossingEdgePulse_then_free_leakage_bound
    ε x y z hx hnorm hpulse hfree

/-- A complete abstract ON/OFF protocol:
first evolve under the selected edge at strength ε, then
switch to the original Hamiltonian, allowing arbitrary
durations for both segments.

Each segment is explicitly assumed to act by an isometry,
preserve the common natural domain, and intertwine its
*own* fixed generator; the actual complex propagators
and A/B reachability remain open. -/
theorem crossingEdgePulse_on_off_uniform_leakage_bound
    (ε : ℝ)
    (Upulse Ufree : ℝ → TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hpdom : ∀ τ : ℝ, ∀ v : infiniteOnsiteDomain potential,
      Upulse τ (v : TileHilbert Vertex) ∈ infiniteOnsiteDomain potential)
    (hpcomm : ∀ τ : ℝ, ∀ v : infiniteOnsiteDomain potential,
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge)
          ⟨Upulse τ (v : TileHilbert Vertex), hpdom τ v⟩ =
        Upulse τ (onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) v))
    (hpisom : ∀ τ : ℝ, ∀ v : TileHilbert Vertex,
      ‖Upulse τ v‖ = ‖v‖)
    (hfdom : ∀ τ : ℝ, ∀ v : infiniteOnsiteDomain potential,
      Ufree τ (v : TileHilbert Vertex) ∈ infiniteOnsiteDomain potential)
    (hfcomm : ∀ τ : ℝ, ∀ v : infiniteOnsiteDomain potential,
      onsitePlusBounded potential
          (ringInteraction crossingParameter)
          ⟨Ufree τ (v : TileHilbert Vertex), hfdom τ v⟩ =
        Ufree τ (onsitePlusBounded potential
          (ringInteraction crossingParameter) v))
    (hfisom : ∀ τ : ℝ, ∀ v : TileHilbert Vertex,
      ‖Ufree τ v‖ = ‖v‖)
    (x : infiniteOnsiteDomain potential)
    (hx : onsitePlusBounded potential
        (ringInteraction crossingParameter) x =
          crossingEnergy • (x : TileHilbert Vertex))
    (pulseTime freeTime : ℝ) :
    ‖crossingLeakage
        (Ufree freeTime (Upulse pulseTime (x : TileHilbert Vertex)))‖ ≤
      512 * |ε| * ‖(x : TileHilbert Vertex)‖ := by
  let y : infiniteOnsiteDomain potential :=
    ⟨Upulse pulseTime (x : TileHilbert Vertex), hpdom pulseTime x⟩
  have hnorm :
      ‖(y : TileHilbert Vertex)‖ =
        ‖(x : TileHilbert Vertex)‖ :=
    hpisom pulseTime (x : TileHilbert Vertex)
  have hpulse :
      ‖crossingEdgePulseResidual ε y‖ =
        ‖crossingEdgePulseResidual ε x‖ :=
    crossingPulseResidual_norm_conserved
      ε (Upulse pulseTime) (hpdom pulseTime)
        (hpcomm pulseTime) (hpisom pulseTime) x
  exact crossingEdgePulse_then_free_family_leakage_bound
    ε x y hx hnorm hpulse Ufree hfdom hfcomm hfisom freeTime

end
end SpectralGeometry.AmmannBeenker
