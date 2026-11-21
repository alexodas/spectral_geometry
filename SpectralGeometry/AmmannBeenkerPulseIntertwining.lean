module

public import SpectralGeometry.AmmannBeenkerPulseResidualBound

public section

/-!
# Intertwining evolution implies residual conservation during a fixed pulse

The previous graph-specific result bounds off-qubit leakage under
two conservation laws. Here we derive the *second* law from a precise
operator-theoretic hypothesis: a norm-preserving continuous real-linear
evolution must preserve the full natural domain and commute with
the fixed edge-perturbed Hamiltonian on that domain.

Under these conditions, its shifted-Hamiltonian residual is
intertwined automatically, so the 512|ε| leakage bound applies to
every time of such a family without any duration-dependent factor.

The physical complex Schrödinger propagator is **not** constructed
here. A real-linear isometry on the real amplitude Hilbert space is
an abstract intermediate object, not automatically the physical
complex quantum evolution.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- Intertwining the *unbounded* graph operator on its natural domain
automatically intertwines the shifted crossing-energy residual.
Domain invariance is an explicit hypothesis, not silently assumed. -/
theorem crossingPulseResidual_intertwines
    (ε : ℝ)
    (U : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hdom : ∀ x : infiniteOnsiteDomain potential,
      U (x : TileHilbert Vertex) ∈ infiniteOnsiteDomain potential)
    (hcomm : ∀ x : infiniteOnsiteDomain potential,
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge)
          ⟨U (x : TileHilbert Vertex), hdom x⟩ =
        U (onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x))
    (x : infiniteOnsiteDomain potential) :
    crossingEdgePulseResidual ε
        ⟨U (x : TileHilbert Vertex), hdom x⟩ =
      U (crossingEdgePulseResidual ε x) := by
  unfold crossingEdgePulseResidual
  rw [hcomm x]
  change
    U (onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge) x) -
      crossingEnergy • U (x : TileHilbert Vertex) =
    U (onsitePlusBounded potential
        (ringInteraction crossingParameter + ε • crossingEdge) x -
          crossingEnergy • (x : TileHilbert Vertex))
  rw [map_sub, map_smul]

/-- An isometry intertwining the edge-perturbed Hamiltonian
preserves the norm of the *entire shifted residual*. The
conservation hypothesis of the preceding pulse theorem
therefore follows rather than being independently postulated. -/
theorem crossingPulseResidual_norm_conserved
    (ε : ℝ)
    (U : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hdom : ∀ x : infiniteOnsiteDomain potential,
      U (x : TileHilbert Vertex) ∈ infiniteOnsiteDomain potential)
    (hcomm : ∀ x : infiniteOnsiteDomain potential,
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge)
          ⟨U (x : TileHilbert Vertex), hdom x⟩ =
        U (onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x))
    (hU : ∀ z : TileHilbert Vertex, ‖U z‖ = ‖z‖)
    (x : infiniteOnsiteDomain potential) :
    ‖crossingEdgePulseResidual ε
        ⟨U (x : TileHilbert Vertex), hdom x⟩‖ =
      ‖crossingEdgePulseResidual ε x‖ := by
  rw [crossingPulseResidual_intertwines ε U hdom hcomm x, hU]

/-- Full-graph leakage bound for any domain-preserving real-linear
isometry intertwining the *fixed selected-edge* Hamiltonian.

The theorem now requires only the structural properties of the
evolution (isometry, domain invariance, commutation), not a
separate residual-conservation assumption. The evolution itself
is still a supplied object. -/
theorem crossingPulseIntertwining_leakage_bound
    (ε : ℝ)
    (U : TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hdom : ∀ x : infiniteOnsiteDomain potential,
      U (x : TileHilbert Vertex) ∈ infiniteOnsiteDomain potential)
    (hcomm : ∀ x : infiniteOnsiteDomain potential,
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge)
          ⟨U (x : TileHilbert Vertex), hdom x⟩ =
        U (onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x))
    (hU : ∀ z : TileHilbert Vertex, ‖U z‖ = ‖z‖)
    (x : infiniteOnsiteDomain potential)
    (hx : onsitePlusBounded potential
        (ringInteraction crossingParameter) x =
          crossingEnergy • (x : TileHilbert Vertex)) :
    ‖crossingLeakage (U (x : TileHilbert Vertex))‖ ≤
      512 * |ε| * ‖(x : TileHilbert Vertex)‖ := by
  have hnorm :
      ‖((⟨U (x : TileHilbert Vertex), hdom x⟩ :
          infiniteOnsiteDomain potential) : TileHilbert Vertex)‖ =
        ‖(x : TileHilbert Vertex)‖ :=
    hU (x : TileHilbert Vertex)
  have hres :
      ‖crossingEdgePulseResidual ε
        ⟨U (x : TileHilbert Vertex), hdom x⟩‖ =
      ‖crossingEdgePulseResidual ε x‖ :=
    crossingPulseResidual_norm_conserved ε U hdom hcomm hU x
  exact crossingConservedPulseResidual_leakage_bound ε x
    ⟨U (x : TileHilbert Vertex), hdom x⟩ hx hnorm hres

/-- The leakage bound is uniform over *every real time parameter*
for any supplied family of domain-preserving, Hamiltonian-intertwining
isometries. No continuity, group law, differentiability or generator
identity is claimed for the family; these are future obligations for
the physical complex unitary propagator. -/
theorem crossingPulseFamily_uniform_leakage_bound
    (ε : ℝ)
    (U : ℝ → TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hdom : ∀ τ : ℝ, ∀ x : infiniteOnsiteDomain potential,
      U τ (x : TileHilbert Vertex) ∈ infiniteOnsiteDomain potential)
    (hcomm : ∀ τ : ℝ, ∀ x : infiniteOnsiteDomain potential,
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge)
          ⟨U τ (x : TileHilbert Vertex), hdom τ x⟩ =
        U τ (onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x))
    (hU : ∀ τ : ℝ, ∀ z : TileHilbert Vertex,
      ‖U τ z‖ = ‖z‖)
    (x : infiniteOnsiteDomain potential)
    (hx : onsitePlusBounded potential
        (ringInteraction crossingParameter) x =
          crossingEnergy • (x : TileHilbert Vertex))
    (τ : ℝ) :
    ‖crossingLeakage (U τ (x : TileHilbert Vertex))‖ ≤
      512 * |ε| * ‖(x : TileHilbert Vertex)‖ :=
  crossingPulseIntertwining_leakage_bound
    ε (U τ) (hdom τ) (hcomm τ) (hU τ) x hx

/-- As above, a normalized initial crossing vector has squared
leakage at most (512|ε|)^2 for every time, independently of
the duration of the constant-strength pulse. -/
theorem crossingPulseFamily_uniform_leakage_sq_bound
    (ε : ℝ)
    (U : ℝ → TileHilbert Vertex →L[ℝ] TileHilbert Vertex)
    (hdom : ∀ τ : ℝ, ∀ x : infiniteOnsiteDomain potential,
      U τ (x : TileHilbert Vertex) ∈ infiniteOnsiteDomain potential)
    (hcomm : ∀ τ : ℝ, ∀ x : infiniteOnsiteDomain potential,
      onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge)
          ⟨U τ (x : TileHilbert Vertex), hdom τ x⟩ =
        U τ (onsitePlusBounded potential
          (ringInteraction crossingParameter + ε • crossingEdge) x))
    (hU : ∀ τ : ℝ, ∀ z : TileHilbert Vertex,
      ‖U τ z‖ = ‖z‖)
    (x : infiniteOnsiteDomain potential)
    (hx : onsitePlusBounded potential
        (ringInteraction crossingParameter) x =
          crossingEnergy • (x : TileHilbert Vertex))
    (hunit : ‖(x : TileHilbert Vertex)‖ = 1)
    (τ : ℝ) :
    ‖crossingLeakage (U τ (x : TileHilbert Vertex))‖ ^ 2 ≤
      (512 * |ε|) ^ 2 := by
  have h := crossingPulseFamily_uniform_leakage_bound
    ε U hdom hcomm hU x hx τ
  rw [hunit, mul_one] at h
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (by norm_num) (abs_nonneg ε))).mpr h

end
end SpectralGeometry.AmmannBeenker
