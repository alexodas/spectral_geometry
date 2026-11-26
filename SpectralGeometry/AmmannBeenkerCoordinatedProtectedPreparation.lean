module

public import SpectralGeometry.AmmannBeenkerCoordinatedVariableDuration

public section

/-!
# Weak coordinated preparation with prescribed spectral protection

The constructive Euler angles are divided by a common stretching factor.
The actual natural-domain pulses last that factor rather than one unit.
The registered centered isolation theorem applies separately to every
active Hamiltonian, with a prescribed fraction of the baseline gap.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

/-- Maximum combined control budget of the original unit-duration pulses. -/
@[expose] def coordinatedProtocolBudget (p t q : ℝ) : ℝ :=
  max (2*|p|) (max (2*|t|) (2*|q|))

/-- Explicit finite stretching factor, valid also for three zero angles. -/
@[expose] def coordinatedProtocolStretch (p t q ε fraction : ℝ) : ℝ :=
  1 + coordinatedProtocolBudget p t q / min ε ((1-fraction)*(1/128))

theorem coordinatedProtocolBudget_nonneg (p t q : ℝ) :
    0 ≤ coordinatedProtocolBudget p t q := by
  exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg p)).trans
    (le_max_left _ _)

theorem coordinatedStretch_bounds (B m : ℝ) (hB : 0 ≤ B) (hm : 0 < m) :
    1 ≤ 1+B/m ∧ B/(1+B/m) ≤ m := by
  have hd := div_nonneg hB hm.le
  have hk : 0 < 1+B/m := by linarith
  refine ⟨by linarith, (div_le_iff₀ hk).2 ?_⟩
  have he : m*(1+B/m) = m+B := by
    field_simp [ne_of_gt hm] <;> ring
  rw [he]
  linarith

/-- All three original budgets are bounded by the rescaled maximum. -/
theorem coordinatedProtocol_scaled_budgets (p t q k : ℝ) (hk : 0 < k) :
    |(0 : ℝ)| + 2*|p/k| ≤ coordinatedProtocolBudget p t q / k ∧
    |-2*(t/k)| + 2*|(0 : ℝ)| ≤ coordinatedProtocolBudget p t q / k ∧
    |(0 : ℝ)| + 2*|q/k| ≤ coordinatedProtocolBudget p t q / k := by
  have hp : 2*|p| ≤ coordinatedProtocolBudget p t q := le_max_left _ _
  have ht : 2*|t| ≤ coordinatedProtocolBudget p t q :=
    (le_max_left (2*|t|) (2*|q|)).trans (le_max_right _ _)
  have hq : 2*|q| ≤ coordinatedProtocolBudget p t q :=
    (le_max_right (2*|t|) (2*|q|)).trans (le_max_right _ _)
  have ep : |(0 : ℝ)| + 2*|p/k| = (2*|p|)/k := by
    rw [abs_zero, zero_add, abs_div, abs_of_pos hk]
    ring
  have et : |-2*(t/k)| + 2*|(0 : ℝ)| = (2*|t|)/k := by
    rw [abs_mul, abs_div, abs_of_pos hk, abs_zero]
    norm_num <;> ring
  have eq : |(0 : ℝ)| + 2*|q/k| = (2*|q|)/k := by
    rw [abs_zero, zero_add, abs_div, abs_of_pos hk]
    ring
  rw [ep, et, eq]
  exact ⟨div_le_div_of_nonneg_right hp hk.le,
    div_le_div_of_nonneg_right ht hk.le, div_le_div_of_nonneg_right hq hk.le⟩

/-- The constructive factor simultaneously bounds all three control
budgets by both the requested amplitude and the allowed loss of gap. -/
theorem coordinatedProtocolStretch_bounds (p t q ε fraction : ℝ)
    (hε : 0 < ε) (hf0 : 0 < fraction) (hf1 : fraction < 1) :
    let k := coordinatedProtocolStretch p t q ε fraction
    1 ≤ k ∧ coordinatedProtocolBudget p t q / k ≤ ε ∧
      coordinatedProtocolBudget p t q / k ≤ (1-fraction)*(1/128) := by
  dsimp only
  have hm : 0 < min ε ((1-fraction)*(1/128)) :=
    lt_min hε (mul_pos (sub_pos.mpr hf1) (by norm_num))
  have h := coordinatedStretch_bounds (coordinatedProtocolBudget p t q)
    (min ε ((1-fraction)*(1/128))) (coordinatedProtocolBudget_nonneg p t q) hm
  unfold coordinatedProtocolStretch
  exact ⟨h.1, h.2.trans (min_le_left _ _), h.2.trans (min_le_right _ _)⟩

/-- Full real-spectral protection for one actual control setting.
The definition includes the exact closed cluster and all eigenvectors at
the controlled energies, and separates exterior spectral energies and
energies of nonzero-leakage eigenvectors by the requested positive gap. -/
@[expose] def CoordinatedProtectedSetting (ε fraction δ η : ℝ) : Prop :=
  |δ| + 2*|η| ≤ ε ∧
  (∀ level : ℝ, CoordinatedPlaneLevel δ η level →
    level ∈ infiniteBoundedOnsiteRealSpectrum potential (coordinatedCorrection δ η) ∧
    ∀ x : infiniteOnsiteDomain potential,
      onsitePlusBounded potential (coordinatedCorrection δ η) x =
        level • (x : TileHilbert Vertex) →
      crossingLeakage (x : TileHilbert Vertex) = 0) ∧
  (∀ e : ℝ, |e-coordinatedLevelCenter δ η| ≤ coordinatedLevelRadius δ η →
    (e ∈ infiniteBoundedOnsiteRealSpectrum potential (coordinatedCorrection δ η) ↔
      CoordinatedPlaneLevel δ η e)) ∧
  (∀ e level : ℝ, CoordinatedPlaneLevel δ η level →
    e ∈ infiniteBoundedOnsiteRealSpectrum potential (coordinatedCorrection δ η) →
    ¬ CoordinatedPlaneLevel δ η e → fraction*(1/128) ≤ |e-level|) ∧
  (∀ e level : ℝ, CoordinatedPlaneLevel δ η level →
    ∀ x : infiniteOnsiteDomain potential,
      onsitePlusBounded potential (coordinatedCorrection δ η) x =
        e • (x : TileHilbert Vertex) →
      crossingLeakage (x : TileHilbert Vertex) ≠ 0 →
      fraction*(1/128) ≤ |e-level|)

theorem coordinatedProtectedSetting_of_budget (ε fraction δ η : ℝ)
    (hf0 : 0 < fraction)
    (hε : |δ| + 2*|η| ≤ ε)
    (hb : |δ| + 2*|η| ≤ (1-fraction)*(1/128)) :
    CoordinatedProtectedSetting ε fraction δ η := by
  have hsmall : |δ| + 2*|η| < (1/128 : ℝ) := by linarith
  have hc := coordinatedCluster_centered_isolation δ η
    (coordinatedCluster_centered_condition_of_budget δ η hsmall)
  have hg : fraction*(1/128) ≤
      1/128-(|δ|+2*|η|)/2-coordinatedLevelRadius δ η := by
    linarith [coordinatedCluster_centered_gap_ge δ η]
  refine ⟨hε, hc.2.1, hc.2.2.1, ?_, ?_⟩
  · intro e level hl he hne
    exact hg.trans (hc.2.2.2.1 e level hl he hne)
  · intro e level hl x he hne
    exact hg.trans (hc.2.2.2.2 e level hl x he hne)

/-- Every normalized complex target can be prepared from dark with
arbitrarily weak controls and any prescribed fraction strictly between
zero and one of the certified baseline spectral gap. The explicit common
duration is finite and at least one. The trajectory is continuous,
normalized, and exactly confined to the original compact plane, with
both real and imaginary components on the full natural domain. Each
open pulse interval satisfies the full graph Schroedinger equations.
The spectral protection applies to every active setting, including
zero controls and both choices of adjacent setting at either switch.
The endpoint retains its exact scalar phase. -/
theorem coordinatedProtocol_protected_exact_preparation (a b : ℂ)
    (hn : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (ε fraction : ℝ)
    (hε : 0 < ε) (hf0 : 0 < fraction) (hf1 : fraction < 1) :
    ∃ p t q : ℝ, 0 ≤ t ∧ t ≤ Real.pi / 2 ∧
      let k := coordinatedProtocolStretch p t q ε fraction
      let v := coordinatedDurationProtocol k (p/k) (t/k) (q/k) (1,0)
      let z := coordinatedPhase (coordinatedDurationAngle k (p/k) (t/k) (q/k))
      1 ≤ k ∧ 0 < 3*k ∧ ‖z‖ = 1 ∧
      v 0 = (1,0) ∧
      coordinatedStateReal (v 0) = crossingDark ∧
      coordinatedStateImag (v 0) = 0 ∧
      v (3*k) = (z*a,z*b) ∧
      coordinatedStateReal (v (3*k)) =
        (z*a).re • crossingDark + (z*b).re • crossingBright ∧
      coordinatedStateImag (v (3*k)) =
        (z*a).im • crossingDark + (z*b).im • crossingBright ∧
      Continuous v ∧
      Continuous (fun s => coordinatedStateReal (v s)) ∧
      Continuous (fun s => coordinatedStateImag (v s)) ∧
      (∀ s : ℝ, coordinatedStateReal (v s) ∈ infiniteOnsiteDomain potential ∧
        coordinatedStateImag (v s) ∈ infiniteOnsiteDomain potential ∧
        ‖coordinatedStateReal (v s)‖ ^ 2 + ‖coordinatedStateImag (v s)‖ ^ 2 = 1 ∧
        crossingLeakage (coordinatedStateReal (v s)) = 0 ∧
        crossingLeakage (coordinatedStateImag (v s)) = 0) ∧
      (∀ s : ℝ, 0 < s → s < k → coordinatedSolvesAt 0 (p/k) v s) ∧
      (∀ s : ℝ, k < s → s < 2*k → coordinatedSolvesAt (-2*(t/k)) 0 v s) ∧
      (∀ s : ℝ, 2*k < s → s < 3*k → coordinatedSolvesAt 0 (q/k) v s) ∧
      CoordinatedProtectedSetting ε fraction 0 (p/k) ∧
      CoordinatedProtectedSetting ε fraction (-2*(t/k)) 0 ∧
      CoordinatedProtectedSetting ε fraction 0 (q/k) := by
  obtain ⟨p,t,q,ht0,ht1,ha,hb⟩ := coordinatedEuler_reaches_from_dark a b hn
  refine ⟨p,t,q,ht0,ht1,?_⟩
  dsimp only
  let k := coordinatedProtocolStretch p t q ε fraction
  have hs : 1 ≤ k ∧ coordinatedProtocolBudget p t q / k ≤ ε ∧
      coordinatedProtocolBudget p t q / k ≤ (1-fraction)*(1/128) :=
    coordinatedProtocolStretch_bounds p t q ε fraction hε hf0 hf1
  have hk : 0 < k := by linarith [hs.1]
  let v := coordinatedDurationProtocol k (p/k) (t/k) (q/k) (1,0)
  let z := coordinatedPhase (coordinatedDurationAngle k (p/k) (t/k) (q/k))
  have hi : v 0 = (1,0) := coordinatedDurationProtocol_initial _ _ _ _ _ hk.le
  have he : v (3*k) = (z*a,z*b) := by
    dsimp [v,z]
    rw [coordinatedDurationProtocol_final_scaled k p t q (1,0) hk]
    dsimp only
    rw [coordinatedApplyPair_dark]
    dsimp only
    rw [ha,hb]
  have hc := coordinatedDurationProtocol_state_continuous k (p/k) (t/k) (q/k) (1,0)
  have budgets := coordinatedProtocol_scaled_budgets p t q k hk
  refine ⟨hs.1, by linarith, coordinatedPhase_norm _, hi, ?_, ?_, he, ?_, ?_,
    coordinatedDurationProtocol_continuous _ _ _ _ _, hc.1, hc.2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hi]
    exact coordinatedState_dark_initial.1
  · rw [hi]
    exact coordinatedState_dark_initial.2
  · rw [he]
    rfl
  · rw [he]
    rfl
  · intro s
    have hd := coordinatedState_domain (v s)
    have hl := coordinatedState_leakage_zero (v s)
    have hw : coordinatedStateWeight (v s) = 1 := by
      dsimp [v]
      rw [coordinatedDurationProtocol_weight, coordinatedStateWeight_eq]
      norm_num
    exact ⟨hd.1 ▸ (domainCoordinatedStateReal (v s)).property,
      hd.2 ▸ (domainCoordinatedStateImag (v s)).property, hw, hl.1, hl.2⟩
  · intro s h0 h1
    exact coordinatedDurationProtocol_solves_first _ _ _ _ _ hk.le h0 h1
  · intro s h1 h2
    exact coordinatedDurationProtocol_solves_second _ _ _ _ _ hk.le h1 h2
  · intro s h2 h3
    exact coordinatedDurationProtocol_solves_third _ _ _ _ _ hk.le h2 h3
  · exact coordinatedProtectedSetting_of_budget ε fraction 0 (p/k) hf0
      (budgets.1.trans hs.2.1) (budgets.1.trans hs.2.2)
  · exact coordinatedProtectedSetting_of_budget ε fraction (-2*(t/k)) 0 hf0
      (budgets.2.1.trans hs.2.1) (budgets.2.1.trans hs.2.2)
  · exact coordinatedProtectedSetting_of_budget ε fraction 0 (q/k) hf0
      (budgets.2.2.trans hs.2.1) (budgets.2.2.trans hs.2.2)

end
end SpectralGeometry.AmmannBeenker
