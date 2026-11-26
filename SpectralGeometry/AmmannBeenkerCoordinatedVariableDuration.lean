module

public import SpectralGeometry.AmmannBeenkerCoordinatedExactPreparation

public section

/-!
# Three coordinated pulses of a common positive duration

The existing physical pulses are used at their actual strengths and
local times. The clock is clamped to the duration of each segment.
The full natural-domain equations are asserted only on open segments.
-/

namespace SpectralGeometry.AmmannBeenker

noncomputable section

open Filter Set
open scoped Topology

@[expose] def coordinatedDurationClock (k s : ℝ) : ℝ := min (max s 0) k

theorem coordinatedDurationClock_zero {k s : ℝ} (hk : 0 ≤ k) (hs : s ≤ 0) :
    coordinatedDurationClock k s = 0 := by
  simp [coordinatedDurationClock, max_eq_right hs, min_eq_left hk]

theorem coordinatedDurationClock_end {k s : ℝ} (hk : 0 ≤ k) (hs : k ≤ s) :
    coordinatedDurationClock k s = k := by
  rw [coordinatedDurationClock, max_eq_left (hk.trans hs), min_eq_right hs]

theorem coordinatedDurationClock_inside {k s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ k) :
    coordinatedDurationClock k s = s := by
  rw [coordinatedDurationClock, max_eq_left h0, min_eq_left h1]

theorem coordinatedDurationClock_continuous (k : ℝ) :
    Continuous (coordinatedDurationClock k) := by
  unfold coordinatedDurationClock
  exact (continuous_id.max continuous_const).min continuous_const

/-- Actual strengths are p, -2*t, q; each segment has duration k. -/
@[expose] def coordinatedDurationProtocol (k p t q : ℝ) (w : ℂ × ℂ)
    (s : ℝ) : ℂ × ℂ :=
  coordinatedPulseZ q (coordinatedDurationClock k (s-2*k))
    (coordinatedPulseX (-2*t) (coordinatedDurationClock k (s-k))
      (coordinatedPulseZ p (coordinatedDurationClock k s) w))

theorem coordinatedDurationProtocol_first (k p t q : ℝ) (w : ℂ × ℂ)
    {s : ℝ} (hk : 0 ≤ k) (h0 : 0 ≤ s) (h1 : s ≤ k) :
    coordinatedDurationProtocol k p t q w s = coordinatedPulseZ p s w := by
  rw [coordinatedDurationProtocol,
    coordinatedDurationClock_zero hk (by linarith : s-2*k ≤ 0),
    coordinatedDurationClock_zero hk (by linarith : s-k ≤ 0),
    coordinatedDurationClock_inside h0 h1, coordinatedPulseX_initial,
    coordinatedPulseZ_initial]

theorem coordinatedDurationProtocol_second (k p t q : ℝ) (w : ℂ × ℂ)
    {s : ℝ} (hk : 0 ≤ k) (h1 : k ≤ s) (h2 : s ≤ 2*k) :
    coordinatedDurationProtocol k p t q w s =
      coordinatedPulseX (-2*t) (s-k) (coordinatedPulseZ p k w) := by
  rw [coordinatedDurationProtocol,
    coordinatedDurationClock_zero hk (by linarith : s-2*k ≤ 0),
    coordinatedDurationClock_inside (by linarith : 0 ≤ s-k)
      (by linarith : s-k ≤ k),
    coordinatedDurationClock_end hk h1, coordinatedPulseZ_initial]

theorem coordinatedDurationProtocol_third (k p t q : ℝ) (w : ℂ × ℂ)
    {s : ℝ} (hk : 0 ≤ k) (h2 : 2*k ≤ s) (h3 : s ≤ 3*k) :
    coordinatedDurationProtocol k p t q w s =
      coordinatedPulseZ q (s-2*k)
        (coordinatedPulseX (-2*t) k (coordinatedPulseZ p k w)) := by
  rw [coordinatedDurationProtocol,
    coordinatedDurationClock_inside (by linarith : 0 ≤ s-2*k)
      (by linarith : s-2*k ≤ k),
    coordinatedDurationClock_end hk (by linarith : k ≤ s-k),
    coordinatedDurationClock_end hk (by linarith : k ≤ s)]

theorem coordinatedDurationProtocol_initial (k p t q : ℝ) (w : ℂ × ℂ)
    (hk : 0 ≤ k) :
    coordinatedDurationProtocol k p t q w 0 = w := by
  rw [coordinatedDurationProtocol_first k p t q w hk (le_refl 0) hk,
    coordinatedPulseZ_initial]

theorem coordinatedDurationProtocol_final (k p t q : ℝ) (w : ℂ × ℂ)
    (hk : 0 ≤ k) :
    coordinatedDurationProtocol k p t q w (3*k) =
      coordinatedPulseZ q k (coordinatedPulseX (-2*t) k (coordinatedPulseZ p k w)) := by
  rw [coordinatedDurationProtocol_third k p t q w hk (by linarith) (le_refl _),
    show 3*k-2*k = k by ring]

theorem coordinatedDurationProtocol_continuous (k p t q : ℝ) (w : ℂ × ℂ) :
    Continuous (coordinatedDurationProtocol k p t q w) := by
  unfold coordinatedDurationProtocol
  have h0 : Continuous (fun s : ℝ => coordinatedDurationClock k s) :=
    coordinatedDurationClock_continuous k
  have h1 : Continuous (fun s : ℝ => coordinatedDurationClock k (s-k)) :=
    (coordinatedDurationClock_continuous k).comp (continuous_id.sub continuous_const)
  have h2 : Continuous (fun s : ℝ => coordinatedDurationClock k (s-2*k)) :=
    (coordinatedDurationClock_continuous k).comp (continuous_id.sub continuous_const)
  exact coordinatedPulseZ_continuous q _ _ h2
    (coordinatedPulseX_continuous (-2*t) _ _ h1
      (coordinatedPulseZ_continuous p _ _ h0 continuous_const))

theorem coordinatedDurationProtocol_state_continuous (k p t q : ℝ) (w : ℂ × ℂ) :
    Continuous (fun s => coordinatedStateReal (coordinatedDurationProtocol k p t q w s)) ∧
    Continuous (fun s => coordinatedStateImag (coordinatedDurationProtocol k p t q w s)) := by
  have hc := coordinatedDurationProtocol_continuous k p t q w
  have ha : Continuous (fun s : ℝ => (coordinatedDurationProtocol k p t q w s).1) := hc.fst
  have hb : Continuous (fun s : ℝ => (coordinatedDurationProtocol k p t q w s).2) := hc.snd
  unfold coordinatedStateReal coordinatedStateImag coordinatedEmbedReal coordinatedEmbedImag
  exact ⟨((Complex.continuous_re.comp ha).smul continuous_const).add
      ((Complex.continuous_re.comp hb).smul continuous_const),
    ((Complex.continuous_im.comp ha).smul continuous_const).add
      ((Complex.continuous_im.comp hb).smul continuous_const)⟩

theorem coordinatedDurationProtocol_weight (k p t q : ℝ) (w : ℂ × ℂ) (s : ℝ) :
    coordinatedStateWeight (coordinatedDurationProtocol k p t q w s) =
      coordinatedStateWeight w := by
  simp only [coordinatedDurationProtocol, coordinatedPulseZ_weight, coordinatedPulseX_weight]

theorem coordinatedDurationProtocol_solves_first (k p t q : ℝ) (w : ℂ × ℂ)
    {s : ℝ} (hk : 0 ≤ k) (h0 : 0 < s) (h1 : s < k) :
    coordinatedSolvesAt 0 p (coordinatedDurationProtocol k p t q w) s := by
  apply coordinatedSolvesAt_congr 0 p (fun τ => coordinatedPulseZ p τ w)
    (coordinatedDurationProtocol k p t q w) s (coordinatedPulseZ_solvesAt p w s)
  filter_upwards [Ioo_mem_nhds h0 h1] with τ hτ
  exact (coordinatedDurationProtocol_first k p t q w hk hτ.1.le hτ.2.le).symm

theorem coordinatedDurationProtocol_solves_second (k p t q : ℝ) (w : ℂ × ℂ)
    {s : ℝ} (hk : 0 ≤ k) (h1 : k < s) (h2 : s < 2*k) :
    coordinatedSolvesAt (-2*t) 0 (coordinatedDurationProtocol k p t q w) s := by
  apply coordinatedSolvesAt_congr (-2*t) 0
    (fun τ => coordinatedPulseX (-2*t) (τ-k) (coordinatedPulseZ p k w))
    (coordinatedDurationProtocol k p t q w) s
  · exact coordinatedSolvesAt_shift _ _ _ k s
      (coordinatedPulseX_solvesAt (-2*t) (coordinatedPulseZ p k w) (s-k))
  · filter_upwards [Ioo_mem_nhds h1 h2] with τ hτ
    exact (coordinatedDurationProtocol_second k p t q w hk hτ.1.le hτ.2.le).symm

theorem coordinatedDurationProtocol_solves_third (k p t q : ℝ) (w : ℂ × ℂ)
    {s : ℝ} (hk : 0 ≤ k) (h2 : 2*k < s) (h3 : s < 3*k) :
    coordinatedSolvesAt 0 q (coordinatedDurationProtocol k p t q w) s := by
  apply coordinatedSolvesAt_congr 0 q
    (fun τ => coordinatedPulseZ q (τ-2*k)
      (coordinatedPulseX (-2*t) k (coordinatedPulseZ p k w)))
    (coordinatedDurationProtocol k p t q w) s
  · exact coordinatedSolvesAt_shift _ _ _ (2*k) s
      (coordinatedPulseZ_solvesAt q
        (coordinatedPulseX (-2*t) k (coordinatedPulseZ p k w)) (s-2*k))
  · filter_upwards [Ioo_mem_nhds h2 h3] with τ hτ
    exact (coordinatedDurationProtocol_third k p t q w hk hτ.1.le hτ.2.le).symm

/-- The accumulated scalar phase of three physical pulses. -/
@[expose] def coordinatedDurationAngle (k p t q : ℝ) : ℝ :=
  -(crossingEnergy + q)*k + -(crossingEnergy - t)*k + -(crossingEnergy + p)*k

private theorem durationScaledMatrix_mul (z u : ℂ)
    (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    (z • M) * (u • N) = (z * u) • (M * N) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem coordinatedDurationMatrix_rotation (k p t q : ℝ) :
    coordinatedZAxisMatrix q k * coordinatedXAxisMatrix (-2*t) k *
      coordinatedZAxisMatrix p k =
    coordinatedPhase (coordinatedDurationAngle k p t q) •
      (coordinatedRotationZ (q*k) * coordinatedRotationX (t*k) *
        coordinatedRotationZ (p*k)) := by
  rw [coordinatedZAxisMatrix_rotation q k, coordinatedXAxisMatrix_rotation,
    coordinatedZAxisMatrix_rotation p k]
  rw [show -(-2*t)*k/2 = t*k by ring,
    show -(crossingEnergy + (-2*t)/2)*k = -(crossingEnergy-t)*k by ring]
  rw [durationScaledMatrix_mul, durationScaledMatrix_mul]
  unfold coordinatedDurationAngle
  rw [coordinatedPhase_add, coordinatedPhase_add]

/-- With reciprocally rescaled strengths the endpoint realizes the same
Euler rotation, retaining the scalar phase of the longer protocol. -/
theorem coordinatedDurationProtocol_final_scaled (k p t q : ℝ) (w : ℂ × ℂ)
    (hk : 0 < k) :
    coordinatedDurationProtocol k (p/k) (t/k) (q/k) w (3*k) =
      let v := coordinatedApplyPair
        (coordinatedRotationZ q * coordinatedRotationX t * coordinatedRotationZ p) w.1 w.2
      let z := coordinatedPhase (coordinatedDurationAngle k (p/k) (t/k) (q/k))
      (z*v.1,z*v.2) := by
  rw [coordinatedDurationProtocol_final k (p/k) (t/k) (q/k) w hk.le]
  unfold coordinatedPulseX coordinatedPulseZ
  rw [coordinatedApplyPair_mul, coordinatedApplyPair_mul,
    coordinatedDurationMatrix_rotation, coordinatedApplyPair_smul]
  have hp : p/k*k = p := by field_simp [ne_of_gt hk]
  have ht : t/k*k = t := by field_simp [ne_of_gt hk]
  have hq : q/k*k = q := by field_simp [ne_of_gt hk]
  rw [hp, ht, hq]

theorem coordinatedDurationAngle_scaled (k p t q : ℝ) (hk : 0 < k) :
    coordinatedDurationAngle k (p/k) (t/k) (q/k) =
      -3*k*crossingEnergy + t-p-q := by
  unfold coordinatedDurationAngle
  field_simp [ne_of_gt hk] <;> ring

end
end SpectralGeometry.AmmannBeenker
