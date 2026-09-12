/-
# Lean Perovskite

Initial formalization of a quantitative coherence specification motivated by
Yitong Dong's CU seminar on interface-regulated perovskite nanocrystals.

The physical specification is supplied explicitly as a hypothesis. Lean checks
the mathematical consequences of that specification.
-/

import Mathlib

namespace LeanPerovskite

/-- Measurable timing quantities for a quantum emitter. -/
structure Emitter where
  T1 : ℝ
  T2 : ℝ
  T1_pos : 0 < T1
  T2_pos : 0 < T2

/-- Normalized coherence relative to the transform-limit relation `T2 = 2 * T1`. -/
noncomputable def coherenceRatio (q : Emitter) : ℝ :=
  q.T2 / (2 * q.T1)

/-- The transform-limit specification. -/
def TransformLimited (q : Emitter) : Prop :=
  q.T2 = 2 * q.T1

/-- Physical coherence constraint used by the initial formalization. -/
def CoherenceBounded (q : Emitter) : Prop :=
  q.T2 ≤ 2 * q.T1

theorem coherenceRatio_pos (q : Emitter) :
    0 < coherenceRatio q := by
  unfold coherenceRatio
  have hden : 0 < 2 * q.T1 := by
    exact mul_pos (by norm_num) q.T1_pos
  exact div_pos q.T2_pos hden

theorem coherenceRatio_le_one (q : Emitter)
    (h : CoherenceBounded q) :
    coherenceRatio q ≤ 1 := by
  unfold CoherenceBounded at h
  unfold coherenceRatio
  have hden : 0 < 2 * q.T1 := by
    exact mul_pos (by norm_num) q.T1_pos
  apply (div_le_iff₀ hden).2
  simpa using h

theorem coherenceRatio_bounds (q : Emitter)
    (h : CoherenceBounded q) :
    0 < coherenceRatio q ∧ coherenceRatio q ≤ 1 := by
  exact ⟨coherenceRatio_pos q, coherenceRatio_le_one q h⟩

theorem transformLimited_iff_coherenceRatio_eq_one (q : Emitter) :
    TransformLimited q ↔ coherenceRatio q = 1 := by
  unfold TransformLimited coherenceRatio
  have hden : 2 * q.T1 ≠ 0 := by
    have hpos : 0 < 2 * q.T1 := by
      exact mul_pos (by norm_num) q.T1_pos
    exact ne_of_gt hpos
  constructor
  · intro h
    rw [h]
    exact div_self hden
  · intro h
    have h' : q.T2 = 1 * (2 * q.T1) := (div_eq_iff hden).mp h
    simpa using h'

/-
Next specification

HOM visibility and stochastic-relaxation timing jitter are intentionally not
identified with `coherenceRatio` here.

The next scientific question is:

  Which assumptions on stochastic relaxation and timing jitter admit a
  quantitative bound on HOM visibility?

That relationship should be added only from a stated physical model or source.
-/

end LeanPerovskite
