/-
# Lean Perovskite

Formalization of quantitative specifications motivated by Yitong Dong's
CU seminar on interface-regulated perovskite nanocrystals.

Physical specifications are supplied explicitly as hypotheses or definitions.
Lean checks the mathematical consequences of those stated specifications.

The formalization contains three layers:

1. A coherence specification based on `T2 ≤ 2 * T1`.
2. A stochastic-relaxation specification that bounds HOM visibility by

     Γ_relaxation / (Γ_relaxation + Γ_X).

3. A source-supported combined indistinguishability model in which coherence
   and stochastic-relaxation limits contribute multiplicatively.

The experimental relationships remain distinguishable from the consequences
verified by Lean.
-/

import Mathlib

namespace LeanPerovskite

/-!
## Coherence specification
-/

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

/-!
## Stochastic-relaxation HOM specification

The seminar identifies stochastic-relaxation timing jitter as a limitation on
Hong-Ou-Mandel photon indistinguishability and presents the limiting ratio

  Γ_relaxation / (Γ_relaxation + Γ_X).

The relation is treated here as a stated physical specification. Lean verifies
properties that follow from positive rates and from an explicitly supplied
HOM-visibility bound.
-/

/-- Positive rates entering the stated stochastic-relaxation visibility model. -/
structure RelaxationSpec where
  gammaRelax : ℝ
  gammaX : ℝ
  gammaRelax_pos : 0 < gammaRelax
  gammaX_pos : 0 < gammaX

/--
The relaxation-limited visibility quantity

  Γ_relaxation / (Γ_relaxation + Γ_X).
-/
noncomputable def relaxationLimit (r : RelaxationSpec) : ℝ :=
  r.gammaRelax / (r.gammaRelax + r.gammaX)

/--
A measured HOM visibility is admissible under the stated relaxation-limited
specification where it is nonnegative and does not exceed `relaxationLimit`.
-/
def HOMAdmissible (r : RelaxationSpec) (visibility : ℝ) : Prop :=
  0 ≤ visibility ∧ visibility ≤ relaxationLimit r

theorem relaxationLimit_pos (r : RelaxationSpec) :
    0 < relaxationLimit r := by
  unfold relaxationLimit
  have hden : 0 < r.gammaRelax + r.gammaX := by
    nlinarith [r.gammaRelax_pos, r.gammaX_pos]
  exact div_pos r.gammaRelax_pos hden

theorem relaxationLimit_lt_one (r : RelaxationSpec) :
    relaxationLimit r < 1 := by
  unfold relaxationLimit
  have hden : 0 < r.gammaRelax + r.gammaX := by
    nlinarith [r.gammaRelax_pos, r.gammaX_pos]
  apply (div_lt_one hden).2
  nlinarith [r.gammaX_pos]

theorem relaxationLimit_bounds (r : RelaxationSpec) :
    0 < relaxationLimit r ∧ relaxationLimit r < 1 := by
  exact ⟨relaxationLimit_pos r, relaxationLimit_lt_one r⟩

/--
Any HOM visibility admitted by the stated relaxation model is strictly below 1.
-/
theorem homVisibility_lt_one
    (r : RelaxationSpec)
    (visibility : ℝ)
    (h : HOMAdmissible r visibility) :
    visibility < 1 := by
  exact lt_of_le_of_lt h.2 (relaxationLimit_lt_one r)

/--
For fixed positive `Γ_X`, increasing the positive relaxation rate cannot
decrease the stated relaxation-limited visibility.
-/
theorem relaxationLimit_mono_gammaRelax
    {gammaRelax₁ gammaRelax₂ gammaX : ℝ}
    (hRelax₁ : 0 < gammaRelax₁)
    (hRelax₂ : 0 < gammaRelax₂)
    (hX : 0 < gammaX)
    (hRate : gammaRelax₁ ≤ gammaRelax₂) :
    gammaRelax₁ / (gammaRelax₁ + gammaX) ≤
      gammaRelax₂ / (gammaRelax₂ + gammaX) := by
  have hden₁ : 0 < gammaRelax₁ + gammaX := by
    nlinarith
  have hden₂ : 0 < gammaRelax₂ + gammaX := by
    nlinarith
  apply (div_le_div_iff₀ hden₁ hden₂).2
  have hmul : 0 ≤ (gammaRelax₂ - gammaRelax₁) * gammaX := by
    exact mul_nonneg (sub_nonneg.mpr hRate) (le_of_lt hX)
  nlinarith

/--
For fixed positive relaxation rate, increasing positive `Γ_X` cannot increase
the stated relaxation-limited visibility.
-/
theorem relaxationLimit_antitone_gammaX
    {gammaRelax gammaX₁ gammaX₂ : ℝ}
    (hRelax : 0 < gammaRelax)
    (hX₁ : 0 < gammaX₁)
    (hX₂ : 0 < gammaX₂)
    (hRate : gammaX₁ ≤ gammaX₂) :
    gammaRelax / (gammaRelax + gammaX₂) ≤
      gammaRelax / (gammaRelax + gammaX₁) := by
  have hden₁ : 0 < gammaRelax + gammaX₁ := by
    nlinarith
  have hden₂ : 0 < gammaRelax + gammaX₂ := by
    nlinarith
  apply (div_le_div_iff₀ hden₂ hden₁).2
  have hmul : 0 ≤ gammaRelax * (gammaX₂ - gammaX₁) := by
    exact mul_nonneg (le_of_lt hRelax) (sub_nonneg.mpr hRate)
  nlinarith

/-!
## Combined indistinguishability specification

A source-supported quantum-dot model combines coherence/dephasing and
stochastic-relaxation timing-jitter effects multiplicatively.

The model is represented here as

  I = C * L

where

  C = T2 / (2 * T1)

and

  L = Γ_relaxation / (Γ_relaxation + Γ_X).

This equation is treated as a stated physical model, not as a consequence
derived by Lean from the perovskite measurements.
-/

/-- Combined source-supported photon-indistinguishability model. -/
noncomputable def combinedIndistinguishability
    (q : Emitter) (r : RelaxationSpec) : ℝ :=
  coherenceRatio q * relaxationLimit r

theorem combinedIndistinguishability_pos
    (q : Emitter)
    (r : RelaxationSpec) :
    0 < combinedIndistinguishability q r := by
  unfold combinedIndistinguishability
  exact mul_pos (coherenceRatio_pos q) (relaxationLimit_pos r)

/--
Under the coherence bound, the combined indistinguishability is strictly below 1.
-/
theorem combinedIndistinguishability_lt_one
    (q : Emitter)
    (r : RelaxationSpec)
    (hq : CoherenceBounded q) :
    combinedIndistinguishability q r < 1 := by
  unfold combinedIndistinguishability
  have hCpos : 0 < coherenceRatio q := coherenceRatio_pos q
  have hCle : coherenceRatio q ≤ 1 := coherenceRatio_le_one q hq
  have hLpos : 0 < relaxationLimit r := relaxationLimit_pos r
  have hLlt : relaxationLimit r < 1 := relaxationLimit_lt_one r
  nlinarith

/--
The combined indistinguishability is strictly below the coherence factor,
because the relaxation factor is positive and strictly below 1.
-/
theorem combinedIndistinguishability_lt_coherence
    (q : Emitter)
    (r : RelaxationSpec) :
    combinedIndistinguishability q r < coherenceRatio q := by
  unfold combinedIndistinguishability
  have hCpos : 0 < coherenceRatio q := coherenceRatio_pos q
  have hLlt : relaxationLimit r < 1 := relaxationLimit_lt_one r
  nlinarith

/--
Under the coherence bound, the combined indistinguishability does not exceed
the relaxation factor.
-/
theorem combinedIndistinguishability_le_relaxation
    (q : Emitter)
    (r : RelaxationSpec)
    (hq : CoherenceBounded q) :
    combinedIndistinguishability q r ≤ relaxationLimit r := by
  unfold combinedIndistinguishability
  have hLnonneg : 0 ≤ relaxationLimit r := le_of_lt (relaxationLimit_pos r)
  have hCle : coherenceRatio q ≤ 1 := coherenceRatio_le_one q hq
  nlinarith

/--
The combined model is bounded by both component constraints:
strictly below coherence and no greater than the relaxation limit.
-/
theorem combinedIndistinguishability_component_bounds
    (q : Emitter)
    (r : RelaxationSpec)
    (hq : CoherenceBounded q) :
    combinedIndistinguishability q r < coherenceRatio q ∧
      combinedIndistinguishability q r ≤ relaxationLimit r := by
  exact ⟨
    combinedIndistinguishability_lt_coherence q r,
    combinedIndistinguishability_le_relaxation q r hq
  ⟩

/-!
## Engineering reading

Within the stated multiplicative model:

* improving coherence alone leaves indistinguishability constrained by the
  relaxation/timing-jitter factor;
* improving the relaxation factor alone leaves indistinguishability constrained
  by coherence.

The Lean results verify those mathematical consequences of the stated model.

## Next specification

The next scientific boundary is to test source-supported refinements of the
combined model against interface-regulated perovskite measurements, rather than
adding an unstated relation between the model and experimental data.
-/

end LeanPerovskite
