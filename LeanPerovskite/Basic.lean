/-
# Lean Perovskite

Initial formalization scaffold for quantitative specifications related to
perovskite quantum light emission.

The first target is the relationship between exciton coherence, radiative
lifetime, and photon indistinguishability.

Scientific measurements are represented as inputs to stated specifications.
Lean verifies consequences of those specifications.
-/

import Mathlib

namespace LeanPerovskite

/-- Measurable timing quantities for a quantum emitter. -/
structure Emitter where
  T1 : ℝ
  T2 : ℝ
  T1_pos : 0 < T1
  T2_pos : 0 < T2

/-- Normalized coherence ratio relative to the transform limit `T2 = 2 * T1`. -/
noncomputable def coherenceRatio (q : Emitter) : ℝ :=
  q.T2 / (2 * q.T1)

/-- The emitter satisfies the transform-limit specification. -/
def TransformLimited (q : Emitter) : Prop :=
  q.T2 = 2 * q.T1

/-
Next target:

State the physically useful relationship connecting coherence, radiative
lifetime, and photon indistinguishability exactly as supported by the
scientific source, then prove its consequences here.

Do not treat an experimental relationship as a Lean-derived physical law:
the physical specification is an explicit hypothesis/input.
-/

end LeanPerovskite
