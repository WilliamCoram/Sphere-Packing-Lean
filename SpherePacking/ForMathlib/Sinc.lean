/-
Copyright (c) 2026 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The complex sinc function

We define `Complex.sinc z = sin z / z` for `z ≠ 0`, with `Complex.sinc 0 = 1`. It is the complex
counterpart of `Real.sinc`, and like it equals `dslope sin 0`, so it is entire.

The contents of this file should eventually be moved to Mathlib, next to `Real.sinc`.
-/

@[expose] public section

namespace Complex

variable {z : ℂ}

/-- The function `sin z / z` modified to take the value 1 at 0, which makes it entire. -/
@[pp_nodot]
noncomputable def sinc (z : ℂ) : ℂ := if z = 0 then 1 else sin z / z

lemma sinc_apply : sinc z = if z = 0 then 1 else sin z / z := rfl

@[simp]
lemma sinc_zero : sinc 0 = 1 := by simp [sinc]

lemma sinc_of_ne_zero (hz : z ≠ 0) : sinc z = sin z / z := by simp [sinc, hz]

lemma sinc_eq_dslope : sinc = dslope sin 0 := by
  ext
  simp [dslope, Function.update_apply, sinc, slope, div_eq_inv_mul]

@[simp, norm_cast]
lemma ofReal_sinc (x : ℝ) : (Real.sinc x : ℂ) = sinc x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Real.sinc_of_ne_zero hx, sinc_of_ne_zero (ofReal_ne_zero.2 hx), ofReal_div, ofReal_sin]

/-- The function `Complex.sinc` is complex analytic. -/
@[fun_prop]
lemma analyticAt_sinc : AnalyticAt ℂ sinc z :=
  sinc_eq_dslope ▸ analyticAt_sin.dslope 0

/-- The function `Complex.sinc` is complex analytic. -/
@[fun_prop]
lemma analyticOnNhd_sinc {s : Set ℂ} : AnalyticOnNhd ℂ sinc s :=
  fun _ _ ↦ analyticAt_sinc

@[fun_prop]
lemma differentiable_sinc : Differentiable ℂ sinc :=
  fun _ ↦ analyticAt_sinc.differentiableAt

@[fun_prop]
lemma continuous_sinc : Continuous sinc :=
  differentiable_sinc.continuous

end Complex
