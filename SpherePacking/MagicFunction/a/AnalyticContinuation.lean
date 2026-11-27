/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.AnalyticContinuation
public import SpherePacking.MagicFunction.a.Schwartz

/-!
# Analytic continuation of `a`

The asymptotic expansion of `φ₀(i/t) t²` as `t → ∞`, and the identity `ψ(it) = t² φ₀(i/t)` for
`ψ(z) = -z² φ₀(-1/z)`, the function to which the analytic continuation of Laplace transforms is
applied.
-/

@[expose] public section

open Set Filter MeasureTheory Real Complex MagicFunction.DoubleZeroes Finset

namespace MagicFunction

/-- `φ₀(i/t) t² = 36/π² e^{2πt} - 8640/π t + 18144/π² + O(t² e^{-2πt})` as `t → ∞`. -/
theorem φ₀''_I_div_mul_sq_sub_isBigO_atTop :
    (fun t : ℝ ↦ φ₀'' (I / t) * t ^ 2 -
      (36 / π ^ 2 * cexp (2 * π * t) - 8640 / π * t + 18144 / π ^ 2)) =O[atTop]
        fun t ↦ t ^ 2 * rexp (-2 * π * t) := by
  sorry

/-- `ψ(it) = t² φ₀(i/t)` for `ψ(z) = -z² φ₀(-1/z)`. -/
theorem neg_sq_mul_φ₀''_neg_inv_I_mul (t : ℝ) :
    -(I * t) ^ 2 * φ₀'' (-1 / (I * t)) = φ₀'' (I / t) * t ^ 2 := by
  /- This is used to rewrite `φ₀(i/t) t²` as `ψ(it)`, in order to apply the analytic continuation
    of Laplace transforms (FGH Proposition 2.1, see `MagicFunction.DoubleZeroes`) to `a`. -/
  have h : -1 / (I * t) = I / t := by simp [div_eq_mul_inv, Complex.inv_I, mul_comm]
  rw [h, mul_pow, I_sq]
  ring

/-- `t ↦ ψ(it)` is locally integrable on `[0, ∞)`, for `ψ(z) = -z² φ₀(-1/z)`. -/
theorem locallyIntegrableOn_φ₀'' :
    LocallyIntegrableOn (fun t : ℝ ↦ -(I * t) ^ 2 * φ₀'' (-1 / (I * t))) (Ici 0) := by
  sorry

theorem expPoly_φ₀'' (t : ℝ) :
    expPoly 1 (fun k ↦ if k = 0 then 18144 / π ^ 2 else 36 / π ^ 2)
      (fun k ↦ if k = 0 then -8640 / π else 0) t =
        36 / π ^ 2 * cexp (2 * π * t) - 8640 / π * t + 18144 / π ^ 2 := by
  simp [sum_range_succ]
  ring

theorem φ₀''_sub_expPoly_isBigO_atTop :
    (fun t : ℝ ↦ -(I * t) ^ 2 * φ₀'' (-1 / (I * t)) -
      expPoly 1 (fun k ↦ if k = 0 then 18144 / π ^ 2 else 36 / π ^ 2)
        (fun k ↦ if k = 0 then -8640 / π else 0) t) =O[atTop] fun t ↦ rexp (-π * t) := by
  have h : (fun t : ℝ ↦ t ^ 2 * rexp (-2 * π * t)) =O[atTop] fun t ↦ rexp (-π * t) :=
    ((isLittleO_pow_exp_pos_mul_atTop 2 pi_pos).isBigO.mul
      (Asymptotics.isBigO_refl _ _)).congr_right fun t ↦ by rw [← Real.exp_add]; ring_nf
  refine (φ₀''_I_div_mul_sq_sub_isBigO_atTop.trans h).congr_left fun t ↦ ?_
  rw [neg_sq_mul_φ₀''_neg_inv_I_mul, expPoly_φ₀'']

/-- The integral in Proposition 7.20 converges absolutely for `s > 2`. -/
theorem integrableOn_φ₀''_I_div_mul_sq_mul_cexp {s : ℝ} (hs : 2 < s) :
    IntegrableOn (fun t : ℝ ↦ φ₀'' (I / t) * t ^ 2 * cexp (-π * s * t)) (Ioi 0) := by
  refine (integrableOn_mul_cexp (ψ := fun z ↦ -z ^ 2 * φ₀'' (-1 / z)) (s := s) pi_pos ?_
    locallyIntegrableOn_φ₀'' φ₀''_sub_expPoly_isBigO_atTop).congr_fun
      (fun t _ ↦ by simp only [neg_sq_mul_φ₀''_neg_inv_I_mul]) measurableSet_Ioi
  simpa using hs

/-- Proposition 7.20: `a(s) = 4i sin(πs/2)² ∫₀^∞ φ₀(i/t) t² e^{-πst} dt` for `s > 2`. -/
theorem a'_eq_four_mul_I_mul_sin_sq_mul_integral {s : ℝ} (hs : 2 < s) :
    a.RealIntegrals.a' s = 4 * I * (Real.sin (π * s / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), φ₀'' (I / t) * t ^ 2 * cexp (-π * s * t) := by
  sorry

theorem a_eq_four_mul_I_mul_sin_sq_mul_integral {x : EuclideanSpace ℝ (Fin 8)} (hx : √2 < ‖x‖) :
    FourierEigenfunctions.a x = 4 * I * (Real.sin (π * ‖x‖ ^ 2 / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), φ₀'' (I / t) * t ^ 2 * cexp (-π * ‖x‖ ^ 2 * t) := by
  rw [FourierEigenfunctions.a_apply,
    a'_eq_four_mul_I_mul_sin_sq_mul_integral (lt_sq_of_sqrt_lt hx)]
  norm_num

/-- The integral in Proposition 7.21 converges absolutely for `s ≥ 0`. -/
theorem integrableOn_φ₀''_I_div_mul_sq_sub_mul_cexp {s : ℝ} (hs : 0 ≤ s) :
    IntegrableOn (fun t : ℝ ↦ (φ₀'' (I / t) * t ^ 2 -
      (36 / π ^ 2 * cexp (2 * π * t) - 8640 / π * t + 18144 / π ^ 2)) * cexp (-π * s * t))
        (Ioi 0) := by
  refine (integrableOn_sub_expPoly_mul_cexp (ψ := fun z ↦ -z ^ 2 * φ₀'' (-1 / z)) (s := s) ?_
    locallyIntegrableOn_φ₀'' φ₀''_sub_expPoly_isBigO_atTop).congr_fun
      (fun t _ ↦ by simp only [neg_sq_mul_φ₀''_neg_inv_I_mul, expPoly_φ₀'']) measurableSet_Ioi
  rw [neg_div, div_self pi_ne_zero, ofReal_re]
  linarith

/-- Proposition 7.21: for `s ≥ 0`,
`a(s) = 4i sin(πs/2)² (36/(π³(s - 2)) - 8640/(π³s²) + 18144/(π³s) + ∫₀^∞ (t² φ₀(i/t)`
`- 36/π² e^{2πt} + 8640/π t - 18144/π²) e^{-πst} dt)`, with the removable singularities at
`s = 0, 2` removed. In the notation of FGH Proposition 2.2, the right hand side is `4i U(s)` for
`ψ(z) = -z² φ₀(-1/z)`. -/
theorem a'_eq_four_mul_I_mul_U {s : ℝ} (hs : 0 ≤ s) :
    a.RealIntegrals.a' s = 4 * I * U (fun z ↦ -z ^ 2 * φ₀'' (-1 / z)) 1
      (fun k ↦ if k = 0 then 18144 / π ^ 2 else 36 / π ^ 2)
      (fun k ↦ if k = 0 then -8640 / π else 0) s := by
  sorry

theorem a_eq_four_mul_I_mul_U (x : EuclideanSpace ℝ (Fin 8)) :
    FourierEigenfunctions.a x = 4 * I * U (fun z ↦ -z ^ 2 * φ₀'' (-1 / z)) 1
      (fun k ↦ if k = 0 then 18144 / π ^ 2 else 36 / π ^ 2)
      (fun k ↦ if k = 0 then -8640 / π else 0) (‖x‖ ^ 2 : ℝ) := by
  rw [FourierEigenfunctions.a_apply, a'_eq_four_mul_I_mul_U (by positivity)]

end MagicFunction
