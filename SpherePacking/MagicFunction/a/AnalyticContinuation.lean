/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.AnalyticContinuation
public import SpherePacking.MagicFunction.a.Schwartz

import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import SpherePacking.ModularForms.PhiAsymptotics

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
  have hres (F : UpperHalfPlane → ℂ)
      (hF : F =O[UpperHalfPlane.atImInfty] fun z ↦ cexp (2 * π * I * z)) :
      F.resToImagAxis =O[atTop] fun t ↦ rexp (-(2 * π) * t) :=
    isBigO_resToImagAxis_of_isBigO_atImInfty (by positivity)
      (hF.norm_right.congr_right fun z ↦ by simp [Complex.norm_exp])
  have h12 : (fun t : ℝ ↦ t) =O[atTop] fun t ↦ t ^ 2 := by
    simpa using (Asymptotics.isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (by norm_num : 1 < 2)).isBigO
  have h02 : (fun _ : ℝ ↦ (1 : ℝ)) =O[atTop] fun t ↦ t ^ 2 := by
    simpa using (Asymptotics.isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (by norm_num : 0 < 2)).isBigO
  have hA : (fun t : ℝ ↦ (t : ℂ) ^ 2 * φ₀.resToImagAxis t) =O[atTop]
      fun t ↦ t ^ 2 * rexp (-(2 * π) * t) :=
    (Asymptotics.isBigO_of_le _ fun t ↦ by simp).mul (hres _ φ₀_isBigO)
  have hB : (fun t : ℝ ↦ (t : ℂ) * (fun z ↦ φ₂' z - 720).resToImagAxis t) =O[atTop]
      fun t ↦ t ^ 2 * rexp (-(2 * π) * t) :=
    ((Asymptotics.isBigO_of_le _ fun t ↦ by simp).trans h12).mul
      (hres _ φ₂'_sub_isBigO)
  have hC : (fun z ↦ φ₄' z - (cexp (2 * π * I * z))⁻¹ - 504).resToImagAxis =O[atTop]
      fun t ↦ t ^ 2 * rexp (-(2 * π) * t) :=
    (hres _ φ₄'_sub_isBigO).trans
      ((h02.mul (Asymptotics.isBigO_refl _ _)).congr_left fun t ↦ one_mul _)
  refine ((hA.sub (hB.const_mul_left (12 / π : ℂ))).add
    (hC.const_mul_left (36 / π ^ 2 : ℂ))).congr' ?_ (.of_forall fun t ↦ by ring_nf)
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hz : 0 < (I * (t : ℂ)).im := by simp [ht]
  have hres_eq (F : UpperHalfPlane → ℂ) : F.resToImagAxis t = F ⟨I * t, hz⟩ :=
    (ResToImagAxis.I_mul_t_eq F t ht).symm
  have hq : (cexp (2 * π * I * (I * t)))⁻¹ = cexp (2 * π * t) := by
    rw [← Complex.exp_neg]
    congr 1
    linear_combination -(2 * π * t : ℂ) * I_sq
  have hφ₀ : φ₀'' (I / t) = φ₀ ⟨I * t, hz⟩ - 12 * I / (π * (I * t)) * φ₂' ⟨I * t, hz⟩ -
      36 / (π ^ 2 * (I * t) ^ 2) * φ₄' ⟨I * t, hz⟩ := by
    have hS := φ₀_S_transform ⟨I * t, hz⟩
    rw [← ResToImagAxis.one_div_eq_S_smul φ₀ ht] at hS
    simp only at hS
    rw [← hS, Function.resToImagAxis_apply, ResToImagAxis, dite_eq_left (one_div_pos.mpr ht),
      φ₀''_def (by simpa using ht)]
    congr 1
    ext
    simp [div_eq_mul_inv]
  rw [hres_eq, hres_eq, hres_eq, hφ₀]
  simp only [hq]
  generalize φ₀ ⟨I * t, hz⟩ = a, φ₂' ⟨I * t, hz⟩ = b, φ₄' ⟨I * t, hz⟩ = c
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have e1 : 12 * I / (π * (I * t)) = 12 / (π * t) := by field_simp
  have e2 : (36 : ℂ) / (π ^ 2 * (I * t) ^ 2) = -36 / (π ^ 2 * t ^ 2) := by
    rw [mul_pow, I_sq]
    field_simp
  rw [e1, e2]
  field_simp
  ring

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

end MagicFunction
