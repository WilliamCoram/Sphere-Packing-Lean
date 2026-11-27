/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.AnalyticContinuation
public import SpherePacking.MagicFunction.a.Schwartz

import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
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
  have hpow {k : ℕ} (hk : k ≤ 2) : (fun t : ℝ ↦ (t : ℂ) ^ k) =O[atTop] fun t ↦ t ^ 2 :=
    (Asymptotics.isBigO_of_le _ fun t ↦ by simp).trans
      ((Asymptotics.isBigO_pow_pow_cobounded_of_le hk).mono IsOrderBornology.atTop_le_cobounded)
  refine ((((hpow le_rfl).mul (hres _ φ₀_isBigO_atImInfty)).sub
    (((hpow one_le_two).mul (hres _ φ₂'_sub_isBigO_atImInfty)).const_mul_left (12 / π : ℂ))).add
      (((hpow zero_le_two).mul (hres _ φ₄'_sub_isBigO_atImInfty)).const_mul_left
        (36 / π ^ 2 : ℂ))).congr' ?_ (.of_forall fun t ↦ by ring_nf)
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hS : φ₀'' (I / t) = φ₀ (ModularGroup.S • ⟨I * t, by simpa using ht⟩) := by
    rw [φ₀''_def (by simpa using ht), UpperHalfPlane.modular_S_smul]
    congr
    simp [div_eq_mul_inv, mul_comm]
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, dite_true, hS, φ₀_S_transform]
  rw [show (cexp (2 * π * I * (I * t)))⁻¹ = cexp (2 * π * t) by
    rw [← Complex.exp_neg]; congr; linear_combination -(2 * π * t : ℂ) * I_sq]
  grind [ofReal_ne_zero.mpr ht.ne', I_sq]

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
  -- it is continuous on `[0, ∞)`
  refine ContinuousOn.locallyIntegrableOn (fun t ht ↦ ?_) measurableSet_Ici
  rcases (mem_Ici.mp ht).eq_or_lt with rfl | ht
  · -- at `0` it vanishes, and `t² φ₀(i/t) → 0` as `t → 0⁺` since `φ₀ → 0` at `i∞`
    rw [← continuousWithinAt_Ioi_iff_Ici]
    have hφ₀ := (tendsto_resToImagAxis_of_tendsto_atImInfty (φ₀_isBigO_atImInfty.trans_tendsto
      (by simpa [Function.Periodic.qParam] using UpperHalfPlane.qParam_tendsto_atImInfty one_pos))
        ).comp tendsto_inv_nhdsGT_zero
    have ht2 : Tendsto (fun t : ℝ ↦ (t : ℂ) ^ 2) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa using ((by fun_prop : Continuous fun t : ℝ ↦ (t : ℂ) ^ 2).tendsto 0).mono_left
        nhdsWithin_le_nhds
    have hfg : (fun t : ℝ ↦ (t : ℂ) ^ 2 * (φ₀.resToImagAxis ∘ fun x ↦ x⁻¹) t)
        =ᶠ[nhdsWithin 0 (Ioi 0)] fun t : ℝ ↦ -(I * t) ^ 2 * φ₀'' (-1 / (I * t)) := by
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      rw [Function.comp_apply, neg_sq_mul_φ₀''_neg_inv_I_mul, Function.resToImagAxis_apply,
        ResToImagAxis, dite_eq_left (inv_pos.mpr ht), φ₀''_def (by simpa using ht), mul_comm]
      congr 2
      ext
      simp [div_eq_mul_inv]
    simpa [ContinuousWithinAt] using (ht2.mul hφ₀).congr' hfg
  · -- on `(0, ∞)`, `φ₀''` is continuous on the upper half plane
    have hI : -1 / (I * t) = I / t := by simp [div_eq_mul_inv, Complex.inv_I, mul_comm]
    have hmem : -1 / (I * t) ∈ (univ ×ℂ Ioi 0 : Set ℂ) := by simpa [reProdIm, hI] using ht
    have hf : ContinuousAt (fun t : ℝ ↦ -1 / (I * t)) t :=
      continuousAt_const.div (by fun_prop) (by simp [ht.ne'])
    exact ((by fun_prop : ContinuousAt (fun t : ℝ ↦ -(I * t) ^ 2) t).mul
      ((a.ComplexIntegrands.φ₀''_continuous.continuousAt
        ((isOpen_univ.reProdIm isOpen_Ioi).mem_nhds hmem)).comp_of_eq hf rfl)).continuousWithinAt

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
