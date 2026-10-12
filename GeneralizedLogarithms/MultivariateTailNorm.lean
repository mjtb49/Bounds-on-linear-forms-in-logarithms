import GeneralizedLogarithms.MultivariateTensorCoefficients
import GeneralizedLogarithms.MultivariateRowTranslation

/-!
# Coefficient bounds for sums of logarithm tails

Expand a product of sums by assigning each factor to a longitudinal variable,
then use the original one-variable tail bound in each independent variable.
-/

namespace GeneralizedLogarithms.MultivariateTailNorm

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open MultivariateTensorCoefficients MultivariateRowTranslation

theorem assigned_product {ι σ R : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ] [CommRing R]
    (f : ι → PowerSeries R) (u : ι → σ) :
    (∏ t, (f t).toMvPowerSeries (u t)) =
      ∏ r, (∏ t, if u t = r then f t else 1).toMvPowerSeries r := by
  simp only [map_prod, apply_ite, map_one]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro t ht
  simp

theorem norm_coeff_assigned_tails {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]
    (T : ι → ℕ) (hT : ∀ t, 1 ≤ T t) (u : ι → σ) (s : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff s (∏ t, (RowTranslation.tail (T t) (PowerSeries.log ℂ)).toMvPowerSeries (u t))‖ ≤
      (2 : ℝ) ^ s.degree := by
  rw [assigned_product, coeff_prod_lift, norm_prod, Finsupp.degree_eq_sum,
    ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro r hr
  have he : (∏ t, if u t = r then RowTranslation.tail (T t) (PowerSeries.log ℂ) else 1) =
      ∏ t, RowTranslation.tail (T t) (PowerSeries.log ℂ) ^ (if u t = r then 1 else 0) := by
    apply Finset.prod_congr rfl
    intro t ht
    split_ifs <;> simp
  rw [he]
  exact LogTailAnalytic.norm_coeff_prod_formal_logTail_le Finset.univ T
    (fun t => if u t = r then 1 else 0) (fun t _ => hT t) (s r)

variable {k m : ℕ}

abbrev Slot (d : Fin m → ℕ) := Σ i : Fin m, Fin (d i)

theorem slot_card (d : Fin m → ℕ) : Fintype.card (Slot d) = ∑ i, d i := by
  simp [Slot, Fintype.card_sigma]

theorem tail_product_expansion (a : Fin m → Fin k → ℤ) (T d : Fin m → ℕ) :
    (∏ i, tail a T i ^ d i) =
      ∑ u : Slot d → Fin k,
        MvPowerSeries.C (∏ t : Slot d, (a t.1 (u t) : ℂ)) *
          ∏ t : Slot d, (RowTranslation.tail (T t.1) (PowerSeries.log ℂ)).toMvPowerSeries (u t) := by
  classical
  have hs : (∏ i, tail a T i ^ d i) = ∏ t : Slot d, tail a T t.1 := by
    rw [Fintype.prod_sigma]
    simp
  rw [hs]
  simp only [tail, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.prod_mul_distrib, ← map_prod]

theorem norm_assigned_scalar (a : Fin m → Fin k → ℤ) (d : Fin m → ℕ) (w : Fin m → ℝ)
    (ha : ∀ i r, ‖(a i r : ℂ)‖ ≤ Real.exp (w i)) (u : Slot d → Fin k) :
    ‖∏ t : Slot d, (a t.1 (u t) : ℂ)‖ ≤ Real.exp (∑ i, w i * (d i : ℝ)) := by
  rw [norm_prod]
  calc
    _ ≤ ∏ t : Slot d, Real.exp (w t.1) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun t _ => ha t.1 (u t))
    _ = Real.exp (∑ t : Slot d, w t.1) := (Real.exp_sum _ _).symm
    _ = _ := by
      congr 1
      rw [Fintype.sum_sigma]
      simp [mul_comm]

theorem norm_coeff_tail_product (a : Fin m → Fin k → ℤ) (T d : Fin m → ℕ)
    (hT : ∀ i, 1 ≤ T i) (w : Fin m → ℝ)
    (ha : ∀ i r, ‖(a i r : ℂ)‖ ≤ Real.exp (w i)) (s : Fin k →₀ ℕ) :
    ‖MvPowerSeries.coeff s (∏ i, tail a T i ^ d i)‖ ≤
      (k : ℝ) ^ (∑ i, d i) * Real.exp (∑ i, w i * (d i : ℝ)) * (2 : ℝ) ^ s.degree := by
  classical
  rw [tail_product_expansion, map_sum]
  calc
    _ ≤ ∑ u : Slot d → Fin k, ‖MvPowerSeries.coeff s
        (MvPowerSeries.C (∏ t : Slot d, (a t.1 (u t) : ℂ)) *
          ∏ t : Slot d, (RowTranslation.tail (T t.1) (PowerSeries.log ℂ)).toMvPowerSeries (u t))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _u : Slot d → Fin k, Real.exp (∑ i, w i * (d i : ℝ)) * (2 : ℝ) ^ s.degree := by
      apply Finset.sum_le_sum
      intro u hu
      rw [MvPowerSeries.coeff_C_mul, norm_mul]
      exact mul_le_mul (norm_assigned_scalar a d w ha u)
        (norm_coeff_assigned_tails (fun t : Slot d => T t.1) (fun t => hT t.1) u s)
        (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by simp [slot_card, Fintype.card_fun, mul_assoc]

end
end GeneralizedLogarithms.MultivariateTailNorm

/-- info: 'GeneralizedLogarithms.MultivariateTailNorm.norm_coeff_tail_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateTailNorm.norm_coeff_tail_product
