import GeneralizedLogarithms.MultivariateFixedParameters
import GeneralizedLogarithms.MultivariateAnalyticSetup
import GeneralizedLogarithms.MultivariateExceptionalWeights
import GeneralizedLogarithms.MultivariateMatrixBounds

/-! Constructing every analytic hypothesis from actual exceptional forms. -/

namespace GeneralizedLogarithms.MultivariateAnalyticConstruction

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open MultivariateParameters MultivariateFixedParameters MultivariateExceptionalWeights
open MultivariateAnalyticSetup MultivariateMatrixBounds MultivariateNormalizedRows
open MultivariateTranslatedDeterminant MultivariateArithmeticBounds MatrixTranslationBounds

variable {k : ℕ} {ν : ℝ}

def denominatorCost (α : Fin k → ℚ) : ℝ := ∑ r, Real.log (α r).den
def logarithmSize (α : Fin k → ℚ) : ℝ := ∑ r, ‖omega α r‖

theorem radius_one {K : ℕ} (hK : 0 < K) (α : Fin k → ℚ) :
    1 ≤ radius K (logarithmSize α) := by
  have hn : 0 ≤ logarithmSize α := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  dsimp [radius]
  nlinarith

theorem center_bound {K : ℕ} (hK : 0 < K) (α : Fin k → ℚ) (j : Fin K) (r : Fin k) :
    ‖(j.val : ℂ)*omega α r‖+3/4 ≤ radius K (logarithmSize α)/2 := by
  have hn : 0 ≤ logarithmSize α := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hr : ‖omega α r‖ ≤ logarithmSize α :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ r)
  have hj : (j.val : ℝ) ≤ K := by exact_mod_cast j.isLt.le
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  rw [norm_mul, Complex.norm_natCast]
  have hh := mul_le_mul hj hr (norm_nonneg _) (Nat.cast_nonneg K)
  dsimp [radius]
  nlinarith

def build (P : Parameters k ν) (α : Fin k → ℚ) (hα : ∀ r, 0 < α r) (hν : 0 ≤ ν)
    (f : Fixed P (denominatorCost α) (logarithmSize α))
    (p : Fin f.m → ℤ) (a : Fin f.m → Fin k → ℤ)
    (hW : ∀ i, f.W ≤ (logarithmicWeight (p i) (a i) : ℝ))
    (hbad : ∀ i, |linearForm α (p i) (a i)| ≤ (coefficientHeight (p i) (a i) : ℝ)^(-ν)) :
    Data α a p (count P f.m) where
  w := fun i => logarithmicWeight (p i) (a i)
  w₀ := w₀ P f.m
  ws := f.W
  v₀ := v₀ P f.m
  F := f.F
  ν := ν
  C := Real.log (count P f.m)+ν
  θ := P.θ
  A := P.A
  η := P.η
  S := f.S
  c := gap P/2
  R := ⟨radius (count P f.m) (logarithmSize α), zero_le_one.trans (radius_one (count_pos P f.m) α)⟩
  T := fun i => truncationOrder f.F (v₀ P f.m) (logarithmicWeight (p i) (a i))
  omega := omega α
  exp_omega := exp_omega α hα
  radius := radius_one (count_pos P f.m) α
  w₀_pos := by exact_mod_cast w₀_pos P f.m
  ws_pos := zero_lt_one.trans_le f.W_one
  v₀_pos := by exact_mod_cast v₀_pos P f.m
  F_pos := f.F_pos
  nu_nonneg := hν
  C_nonneg := add_nonneg (Real.log_nonneg (by exact_mod_cast count_pos P f.m)) hν
  A_nonneg := (P.theta_pos.trans P.theta_lt_A).le
  S_nonneg := f.S_pos.le
  weights := hW
  weights_one := fun i => f.W_one.trans (hW i)
  cutoff_pos := fun i => truncationOrder_pos f.F_pos (by exact_mod_cast v₀_pos P f.m)
    (zero_lt_one.trans_le (f.W_one.trans (hW i)))
  cutoff_budget := fun i => truncationOrder_budget (by exact_mod_cast v₀_pos P f.m)
  coefficients := fun i r => coefficient_norm_le (p i) (a i) r
  errors := actual_error_le (count_pos P f.m) α p a ν hν hbad
  centers := center_bound (count_pos P f.m) α
  high_gap := by
    have hg : columnLoss k (radius (count P f.m) (logarithmSize α)) (w₀ P f.m) f.W+
        ν*P.θ+rowLoss k ν (Real.log (count P f.m)+ν) f.W (v₀ P f.m) f.F-
        (ν+1)*(1-P.η)*P.A ≤ -(gap P/2) := by
      have hh := f.analytic_cost
      dsimp [columnLoss,rowLoss,weightNumerator,gap] at *
      simp only [add_div] at *
      nlinarith
    convert! hg using 1
  low_gap := by
    have hg : columnLoss k (radius (count P f.m) (logarithmSize α)) (w₀ P f.m) f.W+
        ν*P.θ+rowLoss k ν (Real.log (count P f.m)+ν) f.W (v₀ P f.m) f.F+
        Real.log (3/4)*P.η*f.S/2 ≤ -(gap P/2) := by
      have hh := f.analytic_cost
      have hl := f.low_gap
      dsimp [columnLoss,rowLoss,weightNumerator,gap] at *
      simp only [add_div] at *
      nlinarith
    convert! hg using 1

theorem built_cost_lt (P : Parameters k ν) (α : Fin k → ℚ) (hα : ∀ r, 0 < α r) (hν : 0 ≤ ν)
    (f : Fixed P (denominatorCost α) (logarithmSize α))
    (p : Fin f.m → ℤ) (a : Fin f.m → Fin k → ℤ)
    (hW : ∀ i, f.W ≤ (logarithmicWeight (p i) (a i) : ℝ))
    (hbad : ∀ i, |linearForm α (p i) (a i)| ≤ (coefficientHeight (p i) (a i) : ℝ)^(-ν)) :
    let D := build P α hα hν f p a hW hbad
    cost α D.T (count P f.m-1) (degreeWeights D.w₀ D.w) < D.c := by
  let D := build P α hα hν f p a hW hbad
  change cost α D.T (count P f.m-1) (degreeWeights D.w₀ D.w) < D.c
  have hw : ∀ s, 0 < degreeWeights (k := k) D.w₀ D.w s := by
    intro s
    cases s with
    | inl r => exact D.w₀_pos
    | inr i => exact D.ws_pos.trans_le (D.weights i)
  have hh := cutoff_cost_le α (count P f.m-1) (degreeWeights D.w₀ D.w) hw D.F D.v₀ D.F_pos.le D.v₀_pos
  have hT : (fun i => ⌈D.F*degreeWeights (k := k) D.w₀ D.w (Sum.inr i)/D.v₀⌉₊) = D.T := rfl
  rw [hT] at hh
  have hy : (∑ r : Fin k, Real.log (α r).den/degreeWeights (k := k) D.w₀ D.w (Sum.inl r)) =
      denominatorCost α/D.w₀ := by simp only [degreeWeights,Sum.elim_inl,denominatorCost,Finset.sum_div]
  rw [hy] at hh
  have hs : (∑ i, 1/degreeWeights (k := k) D.w₀ D.w (Sum.inr i)) ≤ (f.m : ℝ)/f.W := by
    calc
      _ ≤ ∑ _i : Fin f.m, 1/f.W := Finset.sum_le_sum (fun i _ => by
        apply one_div_le_one_div_of_le (zero_lt_one.trans_le f.W_one)
        exact hW i)
      _ = _ := by simp; ring
  have hden : 0 ≤ denominatorCost α := Finset.sum_nonneg (fun r _ =>
    Real.log_nonneg (by exact_mod_cast (α r).pos))
  have hK : ((count P f.m-1 : ℕ) : ℝ) ≤ count P f.m := by exact_mod_cast Nat.sub_le (count P f.m) 1
  apply lt_of_le_of_lt hh
  apply lt_of_le_of_lt _ f.arithmetic_cost
  have hfirst := mul_le_mul_of_nonneg_right hK (div_nonneg hden D.w₀_pos.le)
  have hlast := mul_le_mul_of_nonneg_left hs Arithmetic.lcmConstant_pos.le
  change _ ≤ (count P f.m : ℝ)*denominatorCost α/D.w₀+
    Arithmetic.lcmConstant*D.F*f.m/D.v₀+Arithmetic.lcmConstant*f.m/f.W
  simp only [mul_div_assoc] at hfirst hlast ⊢
  linarith

end
end GeneralizedLogarithms.MultivariateAnalyticConstruction

/-- info: 'GeneralizedLogarithms.MultivariateAnalyticConstruction.build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateAnalyticConstruction.build

/-- info: 'GeneralizedLogarithms.MultivariateAnalyticConstruction.built_cost_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateAnalyticConstruction.built_cost_lt
