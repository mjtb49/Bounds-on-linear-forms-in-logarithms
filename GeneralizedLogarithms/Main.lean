import GeneralizedLogarithms.MultivariateDeterminantContradiction
import GeneralizedLogarithms.MultivariateAnalyticConstruction
import GeneralizedLogarithms.MultivariateNumericalGeometry

/-! The lower bound for linear forms in multiplicatively independent rational logarithms. -/

namespace GeneralizedLogarithms

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open MultivariateParameters MultivariateFixedParameters MultivariateExceptionalWeights
open MultivariateMatrixBounds MultivariateModeCapacity TransverseWeightSeparation
open MultivariateAnalyticConstruction

theorem no_exceptional_sequence {k : ℕ} (hk : 0 < k)
    (α : Fin k → ℚ) (hα : ∀ r, 0 < α r) (hind : MultiplicativelyIndependent α)
    (hlower : ∀ r : ℕ, 0 < r → r < k → ∀ β : Fin r → ℚ,
      (∀ s, 0 < β s) → MultiplicativelyIndependent β → EventualLinearFormLowerBound β)
    (ν : ℝ) (hν : (k : ℝ) < ν)
    (hfailure : ¬ ∃ H₀ : ℕ, ∀ (p : ℤ) (a : Fin k → ℤ), H₀ ≤ coefficientHeight p a →
      (coefficientHeight p a : ℝ)^(-ν) ≤ |linearForm α p a|) : False := by
  classical
  have hν0 : 0 ≤ ν := (Nat.cast_nonneg k).trans hν.le
  obtain ⟨P⟩ := exists_parameters k hk ν hν
  obtain ⟨f⟩ := exists_fixed hk hν0 P (denominatorCost α) (logarithmSize α)
  let ε := epsilon P f.m
  have hε : 0 < ε := div_pos P.sigma_pos (by positivity)
  let Gfactor := separationFactor (k+f.m)
    (((k+f.m : ℕ) : ℝ)^(k+f.m)*(1+1/ε)^(k+f.m)) (w₀ P f.m) (v₀ P f.m) P.θ
  obtain ⟨p,a,hgp,hne,hbad,hW,hgrowth⟩ := exists_weighted_family α hα hind hlower ν hν hfailure
    f.m f.W Gfactor P.θ P.theta_pos
  let w : Fin f.m → ℚ := fun i => logarithmicWeight (p i) (a i)
  have hw (i : Fin f.m) : 0 < w i := by
    have hh := (zero_lt_one.trans_le f.W_one).trans (hW i)
    dsimp [w]
    exact_mod_cast hh
  have hwθ (i : Fin f.m) : P.θ ≤ w i := by
    have hh : (P.θ : ℝ) < (logarithmicWeight (p i) (a i) : ℝ) :=
      (P.theta_lt_A.trans P.A_lt_one).trans_le (f.W_one.trans (hW i).le)
    exact_mod_cast hh.le
  let D := MultivariateAnalyticConstruction.build P α hα hν0 f p a (fun i => (hW i).le) (fun i => (hbad i).le)
  let coordOrder : LinearOrder (Fin k ⊕ Fin f.m) :=
    LinearOrder.lift' (coordinateIndex k f.m) (coordinateIndex k f.m).injective
  letI := coordOrder
  have horder : ∀ i j : Fin f.m, i < j → coordOrder.lt (Sum.inr i) (Sum.inr j) := by
    intro i j hij
    change k+i.val < k+j.val
    omega
  have hbudget : ((k+f.m : ℕ)+1 : ℝ)*ε ≤ P.σ := by
    dsimp [ε,epsilon]
    have hn : ((k+f.m : ℕ)+1 : ℝ) ≠ 0 := by positivity
    field_simp
    exact le_rfl
  let G := MultivariateNumericalGeometry.build hk horder α hα hind a p hne hgp
    (w₀ P f.m) (v₀ P f.m) P.θ P.σ w ε (w₀_pos P f.m) (v₀_pos P f.m)
    (by exact_mod_cast P.theta_pos) (by exact_mod_cast P.sigma_pos) hε hw hwθ
    f.volume hbudget f.longitudinal P.fibre_discount.le
    (fun i => by simpa only [w,Rat.cast_natCast] using hgrowth i)
  have hDw : D.w = fun i => (w i : ℝ) := by
    funext i
    simp [D,MultivariateAnalyticConstruction.build,w]
  have hDv : D.v₀ = (v₀ P f.m : ℝ) := rfl
  have hDt : D.θ = (P.θ : ℝ) := rfl
  have hGw : (fun s => (G.w s : ℝ)) = degreeWeights D.w₀ D.w := by
    funext s
    cases s <;> simp [G,D,MultivariateNumericalGeometry.build,MultivariateNumericalGeometry.polynomialWeight,
      MultivariateAnalyticConstruction.build,degreeWeights,w]
  have hGv : G.v = jetWeights (v₀ P f.m) P.θ w := rfl
  have hT : ∀ i r, G.v (Sum.inr i) ≤ (D.T i : ℚ)*G.v (Sum.inl r) := by
    intro i r
    rw [hGv]
    change w i/P.θ ≤ (D.T i : ℚ)*v₀ P f.m
    have hh := D.cutoff_budget i
    have hx := mul_le_mul_of_nonneg_right f.F_theta (D.ws_pos.le.trans (D.weights i))
    have hr : (w i : ℝ)/(P.θ : ℝ) ≤ (D.T i : ℝ)*(v₀ P f.m : ℝ) := by
      rw [hDw,hDv] at hh
      change _ ≤ (D.F : ℝ)*(w i : ℝ) at hx
      rw [hDw] at hx
      calc
        _ = (1/(P.θ : ℝ))*(w i : ℝ) := by ring
        _ ≤ D.F*(w i : ℝ) := hx
        _ ≤ (v₀ P f.m : ℝ)*(D.T i : ℝ) := hh
        _ = _ := mul_comm _ _
    exact_mod_cast hr
  have hρ : 0 < rowDensity (k := k) (count P f.m) (v₀ P f.m) P.θ w := by
    unfold rowDensity
    apply div_pos
    · exact mul_pos (by exact_mod_cast count_pos P f.m) (pow_pos P.theta_pos f.m)
    · exact mul_pos (mul_pos (by exact_mod_cast Nat.factorial_pos (k+f.m))
        (pow_pos (by exact_mod_cast v₀_pos P f.m) k))
        (Finset.prod_pos (fun i _ => by exact_mod_cast hw i))
  have hcapacity : capacityDensity (k := k) w D.A D.S <
      D.η*rowDensity (k := k) (count P f.m) (v₀ P f.m) P.θ w/2 := by
    have hh : capacityDensity (k := k) w D.A D.S/
        rowDensity (k := k) (count P f.m) (v₀ P f.m) P.θ w < P.η/2 := by
      rw [density_ratio _ (count_pos P f.m) _ _ _ (v₀_pos P f.m)
        (by exact_mod_cast P.theta_pos) hw]
      exact f.capacity
    have hr := (div_lt_iff₀ hρ).mp hh
    change _ < P.η*rowDensity (k := k) (count P f.m) (v₀ P f.m) P.θ w/2
    nlinarith
  exact MultivariateDeterminantContradiction.impossible hk (count_pos P f.m) α a p G D
    (v₀ P f.m) P.θ w (v₀_pos P f.m) (by exact_mod_cast P.theta_pos) hw hDw hDv hDt hGw hGv hT
    (P.theta_pos.trans P.theta_lt_A) f.S_pos hcapacity
    (built_cost_lt P α hα hν0 f p a (fun i => (hW i).le) (fun i => (hbad i).le))

theorem eventualLowerBound_all (k : ℕ) : ∀ α : Fin k → ℚ,
    (∀ r, 0 < α r) → MultiplicativelyIndependent α → EventualLinearFormLowerBound α := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro α hα hind ν hν
    by_cases hk : k=0
    · subst k
      refine ⟨3,fun p a hH => ?_⟩
      have ha : a=0 := Subsingleton.elim _ _
      subst a
      have hp : p ≠ 0 := by
        intro hp
        subst p
        norm_num [coefficientHeight] at hH
      exact lower_bound_zero_coefficients α p hp ν (by simpa using hν.le)
    · by_contra hf
      exact no_exceptional_sequence (Nat.pos_of_ne_zero hk) α hα hind
        (fun r _ hr β hβ hiβ => ih r hr β hβ hiβ) ν hν hf

/-- Main theorem: every exponent strictly above the logarithmic rank is an
eventual lower-bound exponent, with the exact maximum coefficient height. -/
theorem logarithmic_linear_forms {k : ℕ} (α : Fin k → ℚ)
    (hα : ∀ r, 0 < α r) (hind : MultiplicativelyIndependent α) :
    ∀ ν : ℝ, (k : ℝ) < ν → ∃ H₀ : ℕ, ∀ (p : ℤ) (a : Fin k → ℤ),
      H₀ ≤ coefficientHeight p a →
        (coefficientHeight p a : ℝ)^(-ν) ≤ |(p : ℝ)+∑ r, (a r : ℝ)*Real.log (α r)| :=
  eventualLowerBound_all k α hα hind

end
end GeneralizedLogarithms

/-- info: 'GeneralizedLogarithms.logarithmic_linear_forms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.logarithmic_linear_forms
