import GeneralizedLogarithms.MultivariateTranslatedDeterminant
import GeneralizedLogarithms.MultivariateArithmeticBounds

/-! A finite list of numerical conditions for exponential determinant decay.
No analytic row identity or determinant estimate is assumed in this record. -/

namespace GeneralizedLogarithms.MultivariateAnalyticSetup

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open MultivariateRowTranslation MultivariateColumnSeries MultivariateNormalizedRows
open MultivariateTranslatedDeterminant MultivariateMatrixTranslation
open MatrixTranslationBounds

variable {k m K : ℕ}

structure Data (α : Fin k → ℚ) (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ) (K : ℕ) where
  w : Fin m → ℝ
  w₀ : ℝ
  ws : ℝ
  v₀ : ℝ
  F : ℝ
  ν : ℝ
  C : ℝ
  θ : ℝ
  A : ℝ
  η : ℝ
  S : ℝ
  c : ℝ
  R : NNReal
  T : Fin m → ℕ
  omega : Fin k → ℂ
  exp_omega : ∀ r, Complex.exp (omega r) = (α r : ℂ)
  radius : 1 ≤ (R : ℝ)
  w₀_pos : 0 < w₀
  ws_pos : 0 < ws
  v₀_pos : 0 < v₀
  F_pos : 0 < F
  nu_nonneg : 0 ≤ ν
  C_nonneg : 0 ≤ C
  A_nonneg : 0 ≤ A
  S_nonneg : 0 ≤ S
  weights : ∀ i, ws ≤ w i
  weights_one : ∀ i, 1 ≤ w i
  cutoff_pos : ∀ i, 1 ≤ T i
  cutoff_budget : ∀ i, F*w i ≤ v₀*T i
  coefficients : ∀ i r, ‖(a i r : ℂ)‖ ≤ Real.exp (w i)
  errors : ∀ j : Fin K, ∀ i, ‖error a p omega j.val i‖ ≤ Real.exp (C-ν*w i)
  centers : ∀ j : Fin K, ∀ r, ‖(j.val : ℂ)*omega r‖+3/4 ≤ (R : ℝ)/2
  high_gap : columnLoss k R w₀ ws+ν*θ+rowLoss k ν C ws v₀ F-(ν+1)*(1-η)*A ≤ -c
  low_gap : columnLoss k R w₀ ws+ν*θ+rowLoss k ν C ws v₀ F+Real.log (3/4)*η*S/2 ≤ -c

def termCount (k m : ℕ) (v₀ H : ℝ) : ℕ :=
  (⌊H⌋₊+1)^(2*m)*(⌊H/v₀⌋₊+1)^k

variable {α : Fin k → ℚ} {a : Fin m → Fin k → ℤ} {p : Fin m → ℤ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A bound for actual truncated-jet determinants, with all translation
choices and all infinite Taylor modes already summed. -/
theorem norm_actual_det_le (hk : 0 < k) (D : Data α a p K)
    (H : ℝ) (hH : 0 ≤ H) (j : ι → Fin K) (β : ι → Fin m →₀ ℕ) (s : ι → Fin k →₀ ℕ)
    (h : ι → Fin k →₀ ℕ) (b : ι → Fin m →₀ ℕ)
    (hcol : ∀ l, D.w₀*(∑ r, (h l r : ℝ))+∑ i, D.w i*b l i ≤ H)
    (hβ : ∀ i, weight D.w (β i) ≤ D.θ*H) (hs : ∀ i, ((s i).degree : ℝ) ≤ H/D.v₀)
    (capacity : Finset ((Fin m →₀ ℕ) × (Fin k → ℕ)))
    (hcover : ∀ (g : Fin m →₀ ℕ) (n : Fin k → ℕ), weight D.w g ≤ D.A*H → (∑ r, (n r : ℝ)) < D.S*H → (g,n) ∈ capacity)
    (hcapacity : (capacity.card : ℝ) ≤ D.η*Fintype.card ι/2) :
    ‖Matrix.det (fun i l => MvPowerSeries.coeff ((s i).sumElim (β i))
      (MultivariateArithmetic.jet α a p D.T (j i).val
        (MvPolynomial.monomial ((h l).sumElim (b l)) 1)))‖ ≤
      (termCount k m D.v₀ H : ℝ)^Fintype.card ι * (Fintype.card ι).factorial *
        Real.exp (-(Fintype.card ι : ℝ)*H*D.c+(k*Fintype.card ι : ℕ)*Real.log 4) := by
  let W := MatrixTranslation.transverseIndices D.w H
  let choices := fun i => RowChoices W (β i) (s i)
  let entry := fun i (t : choices i) l =>
    rowScalar (error a p D.omega (j i).val) (tail a D.T) (β i) t.1.val t.2.1 t.2.2.val.1 *
      MvPowerSeries.coeff t.2.2.val.2
        ((periodMonomial (fun r => (α r : ℂ)) D.omega a (j i).val (h l) (b l)).coeff t.1.val)
  have hentry (i l : ι) :
      MvPowerSeries.coeff ((s i).sumElim (β i))
        (MultivariateArithmetic.jet α a p D.T (j i).val
          (MvPolynomial.monomial ((h l).sumElim (b l)) 1)) = ∑ t : choices i, entry i t l := by
    apply actual_jet_row_choices
    apply periodMonomial_support_subset _ _ _ _ _ _ D.w H
      (fun t => D.ws_pos.trans_le (D.weights t))
    have hn : 0 ≤ D.w₀*(∑ r, (h l r : ℝ)) := mul_nonneg D.w₀_pos.le (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    linarith [hcol l]
  simp_rw [hentry]
  have hpiece (f : ∀ i, choices i) :
      ‖Matrix.det (fun i l => entry i (f i) l)‖ ≤
        (Fintype.card ι).factorial *
          Real.exp (-(Fintype.card ι : ℝ)*H*D.c+(k*Fintype.card ι : ℕ)*Real.log 4) := by
    have hparts (i : ι) : (f i).2.2.val.1+(f i).2.2.val.2=s i :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp (f i).2.2.property
    have hdeg (i : ι) : (f i).2.2.val.1.degree+(f i).2.2.val.2.degree=(s i).degree := by
      simpa only [map_add] using congrArg Finsupp.degree (hparts i)
    apply norm_translated_det_le (capacity := capacity) hk a p D.T (fun r => (α r : ℂ)) D.omega D.exp_omega
      (fun i => (j i).val) β (fun i => (f i).1.val) (fun i => (f i).2.1)
      (fun i => (f i).2.2.val.1) (fun i => (f i).2.2.val.2) h b D.w D.R H
      D.w₀ D.ws D.v₀ D.F D.ν D.C D.θ D.A D.η D.S D.c hH D.radius D.w₀_pos D.ws_pos
      D.v₀_pos D.F_pos D.nu_nonneg D.C_nonneg D.A_nonneg D.S_nonneg D.weights
      D.cutoff_pos D.cutoff_budget D.coefficients (fun i => D.errors (j i))
      (fun i => D.centers (j i)) hcol hβ
    · intro i
      exact (MatrixTranslation.mem_transverseIndices D.w H
        (fun t => D.ws_pos.trans_le (D.weights t)) _).mp (f i).1.property
    · intro i
      have hh : (f i).2.2.val.1.degree ≤ (s i).degree := by have := hdeg i; omega
      exact (Nat.cast_le.mpr hh).trans (hs i)
    · intro i
      have hh : (f i).2.2.val.2.degree ≤ (s i).degree := by have := hdeg i; omega
      exact (Nat.cast_le.mpr hh).trans (hs i)
    · exact hcover
    · exact hcapacity
    · exact D.high_gap
    · exact D.low_gap
  have hh := norm_det_row_sum_le entry _ hpiece
  apply hh.trans
  have hc : (∏ i, (Fintype.card (choices i) : ℝ)) ≤
      (termCount k m D.v₀ H : ℝ)^Fintype.card ι := by
    calc
      _ ≤ ∏ _i : ι, (termCount k m D.v₀ H : ℝ) := Finset.prod_le_prod₀
        (fun _ _ => Nat.cast_nonneg _) (fun i _ => by
          exact_mod_cast rowChoices_card_le D.w H D.v₀ D.weights_one (β i) (s i) (hs i))
      _ = _ := by simp
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc
    (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)

end
end GeneralizedLogarithms.MultivariateAnalyticSetup

/-- info: 'GeneralizedLogarithms.MultivariateAnalyticSetup.norm_actual_det_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateAnalyticSetup.norm_actual_det_le
