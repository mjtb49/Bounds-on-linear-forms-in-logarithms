import GeneralizedLogarithms.MultivariateInfiniteCollision

/-! The high-weight/low-mode dichotomy, including the infinite Taylor sums. -/

namespace GeneralizedLogarithms.MultivariateDeterminantDichotomy

noncomputable section
open scoped BigOperators
open MultivariateInfiniteCollision

theorem sum_weight_lower {ι : Type*} [Fintype ι] (x : ι → ℝ) (t η : ℝ)
    (hx : ∀ i, 0 ≤ x i) (ht : 0 ≤ t)
    (hsmall : ((Finset.univ.filter fun i => x i ≤ t).card : ℝ) < η*Fintype.card ι) :
    (1-η)*Fintype.card ι*t ≤ ∑ i, x i := by
  classical
  let low := Finset.univ.filter (fun i => x i ≤ t)
  let high := Finset.univ.filter (fun i => ¬ x i ≤ t)
  have hc : (low.card : ℝ) + high.card = Fintype.card ι := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => x i ≤ t)
  have hh : (high.card : ℝ)*t ≤ ∑ i ∈ high, x i := by
    calc
      _ = ∑ _i ∈ high, t := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi => (lt_of_not_ge (Finset.mem_filter.mp hi).2).le)
  have hsub : ∑ i ∈ high, x i ≤ ∑ i, x i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => hx i)
  have hct : (1-η)*Fintype.card ι ≤ (high.card : ℝ) := by dsimp [low] at hc; linarith
  exact (mul_le_mul_of_nonneg_right hct ht).trans (hh.trans hsub)

theorem product_row_bound {ι Γ : Type*} [Fintype ι]
    (group : ι → Γ) (weight : Γ → ℝ) (q H L : ℝ) :
    (∏ i, Real.exp (-q*weight (group i)+H*L)) =
      Real.exp (-q*(∑ i, weight (group i))+(Fintype.card ι : ℝ)*H*L) := by
  rw [← Real.exp_sum]
  congr 1
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

/-- Every translated determinant has exponential decay when both strict
gaps hold. The only remaining factors are factorial and a fixed geometric
summation constant to the number of rows. -/
theorem norm_det_le {k : ℕ} {ι Γ : Type*} [Fintype ι] [DecidableEq ι]
    (group : ι → Γ) (weight : Γ → ℝ)
    (B : ι → (Fin k → ℕ) → ℂ) (C : Γ → (Fin k → ℕ) → ι → ℂ)
    (capacity : Finset (Γ × (Fin k → ℕ))) (A η S H q D L c : ℝ)
    (hweight : ∀ g, 0 ≤ weight g) (hA : 0 ≤ A) (hS : 0 ≤ S) (hH : 0 ≤ H) (hq : 0 ≤ q)
    (hC : ∀ g d j, ‖C g d j‖ ≤ Real.exp (H*D))
    (hB : ∀ i d, ‖B i d‖ ≤ Real.exp (-q*weight (group i)+H*L) *
      (1/2 : ℝ)^(∑ r, d r))
    (hcover : ∀ g d, weight g ≤ A*H → (∑ r, (d r : ℝ)) < S*H → (g,d) ∈ capacity)
    (hcapacity : (capacity.card : ℝ) ≤ η*Fintype.card ι/2)
    (hhighgap : D+L-q*(1-η)*A ≤ -c)
    (hlowgap : D+L+Real.log (3/4)*η*S/2 ≤ -c)
    (T : Matrix ι ι ℂ)
    (hseries : ∀ i j, HasSum (fun d => B i d*C (group i) d j) (T i j)) :
    ‖T.det‖ ≤ (Fintype.card ι).factorial *
      Real.exp (-(Fintype.card ι : ℝ)*H*c + (k*Fintype.card ι : ℕ)*Real.log 4) := by
  classical
  let M : ℝ := Fintype.card ι
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hMH : 0 ≤ M*H := mul_nonneg hM hH
  have hB' (i : ι) (d : Fin k → ℕ) :
      ‖B i d‖ ≤ Real.exp (-q*weight (group i)+H*L) *
        ((3/4 : ℝ)*(3/4))^(∑ r, d r) :=
    (hB i d).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (1/2 : ℝ) ≤ (3/4)*(3/4)) _)
      (Real.exp_pos _).le)
  have hsimpl (saving : ℝ) :
      ((Fintype.card ι).factorial * (Real.exp (H*D))^Fintype.card ι *
        (∏ i, Real.exp (-q*weight (group i)+H*L))) *
        (3/4 : ℝ)^saving * ((1-(3/4 : ℝ))⁻¹)^(k*Fintype.card ι) =
      (Fintype.card ι).factorial * Real.exp
        (M*H*(D+L)-q*(∑ i, weight (group i))+
          Real.log (3/4)*saving+(k*Fintype.card ι : ℕ)*Real.log 4) := by
    rw [product_row_bound, ← Real.exp_nat_mul, Real.rpow_def_of_pos (by norm_num)]
    norm_num only [show ((1-(3/4 : ℝ))⁻¹) = 4 by norm_num]
    rw [show (4 : ℝ)^(k*Fintype.card ι) =
        Real.exp ((k*Fintype.card ι : ℕ)*Real.log 4) by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ)<4)]]
    simp only [mul_assoc, ← Real.exp_add]
    congr 2
    dsimp [M]
    ring
  by_cases hselected : η*Fintype.card ι ≤
      ((Finset.univ.filter fun i => weight (group i) ≤ A*H).card : ℝ)
  · have hh := multivariate_capacity_bound group B C (fun g => weight g ≤ A*H)
      capacity η S H (Real.exp (H*D)) (3/4)
      (fun i => Real.exp (-q*weight (group i)+H*L)) hS hH (Real.exp_pos _).le
      (by norm_num) (by norm_num) (fun _ => (Real.exp_pos _).le) hC hB'
      hcover hselected hcapacity T hseries
    rw [hsimpl] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Real.exp_le_exp.mpr
    have hsumnn : 0 ≤ ∑ i, weight (group i) := Finset.sum_nonneg (fun i _ => hweight _)
    have hgap := mul_le_mul_of_nonneg_left hlowgap hMH
    dsimp [M] at hgap ⊢
    nlinarith [mul_nonneg hq hsumnn]
  · have hh := infinite_degree_saving_bound group B C (fun d => ∑ r, d r)
      (Real.exp (H*D)) (3/4) 0 (((1-(3/4 : ℝ))⁻¹)^k)
      (fun i => Real.exp (-q*weight (group i)+H*L)) (Real.exp_pos _).le
      (by norm_num) (by norm_num) (by positivity) (fun _ => (Real.exp_pos _).le)
      hC hB' (fun f _ => Nat.cast_nonneg _)
      (multiIndex_geometric_sum_le (3/4) (by norm_num) (by norm_num)) T hseries
    simp only [← pow_mul] at hh
    rw [hsimpl] at hh
    have hsum := sum_weight_lower (fun i => weight (group i)) (A*H) η
      (fun i => hweight _) (mul_nonneg hA hH) (lt_of_not_ge hselected)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Real.exp_le_exp.mpr
    have hgap := mul_le_mul_of_nonneg_left hhighgap hMH
    have hsum' := mul_le_mul_of_nonneg_left hsum hq
    dsimp [M] at hgap ⊢
    nlinarith

end
end GeneralizedLogarithms.MultivariateDeterminantDichotomy

/-- info: 'GeneralizedLogarithms.MultivariateDeterminantDichotomy.norm_det_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateDeterminantDichotomy.norm_det_le
