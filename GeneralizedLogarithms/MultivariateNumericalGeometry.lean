import GeneralizedLogarithms.MultivariateMatrixBounds
import GeneralizedLogarithms.TransverseWeightSeparation
import GeneralizedLogarithms.MultivariateExceptionalWeights

/-! Constructing the geometric numerical data from separated form weights. -/

namespace GeneralizedLogarithms.MultivariateNumericalGeometry

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open MultivariateMatrixBounds MultivariateArithmetic TransverseWeightSeparation

variable {k m K : ℕ}

theorem independent_ne_one (α : Fin k → ℚ) (hind : MultiplicativelyIndependent α)
    (r : Fin k) : α r ≠ 1 := by
  classical
  intro he
  have hh := hind (Pi.single r 1) (by simp [Pi.single_apply, he])
  have hv := congrFun hh r
  simpa using hv

theorem centers_injective (hk : 0 < k) (α : Fin k → ℚ) (hα : ∀ r, 0 < α r)
    (hind : MultiplicativelyIndependent α) (p : Fin m → ℤ) :
    Function.Injective (fun j : Fin K => fun r => center α p j.val (Sum.inl r)) := by
  intro i j he
  let r : Fin k := ⟨0,hk⟩
  have hh := congrFun he r
  simp only [center, MultivariateRationalJet.approximationCenter_Y, Rat.cast_pow] at hh
  have hp : α r^i.val = α r^j.val := by
    exact_mod_cast (show ((α r : ℂ)^i.val) = ((α r : ℂ)^j.val) from hh)
  exact Fin.ext (pow_right_injective₀ (hα r) (independent_ne_one α hind r) hp)

def normalizedSequence (k : ℕ) (w : Fin m → ℝ) (θ : ℝ) (n : ℕ) : ℝ :=
  if hn : n < k then 1 else if hm : n-k < m then w ⟨n-k,hm⟩/θ else 1

theorem normalizedSequence_left (w : Fin m → ℝ) (θ : ℝ) (r : Fin k) :
    normalizedSequence k w θ r.val = 1 := by simp [normalizedSequence, r.isLt]

theorem normalizedSequence_right (w : Fin m → ℝ) (θ : ℝ) (i : Fin m) :
    normalizedSequence k w θ (k+i.val) = w i/θ := by simp [normalizedSequence, i.isLt]

theorem normalizedSequence_ge_one (w : Fin m → ℝ) (θ : ℝ) (hθ : 0 < θ)
    (hw : ∀ i, θ ≤ w i) (n : ℕ) : 1 ≤ normalizedSequence k w θ n := by
  unfold normalizedSequence
  split_ifs with hn hm
  · exact le_rfl
  · exact (one_le_div hθ).mpr (hw _)
  · exact le_rfl

theorem prefix_product (w : Fin m → ℝ) (θ : ℝ) (i : Fin m) :
    (∏ n ∈ Finset.range (k+i.val), normalizedSequence k w θ n) =
      ∏ t : Fin i.val, w ⟨t.val,t.isLt.trans i.isLt⟩/θ := by
  rw [← Fin.prod_univ_eq_prod_range, Fin.prod_univ_add]
  have hleft : (∏ r : Fin k, normalizedSequence k w θ (Fin.castAdd i.val r).val) = 1 := by
    simp [normalizedSequence_left]
  rw [hleft, one_mul]
  apply Finset.prod_congr rfl
  intro t ht
  exact normalizedSequence_right w θ ⟨t.val,t.isLt.trans i.isLt⟩

def polynomialWeight (w₀ : ℚ) (w : Fin m → ℚ) : Fin k ⊕ Fin m → ℚ := Sum.elim (fun _ => w₀) w

theorem volume_identity (K : ℕ) (w₀ v₀ θ σ : ℚ) (w : Fin m → ℚ)
    (hw : ∀ i, 0 < w i) :
    (K : ℝ)*(1+3*(σ : ℝ))^(k+m)*
      (∏ s, (polynomialWeight (k := k) w₀ w s : ℝ))/(∏ s, (jetWeights (k := k) v₀ θ w s : ℝ)) =
        (K : ℝ)*(1+3*(σ : ℝ))^(k+m)*((w₀ : ℝ)/v₀)^k*(θ : ℝ)^m := by
  have hp : (∏ i, (w i : ℝ)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => show (0 : ℝ)<w i by exact_mod_cast hw i)).ne'
  simp only [Fintype.prod_sum_type, polynomialWeight, jetWeights, Sum.elim_inl, Sum.elim_inr,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Rat.cast_div, Finset.prod_div_distrib,
    div_pow]
  field_simp

variable [frameOrder : LinearOrder (Fin k ⊕ Fin m)]

def build (hk : 0 < k) (horder : ∀ i j : Fin m, i < j → frameOrder.lt (Sum.inr i) (Sum.inr j))
    (α : Fin k → ℚ) (hα : ∀ r, 0 < α r) (hind : MultiplicativelyIndependent α)
    (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ) (hne : ∀ i, a i ≠ 0) (hgp : IntegerGeneralPosition a)
    (w₀ v₀ θ σ : ℚ) (w : Fin m → ℚ) (ε : ℝ)
    (hw₀ : 0 < w₀) (hv₀ : 0 < v₀) (hθ : 0 < θ) (hσ : 0 < σ) (hε : 0 < ε)
    (hw : ∀ i, 0 < w i) (hwθ : ∀ i, θ ≤ w i)
    (hvol : (K : ℝ)*(1+3*(σ : ℝ))^(k+m)*((w₀ : ℝ)/v₀)^k*(θ : ℝ)^m < 1)
    (hbudget : ((k+m : ℕ)+1 : ℝ)*ε ≤ σ)
    (hgap : ∀ r d : ℕ, r<k → 1≤d-r → d-r≤k → d≤2*k-1 →
      (d : ℝ)^d/ε^d < (θ : ℝ)^r*((w₀ : ℝ)/v₀)^(d-r))
    (hdiscount : (1+(σ : ℝ))*(θ : ℝ) ≤ 1)
    (hgrowth : ∀ i : Fin m,
      separationFactor (k+m) (((k+m : ℕ) : ℝ)^(k+m)*(1+1/ε)^(k+m)) w₀ v₀ θ *
        (∏ t : Fin i.val, (w ⟨t.val,t.isLt.trans i.isLt⟩ : ℝ)/(θ : ℝ)) < (w i : ℝ)/(θ : ℝ)) :
    MultivariateCurveMargin.NumericalData a (fun j : Fin K => center α p j.val) where
  rows_nonzero := hne
  general_position := hgp
  centerY_nonzero := fun j r => by
    simpa only [center, MultivariateRationalJet.approximationCenter_Y, Rat.cast_pow] using
      (pow_ne_zero j.val (show (α r : ℂ) ≠ 0 by exact_mod_cast (hα r).ne'))
  centers_injective := centers_injective hk α hα hind p
  w := polynomialWeight w₀ w
  v := jetWeights v₀ θ w
  w_pos := by intro s; cases s with | inl r => exact hw₀ | inr i => exact hw i
  v_pos := jetWeights_pos v₀ θ w hv₀ hθ hw
  t := Sum.elim (fun _ => 1) (fun i => (w i : ℝ)/(θ : ℝ))
  t_pos := by
    intro s
    cases s with
    | inl r => exact zero_lt_one
    | inr i => exact div_pos (by exact_mod_cast hw i) (by exact_mod_cast hθ)
  theta := θ
  w₀ := w₀
  v₀ := v₀
  theta_nonneg := by exact_mod_cast hθ.le
  v₀_pos := by exact_mod_cast hv₀
  w_block := by
    intro s
    cases s with
    | inl r => simp [polynomialWeight, blockWeight]
    | inr i =>
      simp only [polynomialWeight, blockWeight, Finset.mem_image, Finset.mem_univ, true_and,
        Sum.inr.injEq, exists_eq, ↓reduceIte, Sum.elim_inr]
      field_simp
  v_block := by intro s; cases s <;> simp [jetWeights, blockWeight]
  sigma := σ
  sigma_pos := hσ
  epsilon := ε
  epsilon_pos := hε
  volume := by simpa only [Fintype.card_fin, volume_identity K w₀ v₀ θ σ w hw] using hvol
  budget := hbudget
  separated := by
    intro A B hcard i hiA hiB hhigh
    have hh := rectangular_blockWeight_products_separated horder (by omega : 1≤k+m)
      ε w₀ v₀ θ hε (by exact_mod_cast hw₀) (by exact_mod_cast hv₀) (by exact_mod_cast hθ)
      (normalizedSequence k (fun i => (w i : ℝ)) θ)
      (normalizedSequence_left _ _) (normalizedSequence_ge_one _ _ (by exact_mod_cast hθ)
        (fun i => by exact_mod_cast hwθ i))
      (fun i => by rw [prefix_product, normalizedSequence_right]; exact hgrowth i)
      A B hcard i hiA hiB hhigh
    convert hh using 1 <;>
      congr 2 <;> funext s <;> cases s <;>
        simp [polynomialWeight, jetWeights, blockWeight, normalizedSequence_left,
          normalizedSequence_right, coordinateIndex_inl, coordinateIndex_inr]
    <;> field_simp
  gap := hgap
  discount := hdiscount

end
end GeneralizedLogarithms.MultivariateNumericalGeometry

/-- info: 'GeneralizedLogarithms.MultivariateNumericalGeometry.build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateNumericalGeometry.build
