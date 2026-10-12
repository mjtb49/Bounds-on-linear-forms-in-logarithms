import GeneralizedLogarithms.MultivariateAnalyticSetup

/-! The analytic estimate applied to the same minors as the arithmetic bound. -/

namespace GeneralizedLogarithms.MultivariateMatrixBounds

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open MultivariateMixedSeries MultivariateInterpolationMatrix MultivariateAnalyticSetup
open MultivariateAuxiliaryPolynomial MultivariateModeCapacity MatrixTranslationBounds

variable {k m K : ℕ}

def degreeWeights (w₀ : ℝ) (w : Fin m → ℝ) : Fin k ⊕ Fin m → ℝ := Sum.elim (fun _ => w₀) w
def jetWeights (v₀ θ : ℚ) (w : Fin m → ℚ) : Fin k ⊕ Fin m → ℚ := Sum.elim (fun _ => v₀) (fun i => w i/θ)

theorem split_weight (w₀ : ℝ) (w : Fin m → ℝ) (e : Fin k ⊕ Fin m →₀ ℕ) :
    Finsupp.weight (degreeWeights w₀ w) e =
      w₀*(∑ r, (leftIndex e r : ℝ))+weight w (rightIndex e) := by
  simp only [Finsupp.weight_eq_sum, nsmul_eq_mul, Fintype.sum_sum_type, degreeWeights,
    Sum.elim_inl, Sum.elim_inr, leftIndex, rightIndex, Finsupp.comapDomain_apply, weight,
    Finset.mul_sum, mul_comm]

theorem jetWeights_pos (v₀ θ : ℚ) (w : Fin m → ℚ)
    (hv : 0 < v₀) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) : ∀ t, 0 < jetWeights (k := k) v₀ θ w t := by
  intro t
  cases t with
  | inl r => exact hv
  | inr i => exact div_pos (hw i) hθ

theorem jet_bounds (v₀ θ : ℚ) (w : Fin m → ℚ)
    (hv : 0 < v₀) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) (H : ℚ)
    (e : ↥(jetExponents (jetWeights (k := k) v₀ θ w) H)) :
    ((leftIndex e.val).degree : ℝ) ≤ (H : ℝ)/v₀ ∧
      weight (fun i => (w i : ℝ)) (rightIndex e.val) ≤ (θ : ℝ)*H := by
  have he := (mem_jetExponents _ (jetWeights_pos v₀ θ w hv hθ hw) H e.val).mp e.property
  have he' : Finsupp.weight (degreeWeights (k := k) (v₀ : ℝ) (fun i => (w i : ℝ)/(θ : ℝ))) e.val < (H : ℝ) := by
    have hcast : ((Finsupp.weight (jetWeights v₀ θ w) e.val : ℚ) : ℝ) =
        Finsupp.weight (degreeWeights (v₀ : ℝ) (fun i => (w i : ℝ)/(θ : ℝ))) e.val := by
      simp [Finsupp.weight_eq_sum, nsmul_eq_mul, Fintype.sum_sum_type, jetWeights, degreeWeights]
    rw [← hcast]
    exact_mod_cast he
  rw [split_weight] at he'
  have hvR : (0 : ℝ) < v₀ := by exact_mod_cast hv
  have htR : (0 : ℝ) < θ := by exact_mod_cast hθ
  have hwn : 0 ≤ weight (fun i => (w i : ℝ)/(θ : ℝ)) (rightIndex e.val) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (div_nonneg (by exact_mod_cast (hw i).le) htR.le) (Nat.cast_nonneg _))
  have hleft : 0 ≤ (v₀ : ℝ)*(∑ r, (leftIndex e.val r : ℝ)) :=
    mul_nonneg hvR.le (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  constructor
  · apply (le_div_iff₀ hvR).mpr
    rw [Finsupp.degree_eq_sum, Nat.cast_sum]
    nlinarith
  · have hb : weight (fun i => (w i : ℝ)/(θ : ℝ)) (rightIndex e.val) ≤ (H : ℝ) := by linarith
    have hh := mul_le_mul_of_nonneg_left hb htR.le
    convert hh using 1
    simp only [weight, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp

theorem row_card_eq (K : ℕ) (v₀ θ : ℚ) (w : Fin m → ℚ) (H : ℚ) :
    Fintype.card (Row (Fin K) (jetWeights (k := k) v₀ θ w) H) =
      rowCount (k := k) K v₀ θ w H := by
  classical
  have hinj : Function.Injective (simplexExponent (k := k) (m := m)) := by
    intro a b h
    funext i
    have hh := congrArg (fun d => d (indexEquiv i)) h
    simpa using hh
  rw [Fintype.card_eq_nat_card]
  simp only [Row, Nat.card_prod, Nat.card_fin, Nat.card_eq_finsetCard, jetExponents,
    Finset.card_image_of_injective _ hinj, rowCount]
  congr 3
  funext i
  refine Fin.addCases (fun r => ?_) (fun r => ?_) i <;>
    simp [jetWeights, rowWeights, indexEquiv]

def modeEmbedding : ((Fin m → ℕ) × (Fin k → ℕ)) ↪ ((Fin m →₀ ℕ) × (Fin k → ℕ)) :=
  Function.Embedding.prodMap Finsupp.equivFunOnFinite.symm.toEmbedding (Function.Embedding.refl _)

def capacity (w : Fin m → ℚ) (A S H : ℝ) := (lowModes (k := k) w A S H).map modeEmbedding

theorem capacity_card (w : Fin m → ℚ) (A S H : ℝ) :
    (capacity (k := k) w A S H).card = (lowModes (k := k) w A S H).card := by
  simp [capacity]

theorem capacity_covers (w : Fin m → ℚ) (hw : ∀ i, 0 < w i) (A S H : ℝ)
    (g : Fin m →₀ ℕ) (n : Fin k → ℕ)
    (hg : weight (fun i => (w i : ℝ)) g ≤ A*H) (hn : (∑ r, (n r : ℝ)) < S*H) :
    (g,n) ∈ capacity w A S H := by
  apply Finset.mem_map.mpr
  refine ⟨(fun i => g i, n), (mem_lowModes w hw A S H _ _).mpr ⟨hg,hn⟩, ?_⟩
  simp [modeEmbedding]

theorem norm_minor_le (hk : 0 < k)
    (α : Fin k → ℚ) (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ) (D : Data α a p K)
    (v₀ θ : ℚ) (w : Fin m → ℚ) (hv : 0 < v₀) (hθ : 0 < θ) (hw : ∀ i, 0 < w i)
    (hDw : D.w = fun i => (w i : ℝ)) (hDv : D.v₀ = v₀) (hDt : D.θ = θ)
    (H : ℚ) (hH : 0 ≤ H)
    (selection : Row (Fin K) (jetWeights v₀ θ w) H → Column (degreeWeights D.w₀ D.w) H)
    (hcapacity : ((lowModes (k := k) w D.A D.S H).card : ℝ) ≤
      D.η*rowCount (k := k) K v₀ θ w H/2) :
    let M := Fintype.card (Row (Fin K) (jetWeights (k := k) v₀ θ w) H)
    ‖((MultivariateArithmetic.actualMatrix α a p D.T K (degreeWeights D.w₀ D.w)
      (jetWeights v₀ θ w) H).submatrix id selection).det‖ ≤
      (termCount k m D.v₀ H : ℝ)^M*M.factorial*
        Real.exp (-(M : ℝ)*H*D.c+(k*M : ℕ)*Real.log 4) := by
  dsimp only
  have hh := norm_actual_det_le hk D (H : ℝ) (by exact_mod_cast hH)
    (fun ρ : Row (Fin K) (jetWeights v₀ θ w) H => ρ.1)
    (fun ρ => rightIndex ρ.2.val) (fun ρ => leftIndex ρ.2.val)
    (fun ρ => leftIndex (selection ρ).val) (fun ρ => rightIndex (selection ρ).val)
    (fun ρ => by
      change D.w₀*(∑ r, (leftIndex (selection ρ).val r : ℝ))+
        weight D.w (rightIndex (selection ρ).val) ≤ (H : ℝ)
      rw [← split_weight]
      apply (mem_columnExponents _ (fun t => by cases t with
        | inl r => exact D.w₀_pos
        | inr i => exact D.ws_pos.trans_le (D.weights i)) _ _).mp (selection ρ).property)
    (fun ρ => by rw [hDw,hDt]; exact (jet_bounds v₀ θ w hv hθ hw H ρ.2).2)
    (fun ρ => by rw [hDv]; exact (jet_bounds v₀ θ w hv hθ hw H ρ.2).1)
    (capacity w D.A D.S H)
    (fun g n hg hn => capacity_covers w hw D.A D.S H g n (by simpa [hDw] using hg) hn)
    (by simpa only [capacity_card, row_card_eq] using hcapacity)
  simp only [sumElim_indices] at hh
  convert! hh using 1

end
end GeneralizedLogarithms.MultivariateMatrixBounds

/-- info: 'GeneralizedLogarithms.MultivariateMatrixBounds.norm_minor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateMatrixBounds.norm_minor_le
