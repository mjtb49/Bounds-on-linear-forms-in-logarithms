import GeneralizedLogarithms.MultivariateColumnSeries
import LogIrrationalityMeasure.Approximation.MatrixTranslation

/-! Finite row choices for the actual multivariate interpolation matrix. -/

namespace GeneralizedLogarithms.MultivariateMatrixTranslation

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open MultivariateRowTranslation MultivariateColumnSeries MultivariateMixedSeries

variable {k m : ℕ}

theorem periodMonomial_support_le (y ω : Fin k → ℂ) (a : Fin m → Fin k → ℤ)
    (j : ℕ) (h : Fin k →₀ ℕ) (b γ : Fin m →₀ ℕ)
    (hγ : γ ∈ (periodMonomial y ω a j h b).support) : γ ≤ b := by
  by_contra hn
  have hz := transversePolynomial_eq_zero_of_not_le a b γ hn
  apply (MvPolynomial.mem_support_iff.mp hγ)
  rw [periodMonomial_coeff, hz]
  simp [MultivariateTensorCoefficients.formalPolynomialRow]

theorem periodMonomial_support_subset (y ω : Fin k → ℂ) (a : Fin m → Fin k → ℤ)
    (j : ℕ) (h : Fin k →₀ ℕ) (b : Fin m →₀ ℕ) (w : Fin m → ℝ) (H : ℝ)
    (hw : ∀ i, 0 < w i) (hb : ∑ i, w i * b i ≤ H) :
    (periodMonomial y ω a j h b).support ⊆ MatrixTranslation.transverseIndices w H := by
  intro γ hγ
  apply (MatrixTranslation.mem_transverseIndices w H hw γ).mpr
  exact (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (periodMonomial_support_le y ω a j h b γ hγ i)) (hw i).le).trans hb

def RowChoices (S : Finset (Fin m →₀ ℕ)) (β : Fin m →₀ ℕ) (s : Fin k →₀ ℕ) :=
  Σ A : S, (∀ i, Fin (A.val i - β i + 1)) ×
    {uv : (Fin k →₀ ℕ) × (Fin k →₀ ℕ) // uv ∈ Finset.HasAntidiagonal.antidiagonal s}

instance (S : Finset (Fin m →₀ ℕ)) (β : Fin m →₀ ℕ) (s : Fin k →₀ ℕ) :
    Fintype (RowChoices S β s) := by unfold RowChoices; infer_instance

theorem actual_jet_row_choices (α : Fin k → ℚ) (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ)
    (ω : Fin k → ℂ) (T : Fin m → ℕ) (j : ℕ) (h : Fin k →₀ ℕ) (b β : Fin m →₀ ℕ)
    (s : Fin k →₀ ℕ) (S : Finset (Fin m →₀ ℕ))
    (hp : (periodMonomial (fun r => (α r : ℂ)) ω a j h b).support ⊆ S) :
    MvPowerSeries.coeff (s.sumElim β)
      (MultivariateArithmetic.jet α a p T j (MvPolynomial.monomial (h.sumElim b) 1)) =
      ∑ t : RowChoices S β s,
        rowScalar (error a p ω j) (tail a T) β t.1.val t.2.1 t.2.2.val.1 *
          MvPowerSeries.coeff t.2.2.val.2
            ((periodMonomial (fun r => (α r : ℂ)) ω a j h b).coeff t.1.val) := by
  have he := RingHom.congr_fun (embed_mixedJet α a p T j) (MvPolynomial.monomial (h.sumElim b) 1)
  rw [RingHom.comp_apply, mixedJet_monomial] at he
  change embed (truncatedMonomial (fun r => (α r : ℂ)) a p T j h b) =
    MultivariateArithmetic.jet α a p T j (MvPolynomial.monomial (h.sumElim b) 1) at he
  rw [← he, ← monomial_shift (fun r => (α r : ℂ)) ω a p T j h b, coeff_embed,
    exact_row_identity _ _ _ β S hp s]
  change _ = ∑ t : (Σ A : S, (∀ i, Fin (A.val i - β i + 1)) ×
    {uv : (Fin k →₀ ℕ) × (Fin k →₀ ℕ) // uv ∈ Finset.HasAntidiagonal.antidiagonal s}), _
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro d hd
  exact (Finset.sum_coe_sort _ _).symm

theorem antidiagonal_card_le (s : Fin k →₀ ℕ) (N : ℕ) (hs : s.degree ≤ N) :
    (Finset.HasAntidiagonal.antidiagonal s).card ≤ (N + 1)^k := by
  classical
  let box := Fintype.piFinset (fun _ : Fin k => Finset.range (N+1))
  have hcard : (Finset.HasAntidiagonal.antidiagonal s).card ≤ box.card := by
    apply Finset.card_le_card_of_injOn (fun uv : (Fin k →₀ ℕ) × (Fin k →₀ ℕ) => fun r => uv.1 r)
    · intro uv huv
      have huv' : uv.1 + uv.2 = s := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
      apply Fintype.mem_piFinset.mpr
      intro r
      apply Finset.mem_range.mpr
      have hr : uv.1 r ≤ s r := by have hh := congrArg (fun e => e r) huv'; simp only [Finsupp.add_apply] at hh; omega
      have hs' : s r ≤ s.degree := by
        rw [Finsupp.degree_eq_sum]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
      exact Nat.lt_succ_of_le ((hr.trans hs').trans hs)
    · intro uv huv xy hxy he
      have hleft : uv.1 = xy.1 := Finsupp.ext (fun r => congrFun he r)
      have h1 : uv.1 + uv.2 = s := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
      have h2 : xy.1 + xy.2 = s := Finset.HasAntidiagonal.mem_antidiagonal.mp hxy
      apply Prod.ext hleft
      rw [hleft] at h1
      exact add_left_cancel (h1.trans h2.symm)
  simpa [box, Fintype.card_piFinset] using hcard

theorem rowChoices_card_le (w : Fin m → ℝ) (H v : ℝ) (hw : ∀ i, 1 ≤ w i)
    (β : Fin m →₀ ℕ) (s : Fin k →₀ ℕ) (hs : (s.degree : ℝ) ≤ H / v) :
    Fintype.card (RowChoices (MatrixTranslation.transverseIndices w H) β s) ≤
      (⌊H⌋₊ + 1)^(2*m) * (⌊H/v⌋₊+1)^k := by
  classical
  let S := MatrixTranslation.transverseIndices w H
  have ha := antidiagonal_card_le s ⌊H/v⌋₊ (Nat.le_floor hs)
  have hbound (A : S) : (∏ i, (A.val i - β i + 1)) ≤ (⌊H⌋₊+1)^m := by
    calc
      _ ≤ ∏ _ : Fin m, (⌊H⌋₊+1) := Finset.prod_le_prod' (fun i _ => by
        have hh := MatrixTranslation.transverseIndices_coordinate_le w H hw A.property i
        omega)
      _ = _ := by simp
  calc
    _ = ∑ A : S, (∏ i, (A.val i - β i + 1)) * (Finset.HasAntidiagonal.antidiagonal s).card := by
      simp [RowChoices, Fintype.card_sigma, Fintype.card_prod, Fintype.card_pi, S]
    _ ≤ ∑ _A : S, (⌊H⌋₊+1)^m * (⌊H/v⌋₊+1)^k :=
      Finset.sum_le_sum (fun A _ => Nat.mul_le_mul (hbound A) ha)
    _ = S.card * ((⌊H⌋₊+1)^m * (⌊H/v⌋₊+1)^k) := by simp
    _ ≤ (⌊H⌋₊+1)^m * ((⌊H⌋₊+1)^m * (⌊H/v⌋₊+1)^k) :=
      Nat.mul_le_mul_right _ (MatrixTranslation.transverseIndices_card_le w H hw)
    _ = _ := by rw [show 2*m=m+m by omega, pow_add]; ring

end
end GeneralizedLogarithms.MultivariateMatrixTranslation

/-- info: 'GeneralizedLogarithms.MultivariateMatrixTranslation.actual_jet_row_choices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateMatrixTranslation.actual_jet_row_choices

/-- info: 'GeneralizedLogarithms.MultivariateMatrixTranslation.rowChoices_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateMatrixTranslation.rowChoices_card_le
