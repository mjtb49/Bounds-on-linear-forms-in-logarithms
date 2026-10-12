import GeneralizedLogarithms.MultivariateMixedSeries
import GeneralizedLogarithms.MultivariateArithmetic

/-!
# Exact row translation in several logarithmic variables

The error is the actual integer linear form, multiplied by the center index.
No approximation or analytic estimate is used in the finite identity.
-/

namespace GeneralizedLogarithms.MultivariateRowTranslation

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open MultivariateMixedSeries RowTranslation

variable {k m : ℕ}

def periodCoordinate (a : Fin m → Fin k → ℤ) (ω : Fin k → ℂ) (j : ℕ)
    (i : Fin m) : MvPowerSeries (Fin k) ℂ :=
  ∑ r, MvPowerSeries.C (a i r : ℂ) *
    (MvPowerSeries.C ((j : ℂ) * ω r) + (PowerSeries.log ℂ).toMvPowerSeries r)

def truncatedCoordinate (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ) (T : Fin m → ℕ)
    (j : ℕ) (i : Fin m) : MvPowerSeries (Fin k) ℂ :=
  MvPowerSeries.C (-(j : ℂ) * (p i : ℂ)) + ∑ r, MvPowerSeries.C (a i r : ℂ) *
    (PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ).toMvPowerSeries r

def error (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ) (ω : Fin k → ℂ) (j : ℕ)
    (i : Fin m) : ℂ := -(j : ℂ) * ((p i : ℂ) + ∑ r, (a i r : ℂ) * ω r)

def tail (a : Fin m → Fin k → ℤ) (T : Fin m → ℕ) (i : Fin m) :
    MvPowerSeries (Fin k) ℂ :=
  ∑ r, MvPowerSeries.C (a i r : ℂ) *
    (RowTranslation.tail (T i) (PowerSeries.log ℂ)).toMvPowerSeries r

theorem coordinate_translation (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ)
    (ω : Fin k → ℂ) (T : Fin m → ℕ) (j : ℕ) (i : Fin m) :
    periodCoordinate a ω j i + (MvPowerSeries.C (error a p ω j i) + tail a T i) =
      truncatedCoordinate a p T j i := by
  simp only [periodCoordinate, error, tail, truncatedCoordinate, RowTranslation.tail,
    map_sub, map_add, map_mul, map_neg, map_sum, mul_sub, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have he : (∑ r, MvPowerSeries.C (σ := Fin k) (a i r : ℂ) * (MvPowerSeries.C (j : ℂ) * MvPowerSeries.C (ω r))) =
      ∑ r, MvPowerSeries.C (j : ℂ) * (MvPowerSeries.C (a i r : ℂ) * MvPowerSeries.C (ω r)) := by
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [he]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

def periodMonomial (y ω : Fin k → ℂ) (a : Fin m → Fin k → ℤ) (j : ℕ)
    (h : Fin k →₀ ℕ) (b : Fin m →₀ ℕ) : MvPolynomial (Fin m) (MvPowerSeries (Fin k) ℂ) :=
  MvPolynomial.C (∏ r, (MvPowerSeries.C (y r ^ j) * (1 + MvPowerSeries.X r)) ^ h r) *
    ∏ i, (MvPolynomial.C (periodCoordinate a ω j i) + MvPolynomial.X i) ^ b i

def truncatedMonomial (y : Fin k → ℂ) (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ)
    (T : Fin m → ℕ) (j : ℕ) (h : Fin k →₀ ℕ) (b : Fin m →₀ ℕ) :
    MvPolynomial (Fin m) (MvPowerSeries (Fin k) ℂ) :=
  MvPolynomial.C (∏ r, (MvPowerSeries.C (y r ^ j) * (1 + MvPowerSeries.X r)) ^ h r) *
    ∏ i, (MvPolynomial.C (truncatedCoordinate a p T j i) + MvPolynomial.X i) ^ b i

theorem monomial_shift (y ω : Fin k → ℂ) (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ)
    (T : Fin m → ℕ) (j : ℕ) (h : Fin k →₀ ℕ) (b : Fin m →₀ ℕ) :
    RowTranslation.shift (fun i => MvPowerSeries.C (error a p ω j i) + tail a T i)
      (periodMonomial y ω a j h b) = truncatedMonomial y a p T j h b := by
  simp only [periodMonomial, truncatedMonomial, map_mul, map_prod, map_pow, map_add,
    shift_C, shift_X]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  calc
    _ = MvPolynomial.C (periodCoordinate a ω j i +
        (MvPowerSeries.C (error a p ω j i) + tail a T i)) + MvPolynomial.X i := by
      simp only [map_add]
      ring
    _ = _ := by rw [coordinate_translation]

def mixedJet (α : Fin k → ℚ) (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ)
    (T : Fin m → ℕ) (j : ℕ) :
    MvPolynomial (Fin k ⊕ Fin m) ℂ →+* MvPolynomial (Fin m) (MvPowerSeries (Fin k) ℂ) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPowerSeries.C)
    (Sum.elim (fun r => MvPolynomial.C (MvPowerSeries.C ((α r : ℂ) ^ j) * (1 + MvPowerSeries.X r)))
      (fun i => MvPolynomial.C (truncatedCoordinate a p T j i) + MvPolynomial.X i))

theorem embed_mixedJet (α : Fin k → ℚ) (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ)
    (T : Fin m → ℕ) (j : ℕ) :
    embed.comp (mixedJet α a p T j) = (MultivariateArithmetic.jet α a p T j).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [mixedJet, MultivariateArithmetic.jet, MultivariateLogPolynomialAdapter.truncatedFormalJet,
      MvPowerSeries.algebraMap_apply]
  · intro s
    cases s with
    | inl r =>
      simp [mixedJet, MultivariateArithmetic.jet, MultivariateFormalLogShift.truncatedFormalJet_Y,
        MultivariateArithmetic.center, MultivariateRationalJet.approximationCenter_Y]
    | inr i =>
      simp [mixedJet, truncatedCoordinate, MultivariateArithmetic.jet,
        MultivariateFormalLogShift.truncatedFormalJet_X, MultivariateArithmetic.center,
        MultivariateRationalJet.approximationCenter_X, MvPowerSeries.rename_toMvPowerSeries,
        add_right_comm]

theorem mixedJet_monomial (α : Fin k → ℚ) (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ)
    (T : Fin m → ℕ) (j : ℕ) (h : Fin k →₀ ℕ) (b : Fin m →₀ ℕ) :
    mixedJet α a p T j (MvPolynomial.monomial (h.sumElim b) 1) =
      truncatedMonomial (fun r => (α r : ℂ)) a p T j h b := by
  rw [mixedJet, MvPolynomial.eval₂Hom_monomial, map_one, one_mul, Finsupp.prod_sumElim]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, truncatedMonomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod]
  simp only [map_pow]

section Coefficients
variable {σ τ R : Type*} [DecidableEq σ] [Fintype τ] [DecidableEq τ] [CommRing R]

def rowScalar (ε : τ → R) (τail : τ → MvPowerSeries σ R)
    (β A : τ →₀ ℕ) (d : ∀ i, Fin (A i - β i + 1)) (s : σ →₀ ℕ) : R :=
  ((∏ i, (A i).choose (β i) * (A i - β i).choose (d i) : ℕ) : R) *
    (∏ i, ε i ^ (A i - β i - d i)) * MvPowerSeries.coeff s (∏ i, τail i ^ (d i : ℕ))

theorem coeff_shiftCoefficient (ε : τ → R) (τail : τ → MvPowerSeries σ R)
    (β A : τ →₀ ℕ) (s : σ →₀ ℕ) :
    MvPowerSeries.coeff s (shiftCoefficient (fun i => MvPowerSeries.C (ε i) + τail i) β A) =
      ∑ d : (∀ i, Fin (A i - β i + 1)), rowScalar ε τail β A d s := by
  rw [shiftCoefficient_eq, Finset.prod_mul_distrib, product_add_expansion]
  simp only [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [rowScalar, Finset.prod_mul_distrib, Nat.cast_mul]
  simp only [← map_pow, ← map_prod]
  rw [show (∏ i, ((A i).choose (β i) : MvPowerSeries σ R)) =
    MvPowerSeries.C ((∏ i, (A i).choose (β i) : ℕ) : R) by simp]
  rw [show ((∏ i, (A i - β i).choose (d i) : ℕ) : MvPowerSeries σ R) =
    MvPowerSeries.C ((∏ i, (A i - β i).choose (d i) : ℕ) : R) by simp]
  simp only [← map_mul, mul_assoc, MvPowerSeries.coeff_C_mul]

theorem exact_row_identity (ε : τ → R) (τail : τ → MvPowerSeries σ R)
    (P : MvPolynomial τ (MvPowerSeries σ R)) (β : τ →₀ ℕ)
    (S : Finset (τ →₀ ℕ)) (hP : P.support ⊆ S) (s : σ →₀ ℕ) :
    MvPowerSeries.coeff s ((shift (fun i => MvPowerSeries.C (ε i) + τail i) P).coeff β) =
      ∑ A ∈ S, ∑ d : (∀ i, Fin (A i - β i + 1)),
        ∑ uv ∈ Finset.HasAntidiagonal.antidiagonal s,
          rowScalar ε τail β A d uv.1 * MvPowerSeries.coeff uv.2 (P.coeff A) := by
  classical
  rw [coeff_shift_over _ P β S hP]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [mul_comm, MvPowerSeries.coeff_mul]
  simp only [coeff_shiftCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]

end Coefficients

theorem actual_jet_row_identity (α : Fin k → ℚ) (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ)
    (ω : Fin k → ℂ) (T : Fin m → ℕ) (j : ℕ) (h : Fin k →₀ ℕ) (b β : Fin m →₀ ℕ)
    (s : Fin k →₀ ℕ) :
    MvPowerSeries.coeff (s.sumElim β)
      (MultivariateArithmetic.jet α a p T j (MvPolynomial.monomial (h.sumElim b) 1)) =
      ∑ A ∈ (periodMonomial (fun r => (α r : ℂ)) ω a j h b).support,
        ∑ d : (∀ i, Fin (A i - β i + 1)),
          ∑ uv ∈ Finset.HasAntidiagonal.antidiagonal s,
            rowScalar (error a p ω j) (tail a T) β A d uv.1 *
              MvPowerSeries.coeff uv.2 ((periodMonomial (fun r => (α r : ℂ)) ω a j h b).coeff A) := by
  have he := RingHom.congr_fun (embed_mixedJet α a p T j) (MvPolynomial.monomial (h.sumElim b) 1)
  rw [RingHom.comp_apply, mixedJet_monomial] at he
  change embed (truncatedMonomial (fun r => (α r : ℂ)) a p T j h b) =
    MultivariateArithmetic.jet α a p T j (MvPolynomial.monomial (h.sumElim b) 1) at he
  rw [← he, ← monomial_shift (fun r => (α r : ℂ)) ω a p T j h b, coeff_embed]
  exact exact_row_identity _ _ _ β _ (Finset.Subset.refl _) s

end
end GeneralizedLogarithms.MultivariateRowTranslation

/-- info: 'GeneralizedLogarithms.MultivariateRowTranslation.actual_jet_row_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateRowTranslation.actual_jet_row_identity
