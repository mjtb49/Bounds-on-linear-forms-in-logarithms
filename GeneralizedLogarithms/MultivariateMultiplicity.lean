import GeneralizedLogarithms.MultivariatePolynomialFrame
import LogIrrationalityMeasure.Jets.TaylorRectangular
import LogIrrationalityMeasure.Jets.PrimeTaylorCotangent

/-!
# Rectangular local multiplicity for the multivariate frame

Weighted vanishing of words in the polynomial frame gives vanishing of a
rectangle of Taylor coefficients. The first Taylor coefficients are the
actual normal frame columns. Independence in the polynomial normal quotient
therefore makes the induced cotangent map surjective, giving the rectangle's
cardinality as a lower bound for the localized quotient length.
-/

namespace GeneralizedLogarithms
namespace MultivariateMultiplicity

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open LogIrrationalityMeasure.LogExponent.CommutingTaylor
open LogIrrationalityMeasure.LogExponent.TaylorRectangular
open LogIrrationalityMeasure.LogExponentApprox.TransverseMultiplicity

section Words

variable {R ι : Type*} [CommRing R] [Algebra ℚ R]

/-- Apply the indicated derivations in the listed order. -/
def derivationWord (D : ι → Derivation ℚ R R) : List ι → R → R
  | [], p => p
  | j :: word, p => D j (derivationWord D word p)

/-- Total cost of a derivation word. -/
def wordCost (cost : ι → ℝ) (word : List ι) : ℝ := (word.map cost).sum

theorem derivationWord_append (D : ι → Derivation ℚ R R) (u v : List ι) (p : R) :
    derivationWord D (u ++ v) p = derivationWord D u (derivationWord D v p) := by
  induction u with
  | nil => rfl
  | cons i u ih => simp only [List.cons_append, derivationWord, ih]

theorem derivationWord_replicate (D : ι → Derivation ℚ R R) (i : ι) (n : ℕ) (p : R) :
    derivationWord D (List.replicate n i) p = iter (D i) n p := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, derivationWord, ih]

theorem mixedIter_eq_derivationWord (D : ι → Derivation ℚ R R)
    (q : ℕ) (B : Fin q → ι) (α : Fin q →₀ ℕ) (p : R) :
    mixedIter q (fun j => D (B j)) α p = derivationWord D (derivativeWord q B α) p := by
  induction q generalizing p with
  | zero => rfl
  | succ q ih =>
    simp only [mixedIter, LinearMap.comp_apply, derivativeWord, derivationWord_append,
      derivationWord_replicate]
    exact ih (fun i => B i.succ) α.tail _

theorem derivativeWord_wordCost (q : ℕ) (B : Fin q → ι)
    (α : Fin q →₀ ℕ) (cost : ι → ℝ) :
    wordCost cost (derivativeWord q B α) = ∑ j, (α j : ℝ) * cost (B j) := by
  induction q with
  | zero => simp [derivativeWord, wordCost]
  | succ q ih =>
    simp only [derivativeWord, wordCost, List.map_append, List.sum_append,
      List.map_replicate, List.sum_replicate]
    change wordCost cost (derivativeWord q (fun i => B i.succ) α.tail) +
      (α 0) • cost (B 0) = _
    rw [ih, Fin.sum_univ_succ]
    simp only [Finsupp.tail_apply, nsmul_eq_mul]
    ring

theorem derivativeWord_wordCost_le (q : ℕ) (B : Fin q → ι)
    (α : Fin q →₀ ℕ) (cost : ι → ℝ) (n : Fin q → ℕ) (δ : ℝ)
    (hcost : ∀ j, 0 ≤ cost j) (hα : ∀ j, α j < n j)
    (hn : ∑ j, ((n j - 1 : ℕ) : ℝ) * cost (B j) ≤ δ) :
    wordCost cost (derivativeWord q B α) ≤ δ := by
  rw [derivativeWord_wordCost]
  apply le_trans _ hn
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (hcost _)
  exact_mod_cast (by have := hα j; omega : α j ≤ n j - 1)

end Words

open MultivariatePolynomialFrame

variable {C : Type*} [Field C] [CharZero C] {k m : ℕ}

/-- Restriction of the polynomial frame to rational scalars for Taylor series. -/
def rationalFrame (a : Fin m → Fin k → C) (j : Fin k ⊕ Fin m) :
    Derivation ℚ (Polynomial C k m) (Polynomial C k m) :=
  (polynomialFrame a j).restrictScalars ℚ

/-- Words in the actual multivariate polynomial frame. -/
def frameWord (a : Fin m → Fin k → C) (word : List (Fin k ⊕ Fin m))
    (p : Polynomial C k m) : Polynomial C k m :=
  derivationWord (rationalFrame a) word p

/-- The actual prime local quotient has length at least the size of the Taylor
rectangle when frame words vanish within its cost budget. -/
theorem prime_frame_rectangular_length_lower
    (a : Fin m → Fin k → C) (q : ℕ)
    (Q : Ideal (Polynomial C k m)) [Q.IsPrime]
    (hy : ∀ r : Fin k, primeResidueMap Q (MvPolynomial.X (Sum.inl r)) ≠ 0)
    (B : Fin q → (Fin k ⊕ Fin m))
    (hB : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (MultivariateFrame.frameBasis
          (fun i r => primeResidueMap Q (MvPolynomial.C (a i r)))
          (fun r => primeResidueMap Q (MvPolynomial.X (Sum.inl r))) hy (B j))))
    (I : Ideal (Polynomial C k m)) (cost : (Fin k ⊕ Fin m) → ℝ)
    (n : Fin q → ℕ) (δ : ℝ) (hn : ∀ j, 2 ≤ n j)
    (hcost : ∀ j, 0 ≤ cost j)
    (hbudget : ∑ j, ((n j - 1 : ℕ) : ℝ) * cost (B j) ≤ δ)
    (hvanish : ∀ p ∈ I, ∀ word : List (Fin k ⊕ Fin m),
      wordCost cost word ≤ δ → frameWord a word p ∈ Q) :
    (∏ j, n j : ℕ) ≤ Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map
        (algebraMap (Polynomial C k m) (Localization.AtPrime Q))) := by
  let ρ := algebraMap (Localization.AtPrime Q) Q.ResidueField
  let τ₀ := residueTaylorFin q (fun j => rationalFrame a (B j))
    (ρ.comp (algebraMap (Polynomial C k m) (Localization.AtPrime Q)))
  have hzero₀ : ∀ p, MvPowerSeries.constantCoeff (τ₀ p) =
      ρ (algebraMap (Polynomial C k m) (Localization.AtPrime Q) p) :=
    constantCoeff_residueTaylorFin _ _ _
  let τ := localizedTaylorMap Q.primeCompl τ₀ ρ hzero₀
  have hzero : ∀ x, MvPowerSeries.constantCoeff (τ x) = ρ x := fun x =>
    RingHom.congr_fun (localizedTaylorMap_constant Q.primeCompl τ₀ ρ hzero₀) x
  let v := fun j => MultivariateFrame.frameBasis
    (fun i r => primeResidueMap Q (MvPolynomial.C (a i r)))
    (fun r => primeResidueMap Q (MvPolynomial.X (Sum.inl r))) hy (B j)
  have hfirst : ∀ j x, MvPowerSeries.coeff (Finsupp.single j 1) (τ x) =
      primeLocalDirectional Q (v j) x := by
    intro j x
    apply prime_localizedTaylor_firstCoefficient Q τ₀ hzero₀ v
    intro l p
    rw [coeff_single_residueTaylorFin]
    change ρ (algebraMap (Polynomial C k m) (Localization.AtPrime Q)
      (polynomialFrame a (B l) p)) = _
    dsimp only [ρ]
    rw [← IsScalarTower.algebraMap_apply]
    exact residue_polynomialFrame_eq_frameBasis_dot a (primeResidueMap Q).toRingHom hy (B l) p
  have hCot := prime_rectangular_mapCotangent_surjective Q τ hzero v hB hfirst n hn
  have hP : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤ RingHom.ker ρ := by
    rw [show RingHom.ker ρ = IsLocalRing.maximalIdeal (Localization.AtPrime Q)
      from IsLocalRing.ker_residue]
  have hbase : I ≤ (rectangularIdeal (K := Q.ResidueField) n).comap τ₀ := by
    intro p hp
    apply residueTaylor_mem_rectangular
    intro α hα
    rw [mixedIter_eq_derivationWord]
    change ρ (algebraMap (Polynomial C k m) (Localization.AtPrime Q)
      (frameWord a (derivativeWord q B α) p)) = 0
    dsimp only [ρ]
    rw [← IsScalarTower.algebraMap_apply]
    apply Ideal.algebraMap_residueField_eq_zero.mpr
    exact hvanish p hp _ (derivativeWord_wordCost_le q B α cost n δ hcost hα hbudget)
  have hlocalized := localizedTaylorMap_ideal_le Q.primeCompl τ₀ ρ hzero₀ n I hbase
  exact rectangularTaylor_length_lower n (rectangularPositive n hn) τ ρ
    IsLocalRing.residue_surjective hzero (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    _ hP hCot hlocalized

end
end MultivariateMultiplicity
end GeneralizedLogarithms

/-- info: 'GeneralizedLogarithms.MultivariateMultiplicity.mixedIter_eq_derivationWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateMultiplicity.mixedIter_eq_derivationWord

/-- info: 'GeneralizedLogarithms.MultivariateMultiplicity.derivativeWord_wordCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateMultiplicity.derivativeWord_wordCost_le

/-- info: 'GeneralizedLogarithms.MultivariateMultiplicity.prime_frame_rectangular_length_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateMultiplicity.prime_frame_rectangular_length_lower
