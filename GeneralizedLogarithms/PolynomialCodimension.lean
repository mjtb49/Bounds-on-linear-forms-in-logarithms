import GeneralizedLogarithms.PolynomialPrimeAdapter
import GeneralizedLogarithms.LongitudinalComparison
import LogIrrationalityMeasure.Approximation.GenericNormalRigidity

/-!
# Codimension bounds for a mandatory transverse set

The actual polynomial normal quotient has dimension `c` between `r+1` and
`r+k`, where `r` is the size of the greedy transverse set. The empty set case
uses the nonzero defining ideal; the nonempty case uses one nonzero exponent
row and the constancy obstruction. Thus the small-rank branch has a
codimension cap depending only on `k`, including when `r = 0`.
-/

namespace GeneralizedLogarithms.PolynomialCodimension

noncomputable section

open MvPolynomial
open LogIrrationalityMeasure.LogExponent
open LogIrrationalityMeasure.LogExponent.NormalBasisRigidity
open PolynomialPrimeAdapter

variable {C E : Type*} [Field C] [CharZero C] [IsAlgClosed C]
  [Field E] [Algebra C E] [Algebra.EssFiniteType C E] {k m : ℕ}

omit [IsAlgClosed C] [Algebra.EssFiniteType C E] in
theorem polynomialNormal_finrank_pos
    (φ : MvPolynomial (Fin k ⊕ Fin m) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin k ⊕ Fin m) C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥) :
    0 < Module.finrank E (PolynomialNormal φ Q) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  by_contra h
  push Not at h
  apply polynomialNormal_mkQ_ne_zero_of_kernel φ Q hker hQ
  ext t
  exact h _

/-- The lower and upper codimension bounds, including the empty transverse
set. Nonzero rows are required only on the selected set. -/
theorem codimension_bounds_of_mandatory_greedy_set
    [frameOrder : LinearOrder (Fin k ⊕ Fin m)]
    (φ : MvPolynomial (Fin k ⊕ Fin m) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin k ⊕ Fin m) C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥)
    (a : Fin m → Fin k → ℤ) (hy : ∀ r : Fin k, φ (X (Sum.inl r)) ≠ 0)
    (J : Finset (Fin m))
    (hJ : IsGreedyBasis (K := E) (coordinateNormalFamily φ Q)
      (Finset.univ.image Sum.inr) (J.image Sum.inr))
    (hrows : ∀ i ∈ J, a i ≠ 0)
    (hmandatory : ∀ i ∈ J, ∀ B,
      IsNormalBasis (K := E) (frameNormalFamily φ Q a hy) B → Sum.inr i ∈ B) :
    J.card + 1 ≤ Module.finrank E (PolynomialNormal φ Q) ∧
      Module.finrank E (PolynomialNormal φ Q) ≤ J.card + k := by
  classical
  constructor
  · by_cases hne : J.Nonempty
    · obtain ⟨i, hi⟩ := hne
      let e : J ↪ Fin m := ⟨Subtype.val, Subtype.val_injective⟩
      have h := mandatory_directions_codimension_gap φ Q hker e ⟨i, hi⟩ a hy
        (hrows i hi) (fun j B hB => hmandatory j j.property B hB)
      simpa using h
    · have hzero : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hpos := polynomialNormal_finrank_pos φ Q hker hQ
      simp only [hzero, Finset.card_empty]
      omega
  · obtain ⟨A, hA, hAX⟩ := exists_normalBasis_with_intersection
      (coordinateNormalFamily φ Q)
      (polynomialNormal_span φ Q (Pi.basisFun E _))
      (Finset.univ.image Sum.inr) (J.image Sum.inr) hJ.1 hJ.2.1 hJ.span_eq
    have hcomp : (Finset.univ : Finset (Fin k ⊕ Fin m)) \
        Finset.univ.image Sum.inr = Finset.univ.image Sum.inl := by
      ext j
      cases j <;> simp
    have hd : (A \ Finset.univ.image Sum.inr).card ≤
        ((Finset.univ : Finset (Fin k ⊕ Fin m)) \ Finset.univ.image Sum.inr).card := by
      apply Finset.card_le_card
      intro j hj
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, (Finset.mem_sdiff.mp hj).2⟩
    have hc := Finset.card_sdiff_add_card_inter A (Finset.univ.image Sum.inr)
    rw [hAX, hA.card_eq] at hc
    rw [hcomp] at hd
    have hJcard : (J.image (Sum.inr : Fin m → Fin k ⊕ Fin m)).card = J.card :=
      Finset.card_image_of_injective _ Sum.inr_injective
    have hYcard : (Finset.univ.image (Sum.inl : Fin k → Fin k ⊕ Fin m)).card = k := by
      rw [Finset.card_image_of_injective _ Sum.inl_injective]
      simp
    rw [hJcard] at hc
    rw [hYcard] at hd
    change Module.finrank E (((Fin k ⊕ Fin m) → E) ⧸ polynomialTangent φ Q) ≤ J.card + k
    omega

/-- In the small-rank case, only codimensions at most `2*k-1` can occur.
This supplies the cap used in the longitudinal multiplicity constant. -/
theorem small_rank_codimension_range
    [frameOrder : LinearOrder (Fin k ⊕ Fin m)]
    (φ : MvPolynomial (Fin k ⊕ Fin m) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin k ⊕ Fin m) C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥)
    (a : Fin m → Fin k → ℤ) (hy : ∀ r : Fin k, φ (X (Sum.inl r)) ≠ 0)
    (J : Finset (Fin m))
    (hJ : IsGreedyBasis (K := E) (coordinateNormalFamily φ Q)
      (Finset.univ.image Sum.inr) (J.image Sum.inr))
    (hrows : ∀ i ∈ J, a i ≠ 0)
    (hmandatory : ∀ i ∈ J, ∀ B,
      IsNormalBasis (K := E) (frameNormalFamily φ Q a hy) B → Sum.inr i ∈ B)
    (hrk : J.card < k) :
    let c := Module.finrank E (PolynomialNormal φ Q)
    1 ≤ c - J.card ∧ c - J.card ≤ k ∧ c ≤ 2 * k - 1 := by
  obtain ⟨hlower, hupper⟩ := codimension_bounds_of_mandatory_greedy_set
    φ Q hker hQ a hy J hJ hrows hmandatory
  exact small_rank_dimension_range k J.card _ hrk (by omega) hupper

end
end GeneralizedLogarithms.PolynomialCodimension

/-- info: 'GeneralizedLogarithms.PolynomialCodimension.codimension_bounds_of_mandatory_greedy_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.PolynomialCodimension.codimension_bounds_of_mandatory_greedy_set

/-- info: 'GeneralizedLogarithms.PolynomialCodimension.small_rank_codimension_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.PolynomialCodimension.small_rank_codimension_range
