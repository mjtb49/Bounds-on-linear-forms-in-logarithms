import GeneralizedLogarithms.PersistentLongitudinal
import LogIrrationalityMeasure.Geometry.CurveCenters
import LogIrrationalityMeasure.Geometry.CurvePrimeHeight

/-!
# Longitudinal field-coordinate constancy from persistent components

The kernel of evaluation in a field is prime. Bounded vanishing of the actual
multivariate frame words therefore supplies the initial prime for the checked
persistent-component argument. Its longitudinal equations are evaluated back
in the original field to give constant longitudinal coordinates.

The initial polynomial and word vanishing and numerical weight conditions remain
explicit. The kernel height is computed for a coordinate-generated function
field of transcendence degree one. Constancy and the persistent component are
derived.
-/

namespace GeneralizedLogarithms.MultivariateCurveConstancy

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open LogIrrationalityMeasure.LogExponentApprox
open NormalBasisRigidity CurveCenters CurveValuationCenter
open MultivariatePolynomialFrame MultivariateMultiplicity MultivariatePersistence

section GenericHeight

open LogIrrationalityMeasure.LogExponentJets.W24
open LogIrrationalityMeasure.LogExponentSiegel.W23
open LogIrrationalityMeasure.LogExponentJets.PolynomialLocalResidueResolution

/-- The dimension formula for an arbitrary finite polynomial variable type. -/
theorem height_add_one_eq_of_quotient_dimension
    (F ι : Type*) [Field F] [Finite ι]
    (P : Ideal (MvPolynomial ι F)) [P.IsPrime]
    (hdim : ringKrullDim (MvPolynomial ι F ⧸ P) = 1) :
    P.height + 1 = (Nat.card ι : ℕ∞) := by
  have h := polynomial_prime_pair_local_dimension F ι ⊥ P bot_le
  have hbot : parameterLocalizedIdeal (⊥ : Ideal (MvPolynomial ι F)) P = ⊥ :=
    Ideal.map_bot
  rw [hbot] at h
  have hlocal : ringKrullDim (Localization.AtPrime P ⧸ (⊥ : Ideal (Localization.AtPrime P))) =
      ringKrullDim (Localization.AtPrime P) := by
    with_unfolding_all exact (RingEquiv.quotientBot (Localization.AtPrime P)).ringKrullDim
  have hpoly : ringKrullDim (MvPolynomial ι F ⧸ (⊥ : Ideal (MvPolynomial ι F))) =
      ringKrullDim (MvPolynomial ι F) := by
    with_unfolding_all exact (RingEquiv.quotientBot (MvPolynomial ι F)).ringKrullDim
  rw [hlocal, hpoly, IsLocalization.AtPrime.ringKrullDim_eq_height P
    (Localization.AtPrime P), hdim] at h
  apply WithBot.coe_injective
  simpa only [WithBot.coe_add, WithBot.coe_one,
    MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_natCard,
    zero_add, WithBot.coe_natCast] using h

variable {F K ι : Type*} [Field F] [Field K] [Algebra F K] [Finite ι]

/-- A coordinate-generated curve field has a one-dimensional coordinate ring. -/
theorem quotient_dimension_eq_one (z : ι → K)
    (hgen : IntermediateField.adjoin F (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg F K = 1)
    (P : Ideal (MvPolynomial ι F)) [P.IsPrime]
    (hker : P = RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom) :
    ringKrullDim (MvPolynomial ι F ⧸ P) = 1 := by
  rw [affine_prime_quotient_dimension_eq_residue_trdeg F _ P,
    CurvePrimeHeight.residue_trdeg_toNat_eq z hgen P hker, htrdeg]
  simp

theorem kernel_height_add_one_eq (z : ι → K)
    (hgen : IntermediateField.adjoin F (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg F K = 1) :
    (RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom).height + 1 =
      (Nat.card ι : ℕ∞) := by
  let P := RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom
  let : P.IsPrime := RingHom.ker_isPrime _
  exact height_add_one_eq_of_quotient_dimension F ι P
    (quotient_dimension_eq_one z hgen htrdeg P rfl)

/-- The curve kernel height is the number of coordinates minus one. Positivity
of that number of coordinates follows from the curve field assumptions. -/
theorem kernel_height_eq (z : ι → K)
    (hgen : IntermediateField.adjoin F (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg F K = 1) :
    (RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom).height =
      ((Nat.card ι - 1 : ℕ) : ℕ∞) := by
  have hadd := kernel_height_add_one_eq z hgen htrdeg
  have hcard : 1 ≤ Nat.card ι := by
    have h1 : (1 : ℕ∞) ≤ (Nat.card ι : ℕ∞) := by
      rw [← hadd]
      exact le_add_of_nonneg_left (by simp)
    exact_mod_cast h1
  have hsum : ((Nat.card ι - 1 : ℕ) : ℕ∞) + 1 = (Nat.card ι : ℕ∞) := by
    exact_mod_cast Nat.sub_add_cancel hcard
  apply (WithTop.add_right_inj (show (1 : ℕ∞) ≠ ⊤ by simp)).mp
  simpa only using! (hadd.trans hsum.symm)

end GenericHeight

variable {E : Type*} [Field E] [Algebra ℂ E] {k m : ℕ}

/-- The prime defining the algebraic relations of the field coordinates. -/
def coordinateKernel (z : Fin k ⊕ Fin m → E) : Ideal (Polynomial ℂ k m) :=
  RingHom.ker (MvPolynomial.aeval z).toRingHom

instance coordinateKernel_isPrime (z : Fin k ⊕ Fin m → E) :
    (coordinateKernel z).IsPrime := RingHom.ker_isPrime _

@[simp] theorem mem_coordinateKernel (z : Fin k ⊕ Fin m → E)
    (F : Polynomial ℂ k m) :
    F ∈ coordinateKernel z ↔ MvPolynomial.aeval z F = 0 := Iff.rfl

/-- The actual evaluation kernel of the multivariate curve has height
`k + m - 1`, without assuming a height bound separately. -/
theorem coordinateKernel_height_eq (z : Fin k ⊕ Fin m → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    (coordinateKernel z).height = ((k + m - 1 : ℕ) : ℕ∞) := by
  simpa only [coordinateKernel, Nat.card_sum, Nat.card_fin] using
    kernel_height_eq z hgen htrdeg

/-- One centered place at a nonzero longitudinal center certifies that all
longitudinal field coordinates are nonzero. -/
theorem longitudinal_ne_zero_of_centered (z : Fin k ⊕ Fin m → E)
    (c : Fin k ⊕ Fin m → ℂ) (p : NormalizedPlace ℂ E)
    (hc : Centered z c p) (hcY : ∀ r, c (Sum.inl r) ≠ 0) :
    ∀ r, z (Sum.inl r) ≠ 0 := by
  intro r hz
  have he : (0 : ℂ) = c (Sum.inl r) :=
    hc.constant_coordinate (Sum.inl r) 0 (by simpa only [map_zero] using hz)
  exact hcY r he.symm

/-- The full persistent-component argument applied to the field evaluation
kernel. In particular no constancy or basis-comparison hypothesis is assumed. -/
theorem longitudinal_constants_of_vanishing
    [frameOrder : LinearOrder (Fin k ⊕ Fin m)]
    (z : Fin k ⊕ Fin m → E)
    (a : Fin m → Fin k → ℤ) (hrows : ∀ i, a i ≠ 0)
    (hgeneral : IntegerGeneralPosition a)
    (rho : (Fin k ⊕ Fin m) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : (Fin k ⊕ Fin m) → ℝ) (hcost : ∀ i, 0 < cost i)
    (t : (Fin k ⊕ Fin m) → ℝ) (ht : ∀ i, 0 < t i)
    (θ w₀ v₀ : ℝ) (hv₀ : 0 < v₀)
    (hW : ∀ i, (rho i : ℝ) =
      blockWeight (Finset.univ.image Sum.inr) (fun j => θ * t j) w₀ i)
    (hV : ∀ i, cost i = blockWeight (Finset.univ.image Sum.inr) t v₀ i)
    (epsilon N : ℝ) (hepsilon : 0 < epsilon) (hN : 0 < N)
    (F : Polynomial ℂ k m) (hF : F ≠ 0)
    (hdegree : WeightedSliceDegree.SupportBound (fun j => (rho j : ℝ)) N F)
    (h : ℕ) (hheight : (coordinateKernel z).height ≤ h)
    (hY : ∀ r : Fin k, z (Sum.inl r) ≠ 0)
    (hvanish : ∀ word : List (Fin k ⊕ Fin m),
      wordCost cost word ≤ ((h : ℝ) + 2) * (epsilon * N) →
        MvPolynomial.aeval z (frameWord (fun i r => (a i r : ℂ)) word F) = 0)
    (hn : ∀ q : ℕ, 0 < q → q ≤ k + m →
      ∀ B : Fin q → Fin k ⊕ Fin m, ∀ i,
        2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i)
    (hseparated : ∀ A B : Finset (Fin k ⊕ Fin m), A.card = B.card →
      ∀ i : Fin m, Sum.inr i ∈ A → Sum.inr i ∉ B →
      (∀ j : Fin m, frameOrder.lt (Sum.inr i) (Sum.inr j) →
        (Sum.inr j ∈ A ↔ Sum.inr j ∈ B)) →
      ((A.card : ℝ) ^ A.card / epsilon ^ A.card) * (∏ j ∈ B, cost j) <
        ∏ j ∈ A, (rho j : ℝ))
    (hgap : ∀ r c : ℕ, r < k → 1 ≤ c - r → c - r ≤ k → c ≤ 2 * k - 1 →
      (c : ℝ) ^ c / epsilon ^ c < θ ^ r * (w₀ / v₀) ^ (c - r)) :
    ∀ r : Fin k, ∃ b : ℂ, z (Sum.inl r) = algebraMap ℂ E b := by
  have hYP : ∀ r : Fin k, MvPolynomial.X (Sum.inl r) ∉ coordinateKernel z := by
    intro r hr
    exact hY r (by simpa only [mem_coordinateKernel, MvPolynomial.aeval_X] using hr)
  obtain ⟨s, hs, Q, hQ, hQne, hQP, hQlo, hQhi, hQr, hconstant⟩ :=
    PersistentLongitudinal.exists_persistent_longitudinal_equations
      a hrows hgeneral rho hrho cost hcost t ht θ w₀ v₀ hv₀ hW hV
      epsilon N hepsilon hN F hF hdegree h (coordinateKernel z) inferInstance hheight hYP
      hvanish hn hseparated hgap
  intro r
  obtain ⟨b, _, hb⟩ := hconstant r
  refine ⟨b, ?_⟩
  simpa only [mem_coordinateKernel, map_sub, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C, sub_eq_zero] using hb

end
end GeneralizedLogarithms.MultivariateCurveConstancy

/-- info: 'GeneralizedLogarithms.MultivariateCurveConstancy.coordinateKernel_height_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCurveConstancy.coordinateKernel_height_eq

/-- info: 'GeneralizedLogarithms.MultivariateCurveConstancy.longitudinal_ne_zero_of_centered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCurveConstancy.longitudinal_ne_zero_of_centered

/-- info: 'GeneralizedLogarithms.MultivariateCurveConstancy.longitudinal_constants_of_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCurveConstancy.longitudinal_constants_of_vanishing
