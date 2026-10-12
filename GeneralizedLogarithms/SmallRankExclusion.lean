import GeneralizedLogarithms.PolynomialCodimension
import GeneralizedLogarithms.GenericConstancy

/-!
# Excluding a small mandatory transverse set

For the actual polynomial normal quotient, constancy gives a strict
codimension lower bound and greedy extension gives the upper bound. In the
branch with fewer than `k` mandatory transverse directions, the codimension is
therefore at most `2*k-1`. Canceling the common transverse weights in two
normal bases contradicts the supplied longitudinal parameter gap.

Universal basis comparison, directed weight separation, and the numerical
longitudinal gap are explicit inputs. Codimension bounds and constancy are
derived here, not supplied as hypotheses. When every sufficiently large row
selection spans the longitudinal space, the final theorem forces every
longitudinal coordinate to be constant on the prime component.
-/

namespace GeneralizedLogarithms.SmallRankExclusion

noncomputable section

open scoped BigOperators
open MvPolynomial
open LogIrrationalityMeasure.LogExponent
open LogIrrationalityMeasure.LogExponent.NormalBasisRigidity
open PolynomialPrimeAdapter

variable {C E : Type*} [Field C] [CharZero C] [IsAlgClosed C]
  [Field E] [Algebra C E] [Algebra.EssFiniteType C E] {k m : ℕ}

/-- The small-rank branch is impossible under the longitudinal parameter gap.
The selected set and all its constancy conclusions come from weighted rigidity. -/
theorem exists_large_constant_transverse_set
    [frameOrder : LinearOrder (Fin k ⊕ Fin m)]
    (φ : MvPolynomial (Fin k ⊕ Fin m) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin k ⊕ Fin m) C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥)
    (a : Fin m → Fin k → ℤ) (hrows : ∀ i, a i ≠ 0)
    (hy : ∀ r : Fin k, φ (X (Sum.inl r)) ≠ 0)
    (t : (Fin k ⊕ Fin m) → ℝ) (ht : ∀ i, 0 < t i)
    (θ w₀ v₀ : ℝ) (hv₀ : 0 < v₀) (bound : ℕ → ℝ)
    (hcomparison : ∀ A B,
      IsNormalBasis (K := E) (coordinateNormalFamily φ Q) A →
      IsNormalBasis (K := E) (frameNormalFamily φ Q a hy) B →
      (∏ i ∈ A, blockWeight (Finset.univ.image Sum.inr) (fun j => θ * t j) w₀ i) ≤
        bound A.card * ∏ i ∈ B, blockWeight (Finset.univ.image Sum.inr) t v₀ i)
    (hseparated : ∀ A B : Finset (Fin k ⊕ Fin m), A.card = B.card →
      ∀ i : Fin m, Sum.inr i ∈ A → Sum.inr i ∉ B →
      (∀ j : Fin m, frameOrder.lt (Sum.inr i) (Sum.inr j) →
        (Sum.inr j ∈ A ↔ Sum.inr j ∈ B)) →
      bound A.card * (∏ j ∈ B, blockWeight (Finset.univ.image Sum.inr) t v₀ j) <
        ∏ j ∈ A, blockWeight (Finset.univ.image Sum.inr) (fun l => θ * t l) w₀ j)
    (hgap : ∀ r c : ℕ, r < k → 1 ≤ c - r → c - r ≤ k → c ≤ 2 * k - 1 →
      bound c < θ ^ r * (w₀ / v₀) ^ (c - r)) :
    ∃ J : Finset (Fin m), k ≤ J.card ∧
      IsGreedyBasis (K := E) (coordinateNormalFamily φ Q)
        (Finset.univ.image Sum.inr) (J.image Sum.inr) ∧
      (∀ B, IsNormalBasis (K := E) (frameNormalFamily φ Q a hy) B →
        B ∩ Finset.univ.image Sum.inr = J.image Sum.inr) ∧
      ∀ i ∈ J,
        (∃ c : C, algebraMap C E c = ∏ r, φ (X (Sum.inl r)) ^ a i r) ∧
        ∃ b : C, X (Sum.inr i) - MvPolynomial.C b ∈ Q := by
  obtain ⟨I, hI, hfixed, hconstant⟩ := weighted_polynomial_constancy φ Q hker a hy
    (blockWeight (Finset.univ.image Sum.inr) (fun j => θ * t j) w₀)
    (blockWeight (Finset.univ.image Sum.inr) t v₀) bound hcomparison hseparated
  let J : Finset (Fin m) := Finset.univ.filter (fun i => Sum.inr i ∈ I)
  have hJI : J.image (Sum.inr : Fin m → Fin k ⊕ Fin m) = I := by
    ext j
    constructor
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact (Finset.mem_filter.mp hi).2
    · intro hj
      have hjX := hI.1 hj
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hjX
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hj⟩, rfl⟩
  have hJ : IsGreedyBasis (K := E) (coordinateNormalFamily φ Q)
      (Finset.univ.image Sum.inr) (J.image Sum.inr) := by
    simpa only [hJI] using hI
  have hIcard : I.card = J.card := by
    rw [← hJI, Finset.card_image_of_injective _ Sum.inr_injective]
  have hmandatory : ∀ i ∈ J, ∀ B,
      IsNormalBasis (K := E) (frameNormalFamily φ Q a hy) B → Sum.inr i ∈ B := by
    intro i hi B hB
    have hiI : Sum.inr i ∈ I := (Finset.mem_filter.mp hi).2
    have hiBX : Sum.inr i ∈ B ∩ Finset.univ.image Sum.inr := by
      rw [hfixed B hB]
      exact hiI
    exact (Finset.mem_inter.mp hiBX).1
  have hlarge : k ≤ J.card := by
    by_contra hsmall
    have hrk : J.card < k := Nat.lt_of_not_ge hsmall
    obtain ⟨hdpos, hdle, hcle⟩ := PolynomialCodimension.small_rank_codimension_range
      φ Q hker hQ a hy J hJ (fun i _ => hrows i) hmandatory hrk
    obtain ⟨A, hA, hAX⟩ := exists_normalBasis_with_intersection
      (coordinateNormalFamily φ Q) (polynomialNormal_span φ Q (Pi.basisFun E _))
      (Finset.univ.image Sum.inr) I hI.1 hI.2.1 hI.span_eq
    have hspan : Submodule.span E (Set.range (frameNormalFamily φ Q a hy)) = ⊤ :=
      polynomialNormal_span φ Q
        (MultivariateFrame.frameBasis (fun i r => (a i r : E))
          (fun r => φ (X (Sum.inl r))) hy)
    obtain ⟨B, _, hB⟩ := exists_normalBasis_subset (frameNormalFamily φ Q a hy) Set.univ
      (by simpa only [Set.image_univ] using hspan)
    have hcard : A.card = B.card := hA.card_eq.trans hB.card_eq.symm
    have hstrict : bound A.card < θ ^ I.card * (w₀ / v₀) ^ (A.card - I.card) := by
      simpa only [hA.card_eq, hIcard] using
        hgap J.card (Module.finrank E (PolynomialNormal φ Q)) hrk hdpos hdle hcle
    exact not_product_comparison_of_longitudinal_gap A B (Finset.univ.image Sum.inr) I
      t θ w₀ v₀ bound hAX (hfixed B hB) hcard (fun i _ => ht i) hv₀ hstrict
      (hcomparison A B hA hB)
  refine ⟨J, hlarge, hJ, ?_, ?_⟩
  · intro B hB
    simpa only [hJI] using hfixed B hB
  · intro i hi
    exact hconstant i (Finset.mem_filter.mp hi).2

/-- Complete the function-field rigidity argument: the large selected set has
spanning exponent rows, so its constant monomials force all longitudinal
coordinates to be constant. The row-spanning selection property is explicit. -/
theorem longitudinal_equations_of_weighted_comparison
    [frameOrder : LinearOrder (Fin k ⊕ Fin m)]
    (φ : MvPolynomial (Fin k ⊕ Fin m) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin k ⊕ Fin m) C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥)
    (a : Fin m → Fin k → ℤ) (hrows : ∀ i, a i ≠ 0)
    (hy : ∀ r : Fin k, φ (X (Sum.inl r)) ≠ 0)
    (t : (Fin k ⊕ Fin m) → ℝ) (ht : ∀ i, 0 < t i)
    (θ w₀ v₀ : ℝ) (hv₀ : 0 < v₀) (bound : ℕ → ℝ)
    (hcomparison : ∀ A B,
      IsNormalBasis (K := E) (coordinateNormalFamily φ Q) A →
      IsNormalBasis (K := E) (frameNormalFamily φ Q a hy) B →
      (∏ i ∈ A, blockWeight (Finset.univ.image Sum.inr) (fun j => θ * t j) w₀ i) ≤
        bound A.card * ∏ i ∈ B, blockWeight (Finset.univ.image Sum.inr) t v₀ i)
    (hseparated : ∀ A B : Finset (Fin k ⊕ Fin m), A.card = B.card →
      ∀ i : Fin m, Sum.inr i ∈ A → Sum.inr i ∉ B →
      (∀ j : Fin m, frameOrder.lt (Sum.inr i) (Sum.inr j) →
        (Sum.inr j ∈ A ↔ Sum.inr j ∈ B)) →
      bound A.card * (∏ j ∈ B, blockWeight (Finset.univ.image Sum.inr) t v₀ j) <
        ∏ j ∈ A, blockWeight (Finset.univ.image Sum.inr) (fun l => θ * t l) w₀ j)
    (hgap : ∀ r c : ℕ, r < k → 1 ≤ c - r → c - r ≤ k → c ≤ 2 * k - 1 →
      bound c < θ ^ r * (w₀ / v₀) ^ (c - r))
    (hspan : ∀ J : Finset (Fin m), k ≤ J.card →
      Submodule.span E (Set.range
        (fun i : Fin J.card => fun r => (a (J.equivFin.symm i) r : E))) = ⊤) :
    ∀ r : Fin k, ∃ c : C, X (Sum.inl r) - MvPolynomial.C c ∈ Q := by
  obtain ⟨J, hlarge, _, _, hconstant⟩ := exists_large_constant_transverse_set
    φ Q hker hQ a hrows hy t ht θ w₀ v₀ hv₀ bound hcomparison hseparated hgap
  have hmonomial : ∀ i : Fin J.card, ∃ c : C, algebraMap C E c =
      ∏ r, φ (X (Sum.inl r)) ^ a (J.equivFin.symm i) r := by
    intro i
    exact (hconstant (J.equivFin.symm i) (J.equivFin.symm i).property).1
  have hY := GenericConstancy.longitudinal_constants_of_spanning_rows
    (fun i : Fin J.card => fun r => a (J.equivFin.symm i) r)
    (fun r => φ (X (Sum.inl r))) hy (hspan J hlarge) hmonomial
  intro r
  obtain ⟨c, hc⟩ := hY r
  exact ⟨c, coordinate_sub_constant_mem φ Q hker (Sum.inl r) c hc⟩

end
end GeneralizedLogarithms.SmallRankExclusion

/-- info: 'GeneralizedLogarithms.SmallRankExclusion.exists_large_constant_transverse_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.SmallRankExclusion.exists_large_constant_transverse_set

/-- info: 'GeneralizedLogarithms.SmallRankExclusion.longitudinal_equations_of_weighted_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.SmallRankExclusion.longitudinal_equations_of_weighted_comparison
