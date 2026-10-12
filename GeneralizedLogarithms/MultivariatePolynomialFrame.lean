import GeneralizedLogarithms.MultivariateFrame
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie

/-!
# Polynomial operators for several logarithmic directions

The polynomial coordinates are indexed by `Fin k ⊕ Fin m`.  The longitudinal
operator indexed by `r` is `Y_r ∂Y_r + ∑ i, a_i_r ∂X_i`; transverse operators
are the ordinary partial derivatives.  Evaluation in a field identifies these
operators with the previously constructed multivariate frame.

The coefficient matrix can be over any commutative ring. Integer exponents
are obtained by casting their entries into that ring.
-/

namespace GeneralizedLogarithms
namespace MultivariatePolynomialFrame

noncomputable section

open scoped BigOperators

abbrev Polynomial (C : Type*) [CommRing C] (k m : ℕ) :=
  MvPolynomial (Fin k ⊕ Fin m) C

variable {C : Type*} [CommRing C] {k m : ℕ}

/-- The polynomial logarithmic direction associated with a longitudinal variable. -/
def logarithmicDerivation (a : Fin m → Fin k → C) (r : Fin k) :
    Derivation C (Polynomial C k m) (Polynomial C k m) :=
  (MvPolynomial.X (Sum.inl r) : Polynomial C k m) • MvPolynomial.pderiv (Sum.inl r) +
    ∑ i, (MvPolynomial.C (a i r) : Polynomial C k m) • MvPolynomial.pderiv (Sum.inr i)

/-- The complete polynomial frame, including ordinary transverse partials. -/
def polynomialFrame (a : Fin m → Fin k → C) :
    (Fin k ⊕ Fin m) → Derivation C (Polynomial C k m) (Polynomial C k m) :=
  Sum.elim (logarithmicDerivation a) (fun i => MvPolynomial.pderiv (Sum.inr i))

theorem derivation_finset_sum_apply {ι : Type*} (s : Finset ι)
    (d : ι → Derivation C (Polynomial C k m) (Polynomial C k m))
    (p : Polynomial C k m) : (∑ i ∈ s, d i) p = ∑ i ∈ s, d i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Derivation.zero_apply]
  | @insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his, Derivation.add_apply, ih]

@[simp] theorem logarithmicDerivation_apply (a : Fin m → Fin k → C)
    (r : Fin k) (p : Polynomial C k m) :
    logarithmicDerivation a r p =
      MvPolynomial.X (Sum.inl r) * MvPolynomial.pderiv (Sum.inl r) p +
        ∑ i, MvPolynomial.C (a i r) * MvPolynomial.pderiv (Sum.inr i) p := by
  simp only [logarithmicDerivation, Derivation.add_apply, Derivation.smul_apply,
    derivation_finset_sum_apply, smul_eq_mul]

@[simp] theorem polynomialFrame_inl (a : Fin m → Fin k → C) (r : Fin k) :
    polynomialFrame a (Sum.inl r) = logarithmicDerivation a r := rfl

@[simp] theorem polynomialFrame_inr (a : Fin m → Fin k → C) (i : Fin m) :
    polynomialFrame a (Sum.inr i) = MvPolynomial.pderiv (Sum.inr i) := rfl

@[simp] theorem logarithmicDerivation_X_inl (a : Fin m → Fin k → C) (r s : Fin k) :
    logarithmicDerivation a r (MvPolynomial.X (Sum.inl s)) =
      if s = r then MvPolynomial.X (Sum.inl r) else 0 := by
  by_cases h : s = r
  · subst s
    simp [logarithmicDerivation_apply]
  · simp [logarithmicDerivation_apply, h]

@[simp] theorem logarithmicDerivation_X_inr (a : Fin m → Fin k → C)
    (r : Fin k) (i : Fin m) :
    logarithmicDerivation a r (MvPolynomial.X (Sum.inr i)) = MvPolynomial.C (a i r) := by
  simp [logarithmicDerivation_apply, Pi.single_apply]

@[simp] theorem polynomialFrame_C (a : Fin m → Fin k → C)
    (j : Fin k ⊕ Fin m) (c : C) : polynomialFrame a j (MvPolynomial.C c) = 0 :=
  MvPolynomial.derivation_C _ _

theorem polynomialFrame_mul (a : Fin m → Fin k → C)
    (j : Fin k ⊕ Fin m) (p q : Polynomial C k m) :
    polynomialFrame a j (p * q) =
      p * polynomialFrame a j q + q * polynomialFrame a j p := by
  simpa only [smul_eq_mul] using (polynomialFrame a j).leibniz p q

/-- All longitudinal and transverse polynomial frame operators commute. -/
theorem polynomialFrame_commute (a : Fin m → Fin k → C)
    (i j : Fin k ⊕ Fin m) (p : Polynomial C k m) :
    polynomialFrame a i (polynomialFrame a j p) =
      polynomialFrame a j (polynomialFrame a i p) := by
  have h : ⁅polynomialFrame a i, polynomialFrame a j⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro v
    simp only [Derivation.commutator_apply, Derivation.zero_apply]
    apply sub_eq_zero.mpr
    cases i with
    | inl r =>
        cases j with
        | inl s =>
            cases v with
            | inl t =>
                by_cases htr : t = r <;> by_cases hts : t = s
                all_goals simp_all
            | inr l =>
                simp only [polynomialFrame_inl, logarithmicDerivation_X_inr,
                  MvPolynomial.derivation_C]
        | inr l =>
            cases v <;> simp [apply_ite, Pi.single_apply]
    | inr l =>
        cases j with
        | inl r =>
            cases v <;> simp [apply_ite, Pi.single_apply]
        | inr n =>
            cases v <;> simp [Pi.single_apply, apply_ite]
  have hp := Derivation.congr_fun h p
  simpa only [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] using hp

/-- Residue evaluation gives the scalar product with the multivariate frame
column. No descent of the polynomial derivation to the residue field is assumed. -/
theorem residue_polynomialFrame_eq_frameBasis_dot
    {E : Type*} [Field E] (a : Fin m → Fin k → C)
    (φ : Polynomial C k m →+* E)
    (hy : ∀ r, φ (MvPolynomial.X (Sum.inl r)) ≠ 0)
    (j : Fin k ⊕ Fin m) (p : Polynomial C k m) :
    φ (polynomialFrame a j p) =
      ∑ v, MultivariateFrame.frameBasis
        (fun i r => φ (MvPolynomial.C (a i r)))
        (fun r => φ (MvPolynomial.X (Sum.inl r))) hy j v *
        φ (MvPolynomial.pderiv v p) := by
  cases j with
  | inl r =>
      rw [polynomialFrame_inl, logarithmicDerivation_apply, map_add, map_mul,
        map_sum, Fintype.sum_sum_type]
      simp [MultivariateFrame.frameBasis_inl_inl,
        MultivariateFrame.frameBasis_inl_inr, ite_mul, map_mul]
  | inr i =>
      rw [polynomialFrame_inr, MultivariateFrame.frameBasis_inr]
      simp [Pi.basisFun_apply, Pi.single_apply]

/-- In particular, the evaluated action on coordinate variables is exactly
the corresponding frame vector. -/
theorem residue_polynomialFrame_X_eq_frameBasis
    {E : Type*} [Field E] (a : Fin m → Fin k → C)
    (φ : Polynomial C k m →+* E)
    (hy : ∀ r, φ (MvPolynomial.X (Sum.inl r)) ≠ 0)
    (j v : Fin k ⊕ Fin m) :
    φ (polynomialFrame a j (MvPolynomial.X v)) =
      MultivariateFrame.frameBasis (fun i r => φ (MvPolynomial.C (a i r)))
        (fun r => φ (MvPolynomial.X (Sum.inl r))) hy j v := by
  rw [residue_polynomialFrame_eq_frameBasis_dot a φ hy]
  simp [Pi.single_apply]

end
end MultivariatePolynomialFrame
end GeneralizedLogarithms

/-- info: 'GeneralizedLogarithms.MultivariatePolynomialFrame.polynomialFrame_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariatePolynomialFrame.polynomialFrame_commute

/-- info: 'GeneralizedLogarithms.MultivariatePolynomialFrame.residue_polynomialFrame_eq_frameBasis_dot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariatePolynomialFrame.residue_polynomialFrame_eq_frameBasis_dot

/-- info: 'GeneralizedLogarithms.MultivariatePolynomialFrame.residue_polynomialFrame_X_eq_frameBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariatePolynomialFrame.residue_polynomialFrame_X_eq_frameBasis
