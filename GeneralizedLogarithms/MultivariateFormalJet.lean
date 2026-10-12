import GeneralizedLogarithms.MultivariateJetDerivatives
import GeneralizedLogarithms.MultivariateMultiplicity
import LogIrrationalityMeasure.Jets.FormalLogJet
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Formal jets for several logarithmic directions

The substitution is `Y_r = c_r (1 + T_r)` and
`X_i = c_i + U_i + ∑ r, a_i_r log(1 + T_r)`.
It intertwines the actual polynomial frame with the formal jet frame, hence
preserves the proved derivative-word budget for rational weighted vanishing.
-/

namespace GeneralizedLogarithms.MultivariateFormalJet

noncomputable section

open scoped BigOperators
open MvPowerSeries
open LogIrrationalityMeasure.LogExponent
open MultivariatePolynomialFrame MultivariateJetDerivatives

section LiftDerivatives

variable {R σ : Type*} [CommRing R]

/-- Differentiation in the variable used for a univariate series lift. -/
theorem pderiv_toMvPowerSeries (i : σ) (f : PowerSeries R) :
    pderiv i (f.toMvPowerSeries i) = (PowerSeries.derivative f).toMvPowerSeries i := by
  classical
  ext d
  have hd : d + Finsupp.single i 1 =
      Finsupp.single i ((d + Finsupp.single i 1 : σ →₀ ℕ) i) ↔
        d = Finsupp.single i (d i) := by
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_add,
      add_left_inj]
  rw [coeff_pderiv]
  simp only [PowerSeries.toMvPowerSeries_eq_subst, PowerSeries.coeff_subst_single]
  by_cases h0 : d = Finsupp.single i (d i)
  · rw [ite_eq_left (hd.mpr h0), ite_eq_left h0]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, PowerSeries.coeff_derivative]
  · rw [ite_eq_right (mt hd.mp h0), ite_eq_right h0, zero_mul]

/-- A univariate series lift is independent of all other variables. -/
theorem pderiv_toMvPowerSeries_of_ne (i j : σ) (h : i ≠ j) (f : PowerSeries R) :
    pderiv j (f.toMvPowerSeries i) = 0 := by
  classical
  ext d
  have hd : d + Finsupp.single j 1 ≠
      Finsupp.single i ((d + Finsupp.single j 1 : σ →₀ ℕ) i) := by
    intro he
    have hj := DFunLike.congr_fun he j
    simp [Finsupp.single_eq_of_ne (Ne.symm h)] at hj
  simp only [coeff_pderiv, PowerSeries.toMvPowerSeries_eq_subst,
    PowerSeries.coeff_subst_single, ite_eq_right hd, zero_mul, coeff_zero]

end LiftDerivatives

variable {k m : ℕ}

/-- The formal series `log(1 + T_r)` in the `r`-th longitudinal variable. -/
def formalLog (r : Fin k) : MvPowerSeries (Fin k ⊕ Fin m) ℂ :=
  (PowerSeries.log ℂ).toMvPowerSeries (Sum.inl r)

@[simp] theorem pderiv_inr_formalLog (i : Fin m) (r : Fin k) :
    pderiv (Sum.inr i) (formalLog (m := m) r) = 0 :=
  pderiv_toMvPowerSeries_of_ne _ _ Sum.inl_ne_inr _

theorem pderiv_inl_formalLog_of_ne (r s : Fin k) (h : s ≠ r) :
    pderiv (Sum.inl r) (formalLog (m := m) s) = 0 :=
  pderiv_toMvPowerSeries_of_ne _ _ (by simpa using h) _

theorem one_add_X_mul_pderiv_formalLog (r : Fin k) :
    (1 + X (Sum.inl r)) * pderiv (Sum.inl r) (formalLog (m := m) r) = 1 := by
  have h := congrArg (PowerSeries.toMvPowerSeries (Sum.inl r : Fin k ⊕ Fin m))
    (PowerSeries.derivative_log_mul_one_add_X (A := ℂ))
  rw [map_mul, map_add, map_one, PowerSeries.toMvPowerSeries_X] at h
  rw [formalLog, pderiv_toMvPowerSeries, mul_comm]
  exact h

@[simp] theorem jetFrame_C (j : Fin k ⊕ Fin m) (c : ℂ) :
    jetFrame j (C c) = 0 := by
  cases j <;> simp

@[simp] theorem jetFrame_inl_formalLog (r s : Fin k) :
    jetFrame (Sum.inl r) (formalLog (m := m) s) = if s = r then 1 else 0 := by
  by_cases h : s = r
  · subst s
    simp only [jetFrame_inl, one_add_X_mul_pderiv_formalLog, ite_true]
  · simp only [jetFrame_inl, pderiv_inl_formalLog_of_ne r s h, mul_zero, ite_eq_right h]

@[simp] theorem jetFrame_inr_formalLog (i : Fin m) (r : Fin k) :
    jetFrame (Sum.inr i) (formalLog (m := m) r) = 0 := by
  simp only [jetFrame_inr, pderiv_inr_formalLog]

theorem jetFrame_inl_logSum (a : Fin m → Fin k → ℤ) (i : Fin m) (r : Fin k) :
    jetFrame (Sum.inl r) (∑ s, C (a i s : ℂ) * formalLog (m := m) s) =
      C (a i r : ℂ) := by
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, jetFrame_C,
    jetFrame_inl_formalLog, mul_zero, add_zero]
  simp [mul_ite]

theorem jetFrame_inr_logSum (a : Fin m → Fin k → ℤ) (i j : Fin m) :
    jetFrame (Sum.inr j) (∑ s, C (a i s : ℂ) * formalLog (m := m) s) = 0 := by
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, jetFrame_C,
    jetFrame_inr_formalLog, mul_zero, add_zero, Finset.sum_const_zero]

/-- Formal logarithmic coordinates at an arbitrary center. -/
def formalJet (a : Fin m → Fin k → ℤ) (c : (Fin k ⊕ Fin m) → ℂ) :
    Polynomial ℂ k m →ₐ[ℂ] MvPowerSeries (Fin k ⊕ Fin m) ℂ :=
  MvPolynomial.aeval (Sum.elim
    (fun r => C (c (Sum.inl r)) * (1 + X (Sum.inl r)))
    (fun i => C (c (Sum.inr i)) + X (Sum.inr i) +
      ∑ r, C (a i r : ℂ) * formalLog r))

@[simp] theorem formalJet_C (a : Fin m → Fin k → ℤ)
    (c : (Fin k ⊕ Fin m) → ℂ) (z : ℂ) :
    formalJet a c (MvPolynomial.C z) = C z := by
  simp [formalJet, MvPowerSeries.algebraMap_apply]

@[simp] theorem formalJet_Y (a : Fin m → Fin k → ℤ)
    (c : (Fin k ⊕ Fin m) → ℂ) (r : Fin k) :
    formalJet a c (MvPolynomial.X (Sum.inl r)) =
      C (c (Sum.inl r)) * (1 + X (Sum.inl r)) := by
  simp [formalJet]

@[simp] theorem formalJet_X (a : Fin m → Fin k → ℤ)
    (c : (Fin k ⊕ Fin m) → ℂ) (i : Fin m) :
    formalJet a c (MvPolynomial.X (Sum.inr i)) =
      C (c (Sum.inr i)) + X (Sum.inr i) +
        ∑ r, C (a i r : ℂ) * formalLog r := by
  simp [formalJet]

/-- Intertwining on polynomial generators, including every cross term. -/
theorem formalJet_frame_X (a : Fin m → Fin k → ℤ)
    (c : (Fin k ⊕ Fin m) → ℂ) (j v : Fin k ⊕ Fin m) :
    formalJet a c (polynomialFrame (fun i r => (a i r : ℂ)) j (MvPolynomial.X v)) =
      jetFrame j (formalJet a c (MvPolynomial.X v)) := by
  classical
  cases j with
  | inl r =>
    cases v with
    | inl s =>
      by_cases h : s = r
      · subst s
        simp [mul_comm]
      · simp [h]
    | inr i =>
      simp only [polynomialFrame_inl, logarithmicDerivation_X_inr, formalJet_C,
        formalJet_X, map_add, jetFrame_C, jetFrame_inl_logSum]
      simp [pderiv_X_of_ne]
  | inr i =>
    cases v with
    | inl r => simp [pderiv_X_of_ne]
    | inr j =>
      simp only [polynomialFrame_inr, MvPolynomial.pderiv_X, formalJet_X,
        map_add, jetFrame_inr]
      by_cases h : i = j
      · subst j; simp
      · simp [h, Ne.symm h, MvPowerSeries.pderiv_X, Pi.single_apply]

/-- The polynomial logarithmic frame becomes the jet-coordinate frame. -/
theorem formalJet_polynomialFrame (a : Fin m → Fin k → ℤ)
    (c : (Fin k ⊕ Fin m) → ℂ) (j : Fin k ⊕ Fin m) (p : Polynomial ℂ k m) :
    formalJet a c (polynomialFrame (fun i r => (a i r : ℂ)) j p) =
      jetFrame j (formalJet a c p) :=
  FormalLogJet.derivation_map_of_X (formalJet a c)
    (polynomialFrame (fun i r => (a i r : ℂ)) j) (jetFrame j)
    (formalJet_frame_X a c j) p

/-- Intertwining uses exactly the frame words appearing in the multiplicity proof. -/
theorem formalJet_polynomialFrameWord (a : Fin m → Fin k → ℤ)
    (c : (Fin k ⊕ Fin m) → ℂ) (word : List (Fin k ⊕ Fin m)) (p : Polynomial ℂ k m) :
    formalJet a c (MultivariateMultiplicity.frameWord (fun i r => (a i r : ℂ)) word p) =
      jetFrameWord word (formalJet a c p) := by
  induction word with
  | nil => rfl
  | cons j word ih =>
    change formalJet a c (polynomialFrame (fun i r => (a i r : ℂ)) j
      (MultivariateMultiplicity.frameWord (fun i r => (a i r : ℂ)) word p)) = _
    rw [formalJet_polynomialFrame, ih, jetFrameWord_cons]

/-- A polynomial frame word spends at most the sum of its coordinate weights. -/
theorem formalJet_polynomialFrameWord_vanishing (a : Fin m → Fin k → ℤ)
    (c : (Fin k ⊕ Fin m) → ℂ) (v : (Fin k ⊕ Fin m) → ℚ)
    (hv : ∀ j, 0 ≤ v j) (H : ℚ) (p : Polynomial ℂ k m)
    (hp : formalJet a c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (word : List (Fin k ⊕ Fin m)) :
    formalJet a c (MultivariateMultiplicity.frameWord (fun i r => (a i r : ℂ)) word p) ∈
      JetGeometry.rationalWeightedIdeal v hv (H - (word.map v).sum) := by
  rw [formalJet_polynomialFrameWord]
  exact jetFrameWord_mem_rationalWeightedIdeal v hv H (formalJet a c p) hp word

end
end GeneralizedLogarithms.MultivariateFormalJet

/-- info: 'GeneralizedLogarithms.MultivariateFormalJet.one_add_X_mul_pderiv_formalLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateFormalJet.one_add_X_mul_pderiv_formalLog

/-- info: 'GeneralizedLogarithms.MultivariateFormalJet.formalJet_polynomialFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateFormalJet.formalJet_polynomialFrame

/-- info: 'GeneralizedLogarithms.MultivariateFormalJet.formalJet_polynomialFrameWord_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateFormalJet.formalJet_polynomialFrameWord_vanishing
