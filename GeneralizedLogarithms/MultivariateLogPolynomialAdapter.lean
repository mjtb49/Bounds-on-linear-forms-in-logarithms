import GeneralizedLogarithms.MultivariateCompactJetPolynomial
import GeneralizedLogarithms.MultivariateLogarithmicContactIdeal
import LogIrrationalityMeasure.Jets.JetGeometry

/-!
# Polynomial ideals and truncated multilogarithmic jets

Specializing the triangular coordinate construction to sums of truncated
logarithms gives the same ideal after evaluation in a local algebra as the
one whose colength is calculated by `MultivariateLogarithmicContactIdeal`.
The polynomial jet sends its generators to coordinate powers.
-/

namespace GeneralizedLogarithms.MultivariateLogPolynomialAdapter

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open MultivariateCompactJetPolynomial

variable {k m : ℕ}

def logPolynomials (a : Fin m → Fin k → ℤ) (T : Fin m → Fin k → ℕ) :
    Fin m → MvPolynomial (Fin k) ℂ := fun i =>
  ∑ r, MvPolynomial.C (a i r : ℂ) *
    Polynomial.aeval (MvPolynomial.X r) (PowerSeries.trunc (T i r) (PowerSeries.log ℂ))

theorem aeval_logPolynomials {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : Fin m → Fin k → ℤ) (T : Fin m → Fin k → ℕ) (y : Fin k → A) (i : Fin m) :
    MvPolynomial.aeval y (logPolynomials a T i) =
      ∑ r, algebraMap ℂ A (a i r : ℂ) *
        Polynomial.aeval (y r) (PowerSeries.trunc (T i r) (PowerSeries.log ℂ)) := by
  simp only [logPolynomials, map_sum, map_mul, MvPolynomial.aeval_C,
    ← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]

@[simp] theorem logPolynomials_aeval_zero
    (a : Fin m → Fin k → ℤ) (T : Fin m → Fin k → ℕ) (i : Fin m) :
    MvPolynomial.aeval (0 : Fin k → ℂ) (logPolynomials a T i) = 0 := by
  rw [aeval_logPolynomials]
  apply Finset.sum_eq_zero
  intro r _
  have hz : (PowerSeries.trunc (T i r) (PowerSeries.log ℂ)).eval 0 = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    simp [PowerSeries.coeff_trunc, PowerSeries.coeff_log]
  simp [Polynomial.coe_aeval_eq_eval, hz]

def logPowerIdeal (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℂ)
    (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ) :
    Ideal (MvPolynomial (Fin k ⊕ Fin m) ℂ) := powerIdeal c (logPolynomials a T) e

theorem radical_logPowerIdeal (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℂ)
    (hc : ∀ r, c (Sum.inl r) ≠ 0) (T : Fin m → Fin k → ℕ)
    (e : Fin k ⊕ Fin m → ℕ) (he : ∀ j, 0 < e j) :
    (logPowerIdeal a c T e).radical = WeightedBezout.pointIdeal c :=
  radical_powerIdeal c hc (logPolynomials a T) (logPolynomials_aeval_zero a T) e he

theorem aeval_coordinates {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℂ) (T : Fin m → Fin k → ℕ)
    (z : Fin k ⊕ Fin m → A) (j : Fin k ⊕ Fin m) :
    MvPolynomial.aeval z (coordinates c (logPolynomials a T) j) =
      MultivariateLogarithmicContactIdeal.truncatedCoordinates a
        (fun r => c (Sum.inl r)) (fun i => c (Sum.inr i))
        (fun r => z (Sum.inl r)) (fun i => z (Sum.inr i)) T j := by
  have hY (r : Fin k) : MvPolynomial.aeval z (centeredY c r) =
      MultivariateLogarithmicContactIdeal.centeredY (c (Sum.inl r)) (z (Sum.inl r)) := by
    simp [centeredY, MultivariateLogarithmicContactIdeal.centeredY]
  cases j with
  | inl r => exact hY r
  | inr i =>
    simp only [coordinates, Sum.elim_inr, map_sub, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C]
    rw [MvPolynomial.comp_aeval_apply, aeval_logPolynomials]
    simp only [hY, MultivariateLogarithmicContactIdeal.truncatedCoordinates, Sum.elim_inr]

theorem map_logPowerIdeal_aeval {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℂ) (T : Fin m → Fin k → ℕ)
    (e : Fin k ⊕ Fin m → ℕ) (z : Fin k ⊕ Fin m → A) :
    (logPowerIdeal a c T e).map (MvPolynomial.aeval z).toRingHom =
      MultivariateLogarithmicContactIdeal.logarithmicIdeal a
        (fun r => c (Sum.inl r)) (fun i => c (Sum.inr i))
        (fun r => z (Sum.inl r)) (fun i => z (Sum.inr i)) T e := by
  rw [logPowerIdeal, powerIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  change MvPolynomial.aeval z (coordinates c (logPolynomials a T) j ^ e j) = _
  rw [map_pow, aeval_coordinates]

def truncatedFormalJet (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℂ)
    (T : Fin m → Fin k → ℕ) :
    MvPolynomial (Fin k ⊕ Fin m) ℂ →ₐ[ℂ] MvPowerSeries (Fin k ⊕ Fin m) ℂ :=
  (MvPolynomial.coeToMvPowerSeries.algHom ℂ).comp (triangularMap c (logPolynomials a T))

theorem truncatedFormalJet_coordinates (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℂ)
    (hc : ∀ r, c (Sum.inl r) ≠ 0) (T : Fin m → Fin k → ℕ) (j : Fin k ⊕ Fin m) :
    truncatedFormalJet a c T (coordinates c (logPolynomials a T) j) = MvPowerSeries.X j := by
  have h := AlgHom.congr_fun (triangularMap_comp_inverse c hc (logPolynomials a T))
    (MvPolynomial.X j)
  have h' : triangularMap c (logPolynomials a T) (coordinates c (logPolynomials a T) j) =
      MvPolynomial.X j := by simpa only [AlgHom.comp_apply, inverseTriangularMap_X,
        AlgHom.id_apply] using h
  simp [truncatedFormalJet, h']

theorem map_logPowerIdeal_truncatedFormalJet
    (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℂ)
    (hc : ∀ r, c (Sum.inl r) ≠ 0) (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ) :
    (logPowerIdeal a c T e).map (truncatedFormalJet a c T).toRingHom =
      JetGeometry.coordinatePowerIdeal (R := ℂ) e := by
  rw [logPowerIdeal, powerIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  change truncatedFormalJet a c T (coordinates c (logPolynomials a T) j ^ e j) =
    MvPowerSeries.X j ^ e j
  rw [map_pow, truncatedFormalJet_coordinates a c hc]

theorem truncatedFormalJet_mem_weighted_of_mem_pow
    (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℂ)
    (hc : ∀ r, c (Sum.inl r) ≠ 0) (T : Fin m → Fin k → ℕ)
    (e : Fin k ⊕ Fin m → ℕ) (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 ≤ v j)
    (R : ℚ) (he : ∀ j, R ≤ (e j : ℚ) * v j) (n : ℕ)
    (P : MvPolynomial (Fin k ⊕ Fin m) ℂ) (hP : P ∈ logPowerIdeal a c T e ^ n) :
    truncatedFormalJet a c T P ∈ JetGeometry.rationalWeightedIdeal v hv (n * R) := by
  apply JetGeometry.coordinatePowerIdeal_pow_le_rational v hv e R he n
  rw [← map_logPowerIdeal_truncatedFormalJet a c hc T e, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hP

end
end GeneralizedLogarithms.MultivariateLogPolynomialAdapter

/-- info: 'GeneralizedLogarithms.MultivariateLogPolynomialAdapter.radical_logPowerIdeal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateLogPolynomialAdapter.radical_logPowerIdeal

/-- info: 'GeneralizedLogarithms.MultivariateLogPolynomialAdapter.map_logPowerIdeal_aeval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateLogPolynomialAdapter.map_logPowerIdeal_aeval

/-- info: 'GeneralizedLogarithms.MultivariateLogPolynomialAdapter.truncatedFormalJet_mem_weighted_of_mem_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateLogPolynomialAdapter.truncatedFormalJet_mem_weighted_of_mem_pow
