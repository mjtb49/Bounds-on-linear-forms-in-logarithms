import GeneralizedLogarithms.MultivariateFormalJet

/-!
# Rational coefficients of multilogarithmic jets

The full formal logarithmic substitution is defined over the rationals. Mapping
its coefficients to the complex numbers gives the actual jet used by the
geometric interpolation theorem. No truncation or rationality hypothesis on
individual matrix entries is needed.
-/

namespace GeneralizedLogarithms.MultivariateRationalJet

noncomputable section
open scoped BigOperators
open MvPowerSeries

variable {k m : ℕ}

def formalLog (r : Fin k) : MvPowerSeries (Fin k ⊕ Fin m) ℚ :=
  (PowerSeries.log ℚ).toMvPowerSeries (Sum.inl r)

def coordinates (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℚ) :
    (Fin k ⊕ Fin m) → MvPowerSeries (Fin k ⊕ Fin m) ℚ :=
  Sum.elim (fun r => C (c (Sum.inl r)) * (1 + X (Sum.inl r)))
    (fun i => C (c (Sum.inr i)) + X (Sum.inr i) +
      ∑ r, C (a i r : ℚ) * formalLog r)

def formalJet (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℚ) :
    MvPolynomial (Fin k ⊕ Fin m) ℚ →ₐ[ℚ] MvPowerSeries (Fin k ⊕ Fin m) ℚ :=
  MvPolynomial.aeval (coordinates a c)

theorem map_lift {σ : Type*} (i : σ) (f : PowerSeries ℚ) :
    MvPowerSeries.map (algebraMap ℚ ℂ) (f.toMvPowerSeries i) =
      (PowerSeries.map (algebraMap ℚ ℂ) f).toMvPowerSeries i := by
  classical
  ext d
  simp only [MvPowerSeries.coeff_map, PowerSeries.toMvPowerSeries_eq_subst,
    PowerSeries.coeff_subst_single, PowerSeries.coeff_map]
  split_ifs <;> simp

@[simp] theorem map_formalLog (r : Fin k) :
    MvPowerSeries.map (algebraMap ℚ ℂ) (formalLog (m := m) r) =
      MultivariateFormalJet.formalLog r := by
  rw [formalLog, map_lift, PowerSeries.map_log]
  rfl

theorem map_coordinates (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℚ)
    (j : Fin k ⊕ Fin m) :
    MvPowerSeries.map (algebraMap ℚ ℂ) (coordinates a c j) =
      MultivariateFormalJet.formalJet a (fun j => (c j : ℂ)) (MvPolynomial.X j) := by
  cases j <;> simp [coordinates]

/-- Coefficient extension commutes with the entire multilogarithmic jet. -/
theorem map_formalJet (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℚ)
    (P : MvPolynomial (Fin k ⊕ Fin m) ℚ) :
    MvPowerSeries.map (algebraMap ℚ ℂ) (formalJet a c P) =
      MultivariateFormalJet.formalJet a (fun j => (c j : ℂ))
        (MvPolynomial.map (algebraMap ℚ ℂ) P) := by
  induction P using MvPolynomial.induction_on with
  | C q => simp [formalJet, MvPowerSeries.algebraMap_apply]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P j hP =>
    simp only [map_mul, hP, MvPolynomial.map_X]
    congr 1
    simpa only [formalJet, MvPolynomial.aeval_X] using map_coordinates a c j

theorem cast_coeff_formalJet (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℚ)
    (P : MvPolynomial (Fin k ⊕ Fin m) ℚ) (d : (Fin k ⊕ Fin m) →₀ ℕ) :
    ((coeff d (formalJet a c P) : ℚ) : ℂ) =
      coeff d (MultivariateFormalJet.formalJet a (fun j => (c j : ℂ))
        (MvPolynomial.map (algebraMap ℚ ℂ) P)) := by
  rw [← map_formalJet, MvPowerSeries.coeff_map]
  rfl

/-- The rational centers used in the approximation argument. -/
def approximationCenter (α : Fin k → ℚ) (p : Fin m → ℤ) (j : ℕ) :
    Fin k ⊕ Fin m → ℚ :=
  Sum.elim (fun r => α r ^ j) (fun i => -(j : ℚ) * p i)

@[simp] theorem approximationCenter_Y (α : Fin k → ℚ) (p : Fin m → ℤ)
    (j : ℕ) (r : Fin k) : approximationCenter α p j (Sum.inl r) = α r ^ j := rfl

@[simp] theorem approximationCenter_X (α : Fin k → ℚ) (p : Fin m → ℤ)
    (j : ℕ) (i : Fin m) : approximationCenter α p j (Sum.inr i) = -(j : ℚ) * p i := rfl

end
end GeneralizedLogarithms.MultivariateRationalJet

/-- info: 'GeneralizedLogarithms.MultivariateRationalJet.map_formalJet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateRationalJet.map_formalJet

/-- info: 'GeneralizedLogarithms.MultivariateRationalJet.cast_coeff_formalJet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateRationalJet.cast_coeff_formalJet
