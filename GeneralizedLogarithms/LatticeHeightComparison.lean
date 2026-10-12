import GeneralizedLogarithms.LatticeReduction
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Reverse height comparison for independent integer rows

The rational coefficient map has a rational linear left inverse. A finite sum
of absolute matrix entries bounds that inverse uniformly, and hence bounds
the original integer coefficient height by a fixed natural multiple of the
transformed height. No lower bound for logarithmic forms is assumed here.
-/

namespace GeneralizedLogarithms
namespace LatticeHeightComparison

noncomputable section

open scoped BigOperators

variable {r k : ℕ}

/-- The coefficient combination map after extending scalars to the rationals. -/
def rationalCombination (v : Fin r → Fin k → ℤ) :
    (Fin r → ℚ) →ₗ[ℚ] (Fin k → ℚ) :=
  Fintype.linearCombination ℚ (fun s j => (v s j : ℚ))

theorem rationalCombination_intCast (v : Fin r → Fin k → ℤ) (b : Fin r → ℤ) :
    rationalCombination v (fun s => (b s : ℚ)) =
      fun j => (integerCombination v b j : ℚ) := by
  ext j
  simp [rationalCombination, Fintype.linearCombination_apply, integerCombination,
    Finset.sum_apply]

private theorem linearMap_apply_eq_sum
    (g : (Fin k → ℚ) →ₗ[ℚ] (Fin r → ℚ)) (x : Fin k → ℚ) (s : Fin r) :
    g x s = ∑ j, x j * g (Pi.single j 1) s := by
  have hx : (∑ j, x j • Pi.single j (1 : ℚ)) = x := by
    simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using (Pi.basisFun ℚ (Fin k)).sum_repr x
  conv_lhs => rw [← hx]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- A fixed rational linear map uniformly bounds heights whenever it maps
an integer vector to an integer vector. The integer constant term is unchanged. -/
theorem exists_height_bound_of_rational_linearMap
    (g : (Fin k → ℚ) →ₗ[ℚ] (Fin r → ℚ)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℤ) (a : Fin k → ℤ) (b : Fin r → ℤ),
      g (fun j => (a j : ℚ)) = (fun s => (b s : ℚ)) →
      coefficientHeight p b ≤ C * coefficientHeight p a := by
  let M : ℚ := ∑ s, ∑ j, |g (Pi.single j 1) s|
  have hM : 0 ≤ M := by
    exact Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  obtain ⟨C, hC⟩ := exists_nat_ge (1 + M)
  have hC1 : 1 ≤ C := by
    exact_mod_cast (show (1 : ℚ) ≤ C from (by linarith : (1 : ℚ) ≤ 1 + M).trans hC)
  have hrow (s : Fin r) : (∑ j, |g (Pi.single j 1) s|) ≤ (C : ℚ) := by
    have hs : (∑ j, |g (Pi.single j 1) s|) ≤ M :=
      Finset.single_le_sum (f := fun t => ∑ j, |g (Pi.single j 1) t|)
        (fun t _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ s)
    exact hs.trans ((by linarith : M ≤ 1 + M).trans hC)
  refine ⟨C, hC1, ?_⟩
  intro p a b hab
  have ha (j : Fin k) : |(a j : ℚ)| ≤ (coefficientHeight p a : ℚ) := by
    have hh : ((a j).natAbs : ℚ) ≤ (coefficientHeight p a : ℚ) := by
      exact_mod_cast natAbs_coefficient_le_height p a j
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
  have hb (s : Fin r) : |(b s : ℚ)| ≤ (C : ℚ) * (coefficientHeight p a : ℚ) := by
    have hbs : (b s : ℚ) = ∑ j, (a j : ℚ) * g (Pi.single j 1) s :=
      (congrFun hab s).symm.trans (linearMap_apply_eq_sum g _ s)
    rw [hbs]
    calc
      |∑ j, (a j : ℚ) * g (Pi.single j 1) s| ≤
          ∑ j, |(a j : ℚ) * g (Pi.single j 1) s| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |(a j : ℚ)| * |g (Pi.single j 1) s| := by simp only [abs_mul]
      _ ≤ ∑ j, (coefficientHeight p a : ℚ) * |g (Pi.single j 1) s| := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (ha j) (abs_nonneg _)
      _ = (coefficientHeight p a : ℚ) * ∑ j, |g (Pi.single j 1) s| :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (coefficientHeight p a : ℚ) * (C : ℚ) :=
        mul_le_mul_of_nonneg_left (hrow s) (Nat.cast_nonneg _)
      _ = (C : ℚ) * (coefficientHeight p a : ℚ) := mul_comm _ _
  have hbNat (s : Fin r) : (b s).natAbs ≤ C * coefficientHeight p a := by
    have hh : ((b s).natAbs : ℚ) ≤ ((C * coefficientHeight p a : ℕ) : ℚ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_mul] using hb s
    exact_mod_cast hh
  have hH : coefficientHeight p a ≤ C * coefficientHeight p a := by
    simpa using Nat.mul_le_mul_right (coefficientHeight p a) hC1
  unfold coefficientHeight
  apply max_le
  · exact (two_le_coefficientHeight p a).trans hH
  · apply max_le
    · exact (natAbs_constant_le_height p a).trans hH
    · exact Finset.sup_le fun s _ => hbNat s

/-- Injectivity after extending scalars to the rationals supplies a reverse
height comparison with a single constant valid for every integer tuple. -/
theorem exists_reverse_height_bound_of_injective
    (v : Fin r → Fin k → ℤ) (hv : Function.Injective (rationalCombination v)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℤ) (b : Fin r → ℤ),
      coefficientHeight p b ≤ C * coefficientHeight p (integerCombination v b) := by
  let f := rationalCombination v
  have hker : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr hv
  obtain ⟨C, hC, hbound⟩ := exists_height_bound_of_rational_linearMap f.leftInverse
  refine ⟨C, hC, ?_⟩
  intro p b
  apply hbound p (integerCombination v b) b
  rw [← rationalCombination_intCast]
  exact LinearMap.leftInverse_apply_of_inj hker _

/-- Rational independence of the integer rows is sufficient for the reverse
height estimate. Together with the forward bound in `LatticeReduction`, this
gives equivalence of the two heights up to fixed multiplicative constants. -/
theorem exists_reverse_height_bound
    (v : Fin r → Fin k → ℤ)
    (hv : LinearIndependent ℚ (fun s j => (v s j : ℚ))) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℤ) (b : Fin r → ℤ),
      coefficientHeight p b ≤ C * coefficientHeight p (integerCombination v b) :=
  exists_reverse_height_bound_of_injective v hv.fintypeLinearCombination_injective

end
end LatticeHeightComparison
end GeneralizedLogarithms

/-- info: 'GeneralizedLogarithms.LatticeHeightComparison.exists_height_bound_of_rational_linearMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.LatticeHeightComparison.exists_height_bound_of_rational_linearMap

/-- info: 'GeneralizedLogarithms.LatticeHeightComparison.exists_reverse_height_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.LatticeHeightComparison.exists_reverse_height_bound
