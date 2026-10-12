import GeneralizedLogarithms.RationalSubspaceLattice
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Conditional lower bounds on fixed rational subspaces

An eventual lower bound for the monomial basis transfers to its integer
coefficient lattice. The two fixed height-comparison constants are absorbed
using an intermediate exponent. Thus positive-rank induction inputs imply
only finitely many exceptional forms on each proper rational subspace. The
rank-zero case is proved directly, rather than assumed in the induction input.
-/

namespace GeneralizedLogarithms.SubspaceLowerBound

noncomputable section

open Filter
open scoped Topology

/-- Fixed multiplicative height losses are absorbed by a strict exponent gap. -/
theorem eventually_rpow_le_scaled_rpow (C μ ν : ℝ) (hC : 0 < C) (hμν : μ < ν) :
    ∀ᶠ H : ℕ in atTop, (H : ℝ) ^ (-ν) ≤ (C * H) ^ (-μ) := by
  have hlim := (tendsto_rpow_neg_atTop (sub_pos.mpr hμν)).comp
    tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ H : ℕ in atTop, (H : ℝ) ^ (-(ν - μ)) < C ^ (-μ) :=
    hlim.eventually (gt_mem_nhds (Real.rpow_pos_of_pos hC (-μ)))
  filter_upwards [hsmall, eventually_ge_atTop 1] with H hH hH1
  have hpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  calc
    (H : ℝ) ^ (-ν) = (H : ℝ) ^ (-(ν - μ)) * (H : ℝ) ^ (-μ) := by
      rw [← Real.rpow_add hpos]
      congr 1
      ring
    _ ≤ C ^ (-μ) * (H : ℝ) ^ (-μ) :=
      mul_le_mul_of_nonneg_right hH.le (Real.rpow_nonneg hpos.le _)
    _ = (C * H) ^ (-μ) := (Real.mul_rpow hC.le hpos.le).symm

/-- The zero-dimensional lower bound is elementary: at height at least three,
the constant integer is nonzero. -/
theorem eventualLowerBound_rank_zero (α : Fin 0 → ℚ) :
    EventualLinearFormLowerBound α := by
  intro ν hν
  have hνpos : 0 < ν := by simpa using hν
  refine ⟨3, ?_⟩
  intro p a hH
  have ha : a = 0 := Subsingleton.elim _ _
  subst a
  have hp : p ≠ 0 := by
    intro hp
    subst p
    simp [coefficientHeight] at hH
  exact lower_bound_zero_coefficients α p hp ν hνpos.le

/-- A fixed independent integer change of coefficients transfers the exact
eventual lower-bound predicate, with any exponent larger than the row rank. -/
theorem eventual_lowerBound_integerCombination {r k : ℕ}
    (α : Fin k → ℚ) (hα : ∀ j, 0 < α j) (v : Fin r → Fin k → ℤ)
    (hv : LinearIndependent ℚ (fun s j => (v s j : ℚ)))
    (hbound : EventualLinearFormLowerBound (monomialBasis α v))
    (ν : ℝ) (hν : (r : ℝ) < ν) :
    ∃ H₀ : ℕ, ∀ (p : ℤ) (b : Fin r → ℤ),
      H₀ ≤ coefficientHeight p (integerCombination v b) →
        (coefficientHeight p (integerCombination v b) : ℝ) ^ (-ν) ≤
          |linearForm α p (integerCombination v b)| := by
  let μ : ℝ := ((r : ℝ) + ν) / 2
  have hrμ : (r : ℝ) < μ := by dsimp [μ]; linarith
  have hμν : μ < ν := by dsimp [μ]; linarith
  have hμpos : 0 < μ := (Nat.cast_nonneg r).trans_lt hrμ
  obtain ⟨Hβ, hβ⟩ := hbound μ hrμ
  obtain ⟨C, hC, hreverse⟩ := LatticeHeightComparison.exists_reverse_height_bound v hv
  have hCR : (0 : ℝ) < C := by exact_mod_cast (by omega : 0 < C)
  obtain ⟨Habs, habs⟩ := eventually_atTop.mp
    (eventually_rpow_le_scaled_rpow (C : ℝ) μ ν hCR hμν)
  let D := integerBasisSize v
  refine ⟨max Habs (D * Hβ), ?_⟩
  intro p b hH
  have hforward := coefficientHeight_integerCombination_le v p b
  have hreach : Hβ ≤ coefficientHeight p b := by
    have hD : 1 ≤ D := one_le_integerBasisSize v
    have hlarge : D * Hβ ≤ D * coefficientHeight p b :=
      (le_max_right Habs (D * Hβ)).trans (hH.trans hforward)
    by_contra hnot
    have hlt : coefficientHeight p b < Hβ := lt_of_not_ge hnot
    nlinarith
  have hHb : (0 : ℝ) < coefficientHeight p b := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (two_le_coefficientHeight p b))
  have hreverseR : (coefficientHeight p b : ℝ) ≤
      (C : ℝ) * coefficientHeight p (integerCombination v b) := by
    exact_mod_cast hreverse p b
  calc
    _ ≤ ((C : ℝ) * coefficientHeight p (integerCombination v b)) ^ (-μ) :=
      habs _ ((le_max_left _ _).trans hH)
    _ ≤ (coefficientHeight p b : ℝ) ^ (-μ) :=
      Real.rpow_le_rpow_of_nonpos hHb hreverseR (neg_nonpos.mpr hμpos.le)
    _ ≤ |linearForm (monomialBasis α v) p b| := hβ p b hreach
    _ = _ := by rw [linearForm_monomialBasis α hα v p b]

/-- Bounds assumed only in positive ranks below `k` give a bound on each fixed
proper rational subspace, at any exponent exceeding that subspace's rank. -/
theorem eventual_lowerBound_on_subspace {k : ℕ}
    (α : Fin k → ℚ) (hα : ∀ j, 0 < α j) (hind : MultiplicativelyIndependent α)
    (W : Submodule ℚ (Fin k → ℚ)) (hW : W ≠ ⊤)
    (hlower : ∀ r : ℕ, 0 < r → r < k → ∀ β : Fin r → ℚ,
      (∀ s, 0 < β s) → MultiplicativelyIndependent β → EventualLinearFormLowerBound β)
    (ν : ℝ) (hν : (Module.finrank ℚ W : ℝ) < ν) :
    ∃ H₀ : ℕ, ∀ (p : ℤ) (a : Fin k → ℤ),
      (fun j => (a j : ℚ)) ∈ W → H₀ ≤ coefficientHeight p a →
        (coefficientHeight p a : ℝ) ^ (-ν) ≤ |linearForm α p a| := by
  obtain ⟨r, v, hr, hvZ, hvQ, _, hrepr⟩ := RationalSubspaceLattice.exists_integer_basis W
  have hrk : r < k := by
    have hdim := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hW)
    simpa [← hr] using hdim
  have hβ : EventualLinearFormLowerBound (monomialBasis α v) := by
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · rcases hr0 with rfl
      exact eventualLowerBound_rank_zero _
    · exact hlower r hrpos hrk _ (monomialBasis_pos α hα v)
        (multiplicativelyIndependent_monomialBasis α hα hind v hvZ)
  obtain ⟨H₀, hH₀⟩ := eventual_lowerBound_integerCombination α hα v hvQ hβ ν (by simpa [hr] using hν)
  refine ⟨H₀, ?_⟩
  intro p a ha hH
  obtain ⟨b, hb, _⟩ := (hrepr a).mp ha
  simpa only [hb] using hH₀ p b (by simpa only [hb] using hH)

/-- A fixed proper rational subspace contains only finitely many strict
exceptions once the positive lower-rank eventual bounds are supplied. -/
theorem finite_exceptions_on_subspace {k : ℕ}
    (α : Fin k → ℚ) (hα : ∀ j, 0 < α j) (hind : MultiplicativelyIndependent α)
    (W : Submodule ℚ (Fin k → ℚ)) (hW : W ≠ ⊤)
    (hlower : ∀ r : ℕ, 0 < r → r < k → ∀ β : Fin r → ℚ,
      (∀ s, 0 < β s) → MultiplicativelyIndependent β → EventualLinearFormLowerBound β)
    (ν : ℝ) (hν : (Module.finrank ℚ W : ℝ) < ν) :
    {x : ℤ × (Fin k → ℤ) | (fun j => (x.2 j : ℚ)) ∈ W ∧
      |linearForm α x.1 x.2| < (coefficientHeight x.1 x.2 : ℝ) ^ (-ν)}.Finite := by
  obtain ⟨H₀, hH₀⟩ := eventual_lowerBound_on_subspace α hα hind W hW hlower ν hν
  apply (finite_bounded_height k H₀).subset
  intro x hx
  have hlt : coefficientHeight x.1 x.2 < H₀ := by
    apply lt_of_not_ge
    intro hH
    exact (not_lt_of_ge (hH₀ x.1 x.2 hx.1 hH)) hx.2
  exact hlt.le

end
end GeneralizedLogarithms.SubspaceLowerBound

/-- info: 'GeneralizedLogarithms.SubspaceLowerBound.eventualLowerBound_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.SubspaceLowerBound.eventualLowerBound_rank_zero

/-- info: 'GeneralizedLogarithms.SubspaceLowerBound.eventual_lowerBound_on_subspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.SubspaceLowerBound.eventual_lowerBound_on_subspace

/-- info: 'GeneralizedLogarithms.SubspaceLowerBound.finite_exceptions_on_subspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.SubspaceLowerBound.finite_exceptions_on_subspace
