import GeneralizedLogarithms.LatticeHeightComparison
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.Integer

/-!
# The integer lattice of a rational subspace

Every rational subspace of `ℚ^k` has an integer basis for its full intersection
with `ℤ^k`. The same rows are rationally independent and span the given
subspace. In particular, this does not replace the full lattice by a
finite-index sublattice obtained by merely clearing a chosen rational basis.
-/

namespace GeneralizedLogarithms.RationalSubspaceLattice

noncomputable section

open scoped BigOperators nonZeroDivisors

variable {k : ℕ}

def castLinearMap (k : ℕ) : (Fin k → ℤ) →ₗ[ℤ] (Fin k → ℚ) where
  toFun := fun a j => (a j : ℚ)
  map_add' := by intros; ext j; simp
  map_smul' := by intros; ext j; simp [zsmul_eq_mul]

theorem castLinearMap_injective (k : ℕ) : Function.Injective (castLinearMap k) := by
  intro a b hab
  ext j
  have hj : (a j : ℚ) = (b j : ℚ) := congrFun hab j
  exact_mod_cast hj

/-- The saturated integer lattice inside a rational subspace. -/
def integerPoints (W : Submodule ℚ (Fin k → ℚ)) : Submodule ℤ (Fin k → ℤ) :=
  (W.restrictScalars ℤ).comap (castLinearMap k)

@[simp] theorem mem_integerPoints (W : Submodule ℚ (Fin k → ℚ)) (a : Fin k → ℤ) :
    a ∈ integerPoints W ↔ (fun j => (a j : ℚ)) ∈ W := Iff.rfl

/-- A single nonzero integer clears all coordinates of a rational vector. -/
theorem exists_integer_multiple (x : Fin k → ℚ) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ a : Fin k → ℤ,
      (fun j => (a j : ℚ)) = (n : ℚ) • x := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite ℤ⁰ x
  change ∀ j, ∃ a : ℤ, (a : ℚ) = (d : ℤ) • x j at hd
  choose a ha using hd
  refine ⟨d, nonZeroDivisors.coe_ne_zero d, a, ?_⟩
  ext j
  simpa [Algebra.smul_def] using ha j

theorem cast_integerCombination_mem_span {r : ℕ} (v : Fin r → Fin k → ℤ)
    (b : Fin r → ℤ) :
    (fun j => (integerCombination v b j : ℚ)) ∈
      Submodule.span ℚ (Set.range (fun s j => (v s j : ℚ))) := by
  rw [← LatticeHeightComparison.rationalCombination_intCast]
  simp only [LatticeHeightComparison.rationalCombination, Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro s _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

/-- Clearing denominators upgrades integral spanning of all integer points
to rational spanning of the original subspace. -/
theorem rational_span_eq_of_integer_points_span {r : ℕ}
    (W : Submodule ℚ (Fin k → ℚ)) (v : Fin r → Fin k → ℤ)
    (hv : ∀ s, (fun j => (v s j : ℚ)) ∈ W)
    (hspan : ∀ a : Fin k → ℤ, (fun j => (a j : ℚ)) ∈ W →
      ∃ b, integerCombination v b = a) :
    Submodule.span ℚ (Set.range (fun s j => (v s j : ℚ))) = W := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    exact hv s
  · intro x hx
    obtain ⟨n, hn, a, ha⟩ := exists_integer_multiple x
    have haW : (fun j => (a j : ℚ)) ∈ W := by
      rw [ha]
      exact W.smul_mem _ hx
    obtain ⟨b, hb⟩ := hspan a haW
    have haSpan : (fun j => (a j : ℚ)) ∈
        Submodule.span ℚ (Set.range (fun s j => (v s j : ℚ))) := by
      rw [← hb]
      exact cast_integerCombination_mem_span v b
    have hscaled := (Submodule.span ℚ (Set.range (fun s j => (v s j : ℚ)))).smul_mem
      (n : ℚ)⁻¹ haSpan
    have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    simpa only [ha, smul_smul, inv_mul_cancel₀ hnQ, one_smul] using hscaled

/-- A basis of the full integer lattice in a rational subspace. It has the
expected rational rank, and every integral point has unique integer
coordinates. The zero-dimensional case is included. -/
theorem exists_integer_basis (W : Submodule ℚ (Fin k → ℚ)) :
    ∃ r : ℕ, ∃ v : Fin r → Fin k → ℤ,
      r = Module.finrank ℚ W ∧
      LinearIndependent ℤ v ∧
      LinearIndependent ℚ (fun s j => (v s j : ℚ)) ∧
      Submodule.span ℚ (Set.range (fun s j => (v s j : ℚ))) = W ∧
      ∀ a : Fin k → ℤ, (fun j => (a j : ℚ)) ∈ W ↔
        ∃! b : Fin r → ℤ, integerCombination v b = a := by
  classical
  obtain ⟨r, b⟩ := (integerPoints W).basisOfPid (Pi.basisFun ℤ (Fin k))
  let v : Fin r → Fin k → ℤ := fun s => (b s : Fin k → ℤ)
  have hvZ : LinearIndependent ℤ v := by
    simpa only [v, Function.comp_def, Submodule.coe_subtype] using
      b.linearIndependent.map' (integerPoints W).subtype (Submodule.ker_subtype _)
  have hvQ : LinearIndependent ℚ (fun s j => (v s j : ℚ)) := by
    apply (LinearIndependent.iff_fractionRing ℤ ℚ).mp
    change LinearIndependent ℤ ((castLinearMap k) ∘ v)
    exact hvZ.map' (castLinearMap k) (LinearMap.ker_eq_bot.mpr (castLinearMap_injective k))
  have hrepr (a : Fin k → ℤ) : (fun j => (a j : ℚ)) ∈ W ↔
      ∃ t : Fin r → ℤ, integerCombination v t = a := by
    change a ∈ integerPoints W ↔ _
    rw [b.mem_submodule_iff']
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, (integerCombination_eq_sum_smul v t).trans ht.symm⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, ht.symm.trans (integerCombination_eq_sum_smul v t)⟩
  have hvW (s : Fin r) : (fun j => (v s j : ℚ)) ∈ W := (b s).property
  have hspan := rational_span_eq_of_integer_points_span W v hvW
    (fun a ha => (hrepr a).mp ha)
  have hr : r = Module.finrank ℚ W := by
    rw [← hspan, finrank_span_eq_card hvQ]
    simp
  refine ⟨r, v, hr, hvZ, hvQ, hspan, ?_⟩
  intro a
  constructor
  · intro ha
    obtain ⟨t, ht⟩ := (hrepr a).mp ha
    refine ⟨t, ht, ?_⟩
    intro u hu
    exact integerCombination_injective v hvZ (hu.trans ht.symm)
  · rintro ⟨t, ht, _⟩
    exact (hrepr a).mpr ⟨t, ht⟩

end
end GeneralizedLogarithms.RationalSubspaceLattice

/-- info: 'GeneralizedLogarithms.RationalSubspaceLattice.exists_integer_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.RationalSubspaceLattice.exists_integer_basis
