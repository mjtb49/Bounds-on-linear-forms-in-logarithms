import GeneralizedLogarithms.SubspaceLowerBound

/-!
# Exceptional forms escape finite families of proper rational subspaces

The failure input is at one specified exponent. Conditional lower-rank bounds
make the exceptional forms in each proper rational subspace finite. Their
finite union can therefore be avoided while imposing any height threshold.
No higher-rank lower bound or general-position selection is assumed.
-/

namespace GeneralizedLogarithms.GeneralPositionSelection

noncomputable section

variable {k : ℕ}

/-- Failure at a fixed exponent supplies large strict exceptions outside any
fixed finite set of coefficient tuples. -/
theorem exceptional_form_outside_finite_set
    (α : Fin k → ℚ) (ν : ℝ)
    (hfailure : ¬ ∃ H₀ : ℕ, ∀ (p : ℤ) (a : Fin k → ℤ),
      H₀ ≤ coefficientHeight p a →
        (coefficientHeight p a : ℝ) ^ (-ν) ≤ |linearForm α p a|)
    (E : Set (ℤ × (Fin k → ℤ))) (hE : E.Finite) (T : ℕ) :
    ∃ (p : ℤ) (a : Fin k → ℤ), T ≤ coefficientHeight p a ∧
      |linearForm α p a| < (coefficientHeight p a : ℝ) ^ (-ν) ∧ (p, a) ∉ E := by
  classical
  let M := hE.toFinset.sup (fun x => coefficientHeight x.1 x.2)
  push Not at hfailure
  obtain ⟨p, a, hH, hbad⟩ := hfailure (max T (M + 1))
  refine ⟨p, a, (le_max_left _ _).trans hH, hbad, ?_⟩
  intro hmem
  have hupper : coefficientHeight p a ≤ M :=
    Finset.le_sup (f := fun x => coefficientHeight x.1 x.2)
      (hE.mem_toFinset.mpr hmem)
  have hlower : M + 1 ≤ coefficientHeight p a := (le_max_right _ _).trans hH
  omega

/-- Strict exceptions have nonzero logarithmic coefficient vectors once the
height exceeds two and the exponent is nonnegative. -/
theorem exceptional_coefficient_ne_zero
    (α : Fin k → ℚ) (ν : ℝ) (hν : 0 ≤ ν) (p : ℤ) (a : Fin k → ℤ)
    (hH : 3 ≤ coefficientHeight p a)
    (hbad : |linearForm α p a| < (coefficientHeight p a : ℝ) ^ (-ν)) : a ≠ 0 := by
  intro ha
  subst a
  have hp : p ≠ 0 := by
    intro hp
    subst p
    simp only [coefficientHeight_zero] at hH
    omega
  exact (not_lt_of_ge (lower_bound_zero_coefficients α p hp ν hν)) hbad

/-- Given positive lower-rank bounds, strict exceptions at the fixed exponent
`ν > k` escape every finite family of proper rational subspaces at arbitrarily
large heights. -/
theorem exceptional_form_outside_subspaces
    (α : Fin k → ℚ) (hα : ∀ j, 0 < α j) (hind : MultiplicativelyIndependent α)
    (hlower : ∀ r : ℕ, 0 < r → r < k → ∀ β : Fin r → ℚ,
      (∀ s, 0 < β s) → MultiplicativelyIndependent β → EventualLinearFormLowerBound β)
    (ν : ℝ) (hν : (k : ℝ) < ν)
    (hfailure : ¬ ∃ H₀ : ℕ, ∀ (p : ℤ) (a : Fin k → ℤ),
      H₀ ≤ coefficientHeight p a →
        (coefficientHeight p a : ℝ) ^ (-ν) ≤ |linearForm α p a|)
    (S : Finset (Submodule ℚ (Fin k → ℚ))) (hS : ∀ W ∈ S, W ≠ ⊤) (T : ℕ) :
    ∃ (p : ℤ) (a : Fin k → ℤ), T ≤ coefficientHeight p a ∧ a ≠ 0 ∧
      |linearForm α p a| < (coefficientHeight p a : ℝ) ^ (-ν) ∧
      ∀ W ∈ S, (fun j => (a j : ℚ)) ∉ W := by
  classical
  let E : Set (ℤ × (Fin k → ℤ)) := ⋃ W ∈ (S : Set (Submodule ℚ (Fin k → ℚ))),
    {x | (fun j => (x.2 j : ℚ)) ∈ W ∧
      |linearForm α x.1 x.2| < (coefficientHeight x.1 x.2 : ℝ) ^ (-ν)}
  have hE : E.Finite := by
    apply S.finite_toSet.biUnion
    intro W hW
    apply SubspaceLowerBound.finite_exceptions_on_subspace α hα hind W (hS W hW) hlower ν
    have hrank : Module.finrank ℚ W ≤ k := by simpa using W.finrank_le
    exact (show (Module.finrank ℚ W : ℝ) ≤ k by exact_mod_cast hrank).trans_lt hν
  obtain ⟨p, a, hH, hbad, hescape⟩ :=
    exceptional_form_outside_finite_set α ν hfailure E hE (max T 3)
  refine ⟨p, a, (le_max_left _ _).trans hH,
    exceptional_coefficient_ne_zero α ν ((Nat.cast_nonneg k).trans hν.le) p a
      ((le_max_right _ _).trans hH) hbad, hbad, ?_⟩
  intro W hW ha
  apply hescape
  exact Set.mem_iUnion_of_mem W (Set.mem_iUnion_of_mem hW ⟨ha, hbad⟩)

/-- One concrete extension step for general-position selection: the next
exception can avoid the span of every subset of fewer than `k` previous rows.
No independence assumption on the previous rows is needed for this step. -/
theorem exceptional_form_outside_small_spans {n : ℕ}
    (α : Fin k → ℚ) (hα : ∀ j, 0 < α j) (hind : MultiplicativelyIndependent α)
    (hlower : ∀ r : ℕ, 0 < r → r < k → ∀ β : Fin r → ℚ,
      (∀ s, 0 < β s) → MultiplicativelyIndependent β → EventualLinearFormLowerBound β)
    (ν : ℝ) (hν : (k : ℝ) < ν)
    (hfailure : ¬ ∃ H₀ : ℕ, ∀ (p : ℤ) (a : Fin k → ℤ),
      H₀ ≤ coefficientHeight p a →
        (coefficientHeight p a : ℝ) ^ (-ν) ≤ |linearForm α p a|)
    (previous : Fin n → Fin k → ℤ) (T : ℕ) :
    ∃ (p : ℤ) (a : Fin k → ℤ), T ≤ coefficientHeight p a ∧ a ≠ 0 ∧
      |linearForm α p a| < (coefficientHeight p a : ℝ) ^ (-ν) ∧
      ∀ s : Finset (Fin n), s.card < k → (fun j => (a j : ℚ)) ∉
        Submodule.span ℚ (Set.range (fun i : s => fun j => (previous i.val j : ℚ))) := by
  classical
  let U (s : Finset (Fin n)) :=
    Submodule.span ℚ (Set.range (fun i : s => fun j => (previous i.val j : ℚ)))
  let S := (Finset.univ.filter (fun s : Finset (Fin n) => s.card < k)).image U
  have hproper : ∀ W ∈ S, W ≠ ⊤ := by
    intro W hW
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hW
    have hsk : s.card < k := (Finset.mem_filter.mp hs).2
    have hdim : Module.finrank ℚ (U s) ≤ s.card := by
      simpa only [U, Set.finrank, Fintype.card_coe] using
        finrank_range_le_card (fun i : s => fun j => (previous i.val j : ℚ))
    intro heq
    rw [heq] at hdim
    have hkdim : k ≤ s.card := by simpa using hdim
    omega
  obtain ⟨p, a, hH, ha, hbad, hescape⟩ :=
    exceptional_form_outside_subspaces α hα hind hlower ν hν hfailure S hproper T
  refine ⟨p, a, hH, ha, hbad, ?_⟩
  intro s hs
  exact hescape (U s) (Finset.mem_image.mpr
    ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, rfl⟩)

end
end GeneralizedLogarithms.GeneralPositionSelection

/-- info: 'GeneralizedLogarithms.GeneralPositionSelection.exceptional_form_outside_finite_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.GeneralPositionSelection.exceptional_form_outside_finite_set

/-- info: 'GeneralizedLogarithms.GeneralPositionSelection.exceptional_form_outside_subspaces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.GeneralPositionSelection.exceptional_form_outside_subspaces

/-- info: 'GeneralizedLogarithms.GeneralPositionSelection.exceptional_form_outside_small_spans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.GeneralPositionSelection.exceptional_form_outside_small_spans
