import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Abel
import GeneralizedLogarithms.ConormalDimension

/-!
# Conormal estimates for an actual normal quotient

Coefficient pairs in the transverse and longitudinal blocks define linear
forms on the ambient coordinate space. This map is injective, as seen by
evaluation on the standard coordinate vectors. Consequently the subspace of
coefficient pairs annihilating a tangent subspace embeds in its annihilator.
The dual-annihilator/quotient dimension identity then turns the disjoint-block
estimates into estimates for the dimension of the actual normal quotient.
-/

namespace GeneralizedLogarithms

noncomputable section

open Module

namespace GenericConormal

variable {K : Type*} [Field K] {k m : ℕ}

/-- A pair of transverse and longitudinal coefficient vectors defines a
covector on the ambient coordinates. -/
def coefficientMap : ((Fin m → K) × (Fin k → K)) →ₗ[K]
    Module.Dual K ((Fin k ⊕ Fin m) → K) where
  toFun u :=
    { toFun := fun t => (∑ i, u.1 i * t (Sum.inr i)) + ∑ r, u.2 r * t (Sum.inl r)
      map_add' := by
        intro t s
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        abel
      map_smul' := by
        intro b t
        simp [Finset.mul_sum, mul_add, mul_left_comm] }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro t
    change ((∑ i, (u.1 i + v.1 i) * t (Sum.inr i)) +
      ∑ r, (u.2 r + v.2 r) * t (Sum.inl r)) =
      ((∑ i, u.1 i * t (Sum.inr i)) + ∑ r, u.2 r * t (Sum.inl r)) +
      ((∑ i, v.1 i * t (Sum.inr i)) + ∑ r, v.2 r * t (Sum.inl r))
    simp only [add_mul, Finset.sum_add_distrib]
    abel
  map_smul' := by
    intro b u
    ext t
    simp [Finset.mul_sum, mul_add, mul_assoc]

@[simp] theorem coefficientMap_apply (u : (Fin m → K) × (Fin k → K))
    (t : (Fin k ⊕ Fin m) → K) :
    coefficientMap u t = (∑ i, u.1 i * t (Sum.inr i)) + ∑ r, u.2 r * t (Sum.inl r) := rfl

@[simp] theorem coefficientMap_standard_inr
    (u : (Fin m → K) × (Fin k → K)) (i : Fin m) :
    coefficientMap u (Pi.single (Sum.inr i) 1) = u.1 i := by
  simp [coefficientMap_apply, Pi.single_apply]

@[simp] theorem coefficientMap_standard_inl
    (u : (Fin m → K) × (Fin k → K)) (r : Fin k) :
    coefficientMap u (Pi.single (Sum.inl r) 1) = u.2 r := by
  simp [coefficientMap_apply, Pi.single_apply]

theorem coefficientMap_injective : Function.Injective (coefficientMap (K := K) (k := k) (m := m)) := by
  intro u v h
  apply Prod.ext
  · funext i
    have hi := LinearMap.congr_fun h (Pi.single (Sum.inr i) 1)
    simpa only [coefficientMap_standard_inr] using hi
  · funext r
    have hr := LinearMap.congr_fun h (Pi.single (Sum.inl r) 1)
    simpa only [coefficientMap_standard_inl] using hr

/-- The coefficient vectors annihilating the tangent subspace. -/
def coefficientAnnihilator (T : Submodule K ((Fin k ⊕ Fin m) → K)) :
    Submodule K ((Fin m → K) × (Fin k → K)) :=
  T.dualAnnihilator.comap coefficientMap

@[simp] theorem mem_coefficientAnnihilator
    (T : Submodule K ((Fin k ⊕ Fin m) → K))
    (u : (Fin m → K) × (Fin k → K)) :
    u ∈ coefficientAnnihilator T ↔ ∀ t ∈ T,
      (∑ i, u.1 i * t (Sum.inr i)) + ∑ r, u.2 r * t (Sum.inl r) = 0 := by
  change coefficientMap u ∈ T.dualAnnihilator ↔ _
  rw [Submodule.mem_dualAnnihilator]
  rfl

/-- The coefficient annihilator has dimension at most the normal quotient.
This comparison is proved from the injective coefficient map and the standard
duality equivalence, with no assumed equality of dimensions. -/
theorem finrank_coefficientAnnihilator_le_normalQuotient
    (T : Submodule K ((Fin k ⊕ Fin m) → K)) :
    finrank K (coefficientAnnihilator T) ≤ finrank K (((Fin k ⊕ Fin m) → K) ⧸ T) := by
  let f : coefficientAnnihilator T →ₗ[K] T.dualAnnihilator :=
    { toFun := fun u => ⟨coefficientMap u, u.property⟩
      map_add' := by
        intro u v
        apply Subtype.ext
        exact map_add coefficientMap
          (u : (Fin m → K) × (Fin k → K)) (v : (Fin m → K) × (Fin k → K))
      map_smul' := by
        intro b u
        apply Subtype.ext
        exact map_smul coefficientMap b (u : (Fin m → K) × (Fin k → K)) }
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply coefficientMap_injective
    exact congrArg Subtype.val huv
  have hdim := f.finrank_le_finrank_of_injective hf
  rw [← (Subspace.quotEquivAnnihilator T).finrank_eq] at hdim
  exact hdim

variable {I : Type*} [Fintype I]

/-- Independent transverse coordinates and one nonzero longitudinal
annihilating row force the normal quotient to have dimension at least `r+1`.
The hypotheses describe actual vanishing on the tangent subspace. -/
theorem coordinate_card_add_one_le_normalQuotient
    (T : Submodule K ((Fin k ⊕ Fin m) → K)) (e : I ↪ Fin m)
    (η : Fin k → K) (hη : η ≠ 0)
    (hX : ∀ i : I, ∀ t ∈ T, t (Sum.inr (e i)) = 0)
    (hY : ∀ t ∈ T, ∑ r, η r * t (Sum.inl r) = 0) :
    Fintype.card I + 1 ≤ finrank K (((Fin k ⊕ Fin m) → K) ⧸ T) := by
  have hx : ∀ i : I, ((Pi.single (e i) 1 : Fin m → K), (0 : Fin k → K)) ∈
      coefficientAnnihilator T := by
    intro i
    rw [mem_coefficientAnnihilator]
    intro t ht
    simpa [Pi.single_apply] using hX i t ht
  have hy : ((0 : Fin m → K), η) ∈ coefficientAnnihilator T := by
    rw [mem_coefficientAnnihilator]
    intro t ht
    simpa using hY t ht
  exact (coordinate_card_add_one_le e (coefficientAnnihilator T) η hη hx hy).trans
    (finrank_coefficientAnnihilator_le_normalQuotient T)

/-- The same argument retains the full rank of a family of longitudinal rows. -/
theorem coordinate_card_add_span_finrank_le_normalQuotient
    {L : Type*} (T : Submodule K ((Fin k ⊕ Fin m) → K)) (e : I ↪ Fin m)
    (a : L → Fin k → K)
    (hX : ∀ i : I, ∀ t ∈ T, t (Sum.inr (e i)) = 0)
    (hY : ∀ l, ∀ t ∈ T, ∑ r, a l r * t (Sum.inl r) = 0) :
    Fintype.card I + finrank K (Submodule.span K (Set.range a)) ≤
      finrank K (((Fin k ⊕ Fin m) → K) ⧸ T) := by
  have hx : ∀ i : I, ((Pi.single (e i) 1 : Fin m → K), (0 : Fin k → K)) ∈
      coefficientAnnihilator T := by
    intro i
    rw [mem_coefficientAnnihilator]
    intro t ht
    simpa [Pi.single_apply] using hX i t ht
  have hy : ∀ l, ((0 : Fin m → K), a l) ∈ coefficientAnnihilator T := by
    intro l
    rw [mem_coefficientAnnihilator]
    intro t ht
    simpa using hY l t ht
  exact (coordinate_card_add_span_finrank_le e a (coefficientAnnihilator T) hx hy).trans
    (finrank_coefficientAnnihilator_le_normalQuotient T)

/-- A nonzero integer logarithmic row contributes the extra normal direction
once its transverse coordinate, together with the selected transverse
coordinates, is constant along the tangent subspace. -/
theorem coordinate_card_add_one_le_of_logarithmic_relation [CharZero K]
    (T : Submodule K ((Fin k ⊕ Fin m) → K)) (e : I ↪ Fin m)
    (i₀ : I) (a : Fin k → ℤ) (ha : a ≠ 0)
    (y : Fin k → K) (hy : ∀ r, y r ≠ 0)
    (hX : ∀ i : I, ∀ t ∈ T, t (Sum.inr (e i)) = 0)
    (hlog : ∀ t ∈ T,
      t (Sum.inr (e i₀)) = ∑ r, (a r : K) * (t (Sum.inl r) / y r)) :
    Fintype.card I + 1 ≤ finrank K (((Fin k ⊕ Fin m) → K) ⧸ T) := by
  apply coordinate_card_add_one_le_normalQuotient T e (fun r => (a r : K) / y r)
    (int_div_coordinates_ne_zero ha hy) hX
  intro t ht
  calc
    (∑ r, ((a r : K) / y r) * t (Sum.inl r)) =
        ∑ r, (a r : K) * (t (Sum.inl r) / y r) := by
      apply Finset.sum_congr rfl
      intro r _
      simp [div_eq_mul_inv, mul_assoc, mul_comm]
    _ = t (Sum.inr (e i₀)) := (hlog t ht).symm
    _ = 0 := hX i₀ t ht

end GenericConormal

end

end GeneralizedLogarithms

/-- info: 'GeneralizedLogarithms.GenericConormal.coefficientMap_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.GenericConormal.coefficientMap_injective

/-- info: 'GeneralizedLogarithms.GenericConormal.finrank_coefficientAnnihilator_le_normalQuotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.GenericConormal.finrank_coefficientAnnihilator_le_normalQuotient

/-- info: 'GeneralizedLogarithms.GenericConormal.coordinate_card_add_one_le_normalQuotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.GenericConormal.coordinate_card_add_one_le_normalQuotient

/-- info: 'GeneralizedLogarithms.GenericConormal.coordinate_card_add_span_finrank_le_normalQuotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.GenericConormal.coordinate_card_add_span_finrank_le_normalQuotient

/-- info: 'GeneralizedLogarithms.GenericConormal.coordinate_card_add_one_le_of_logarithmic_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.GenericConormal.coordinate_card_add_one_le_of_logarithmic_relation
