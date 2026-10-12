import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.StdBasis

/-!
# Dimensions forced by disjoint coordinate blocks

The intended application is to the generic conormal space of a persistent
component. The two factors of `X × Y` are the additive and logarithmic
coordinate covectors. Constancy on the component places the required covectors
in the conormal subspace. This file proves the ensuing dimension inequalities;
it does not assume independence of the combined family.
-/

namespace GeneralizedLogarithms

open Module

section Blocks

variable {K X Y : Type*} [Field K]
variable [AddCommGroup X] [Module K X] [FiniteDimensional K X]
variable [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]

/-- Subspaces in different coordinate blocks contribute additively to dimension.
The injectivity required for the dimension estimate follows from the two
coordinate projections. -/
theorem finrank_add_le_of_block_mem
    (A : Submodule K X) (B : Submodule K Y) (N : Submodule K (X × Y))
    (hA : ∀ x ∈ A, (x, (0 : Y)) ∈ N)
    (hB : ∀ y ∈ B, ((0 : X), y) ∈ N) :
    finrank K A + finrank K B ≤ finrank K N := by
  let f : (A × B) →ₗ[K] N :=
    { toFun := fun z => ⟨((z.1 : X), (z.2 : Y)), by
        simpa using N.add_mem (hA z.1 z.1.property) (hB z.2 z.2.property)⟩
      map_add' := by intro z w; rfl
      map_smul' := by intro a z; rfl }
  have hf : Function.Injective f := by
    intro z w h
    have hval : ((z.1 : X), (z.2 : Y)) = ((w.1 : X), (w.2 : Y)) :=
      congrArg Subtype.val h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hval)
    · exact Subtype.ext (congrArg Prod.snd hval)
  simpa only [Module.finrank_prod] using f.finrank_le_finrank_of_injective hf

end Blocks

section Coordinates

variable {K I J Y : Type*} [Field K] [Fintype I] [Fintype J] [DecidableEq J]
variable [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]

/-- Selected, distinct additive coordinate covectors together with a longitudinal
subspace force `card I + dim B` conormal dimensions. The coordinate independence
is proved using the standard basis and the injectivity of `e`. -/
theorem coordinate_card_add_finrank_le
    (e : I ↪ J) (B : Submodule K Y) (N : Submodule K ((J → K) × Y))
    (hX : ∀ i, ((Pi.single (e i) 1 : J → K), (0 : Y)) ∈ N)
    (hY : ∀ y ∈ B, ((0 : J → K), y) ∈ N) :
    Fintype.card I + finrank K B ≤ finrank K N := by
  classical
  let v : I → (J → K) := fun i => (Pi.basisFun K J) (e i)
  let A : Submodule K (J → K) := Submodule.span K (Set.range v)
  have hv : LinearIndependent K v :=
    (Pi.basisFun K J).linearIndependent.comp e e.injective
  have hA : ∀ x ∈ A, (x, (0 : Y)) ∈ N := by
    have hle : A ≤ N.comap (LinearMap.inl K (J → K) Y) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      simpa [v] using hX i
    exact fun x hx => hle hx
  have hdim : finrank K A = Fintype.card I := finrank_span_eq_card hv
  simpa only [hdim] using finrank_add_le_of_block_mem A B N hA hY

/-- A single nonzero longitudinal covector gives the strict inequality `c > r`.
Here `c = finrank K N` and `r = Fintype.card I`. -/
theorem coordinate_card_add_one_le
    (e : I ↪ J) (N : Submodule K ((J → K) × Y)) (η : Y)
    (hη : η ≠ 0)
    (hX : ∀ i, ((Pi.single (e i) 1 : J → K), (0 : Y)) ∈ N)
    (hY : ((0 : J → K), η) ∈ N) :
    Fintype.card I + 1 ≤ finrank K N := by
  classical
  have hspan : ∀ y ∈ Submodule.span K ({η} : Set Y), ((0 : J → K), y) ∈ N := by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simpa using N.smul_mem a hY
  have h := coordinate_card_add_finrank_le e (Submodule.span K ({η} : Set Y)) N hX hspan
  simpa only [finrank_span_singleton hη] using h

/-- A family of longitudinal covectors contributes the dimension of its span.
No independence of this family is needed for this rank-sensitive estimate. -/
theorem coordinate_card_add_span_finrank_le
    {L : Type*} (e : I ↪ J) (a : L → Y) (N : Submodule K ((J → K) × Y))
    (hX : ∀ i, ((Pi.single (e i) 1 : J → K), (0 : Y)) ∈ N)
    (hY : ∀ l, ((0 : J → K), a l) ∈ N) :
    Fintype.card I + finrank K (Submodule.span K (Set.range a)) ≤ finrank K N := by
  classical
  apply coordinate_card_add_finrank_le e (Submodule.span K (Set.range a)) N hX
  have hle : Submodule.span K (Set.range a) ≤
      N.comap (LinearMap.inr K (J → K) Y) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    exact hY l
  exact fun y hy => hle hy

/-- Under independence of the longitudinal rows, the same argument gives
`c ≥ r + s`. In particular, a family indexed by `I` gives `c ≥ 2r`. -/
theorem coordinate_card_add_card_le
    {L : Type*} [Fintype L] (e : I ↪ J) (a : L → Y)
    (ha : LinearIndependent K a) (N : Submodule K ((J → K) × Y))
    (hX : ∀ i, ((Pi.single (e i) 1 : J → K), (0 : Y)) ∈ N)
    (hY : ∀ l, ((0 : J → K), a l) ∈ N) :
    Fintype.card I + Fintype.card L ≤ finrank K N := by
  simpa only [finrank_span_eq_card ha] using
    coordinate_card_add_span_finrank_le e a N hX hY

end Coordinates

section LogarithmicRows

variable {K J : Type*} [Field K]

/-- Division by nonzero coordinate values preserves nonzeroness of a row. -/
theorem div_coordinates_ne_zero {a y : J → K}
    (ha : a ≠ 0) (hy : ∀ j, y j ≠ 0) :
    (fun j => a j / y j) ≠ 0 := by
  intro h
  apply ha
  funext j
  have hj := congrFun h j
  simpa [hy j] using hj

/-- A nonzero integer row gives a nonzero logarithmic covector in characteristic
zero, provided all multiplicative coordinates are nonzero. -/
theorem int_div_coordinates_ne_zero [CharZero K] {a : J → ℤ} {y : J → K}
    (ha : a ≠ 0) (hy : ∀ j, y j ≠ 0) :
    (fun j => (a j : K) / y j) ≠ 0 := by
  apply div_coordinates_ne_zero (y := y) ?_ hy
  intro h
  apply ha
  funext j
  have hj := congrFun h j
  simpa using hj

end LogarithmicRows

end GeneralizedLogarithms

/-- info: 'GeneralizedLogarithms.finrank_add_le_of_block_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.finrank_add_le_of_block_mem

/-- info: 'GeneralizedLogarithms.coordinate_card_add_span_finrank_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.coordinate_card_add_span_finrank_le

/-- info: 'GeneralizedLogarithms.coordinate_card_add_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.coordinate_card_add_one_le

/-- info: 'GeneralizedLogarithms.coordinate_card_add_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.coordinate_card_add_card_le

/-- info: 'GeneralizedLogarithms.int_div_coordinates_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.int_div_coordinates_ne_zero
