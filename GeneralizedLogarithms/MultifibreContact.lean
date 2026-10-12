import LogIrrationalityMeasure.LocalAlgebra.CoordinateContactBound
import LogIrrationalityMeasure.LocalAlgebra.FibreContact

/-!
# Contact bounds on a fibre with several constant longitudinal coordinates

Zero longitudinal branch coordinates can be removed from contact, and constant
longitudinal field coordinates can be removed from weighted degree. Injectivity
of the complete longitudinal center tuple then puts all relevant places over
one transverse center. The ordinary coordinate contact bound gives the theta
discount.

The main theorem explicitly assumes that the supplied contact equals ordinary
transverse contact. The multilogarithmic branch-coordinate identity needed to
discharge that assumption is not established in this module.
-/

namespace GeneralizedLogarithms.MultifibreContact

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open CurveValuationCenter CurveCenters PlaceValuationRing

/-- A block of zero branch coordinates does not affect contact. -/
theorem contact_zero_left {α β : Type*} [Fintype α] [Fintype β]
    (v : α ⊕ β → ℚ) (b : β → PowerSeries ℂ) (hb : ∃ i, b i ≠ 0)
    (hfull : ∃ i, (Sum.elim (fun _ : α => 0) b) i ≠ 0) :
    BranchContact.contact v (Sum.elim (fun _ : α => 0) b) hfull =
      BranchContact.contact (fun i => v (Sum.inr i)) b hb := by
  apply le_antisymm
  · obtain ⟨i, hi, he⟩ := BranchContact.exists_attains (fun i => v (Sum.inr i)) b hb
    have h := BranchContact.contact_le v (Sum.elim (fun _ : α => 0) b) hfull
      (Sum.inr i) hi
    exact h.trans_eq he.symm
  · obtain ⟨i, hi, he⟩ :=
      BranchContact.exists_attains v (Sum.elim (fun _ : α => 0) b) hfull
    cases i with
    | inl r => exact (hi rfl).elim
    | inr i =>
      exact (BranchContact.contact_le (fun i => v (Sum.inr i)) b hb i hi).trans_eq
        he.symm

/-- A block of zero coordinate orders does not affect weighted pole order. -/
theorem weightedPole_zero_left {α β : Type*} [Fintype α] [Fintype β]
    (w : α ⊕ β → ℚ) (b : β → ℚ) :
    WeightedCurveDegree.weightedPole w (Sum.elim (fun _ : α => 0) b) =
      WeightedCurveDegree.weightedPole (fun i => w (Sum.inr i)) b := by
  apply le_antisymm
  · apply FibreContact.weightedPole_le _ _ _
      (WeightedCurveDegree.weightedPole_nonneg _ _)
    intro j
    cases j with
    | inl r =>
      simpa only [Sum.elim_inl, neg_zero, zero_div] using
        WeightedCurveDegree.weightedPole_nonneg (fun i => w (Sum.inr i)) b
    | inr i => exact WeightedCurveDegree.div_le_weightedPole _ b i
  · apply FibreContact.weightedPole_le _ _ _
      (WeightedCurveDegree.weightedPole_nonneg _ _)
    intro i
    exact WeightedCurveDegree.div_le_weightedPole w
      (Sum.elim (fun _ : α => 0) b) (Sum.inr i)

variable {E : Type*} [Field E] [Algebra ℂ E]

/-- Insert a block of constant longitudinal coordinates. -/
def fibre {α β : Type*} (a : α → ℂ) (x : β → E) : α ⊕ β → E :=
  Sum.elim (fun r => algebraMap ℂ E (a r)) x

@[simp] theorem fibre_inl {α β : Type*} (a : α → ℂ) (x : β → E) (r : α) :
    fibre a x (Sum.inl r) = algebraMap ℂ E (a r) := rfl

@[simp] theorem fibre_inr {α β : Type*} (a : α → ℂ) (x : β → E) (i : β) :
    fibre a x (Sum.inr i) = x i := rfl

theorem coordinatePole_const_left {α β : Type*} [Fintype α] [Fintype β]
    (p : NormalizedPlace ℂ E) (a : α → ℂ) (w : α ⊕ β → ℚ) (x : β → E) :
    WeightedPolynomialPole.coordinatePole p.valuation (fibre a x) w =
      WeightedPolynomialPole.coordinatePole p.valuation x (fun i => w (Sum.inr i)) := by
  have he : (fun j : α ⊕ β =>
      (WeightedPolynomialPole.coordinateOrder p.valuation (fibre a x j) : ℚ)) =
      Sum.elim (fun _ : α => 0)
        (fun i => (WeightedPolynomialPole.coordinateOrder p.valuation (x i) : ℚ)) := by
    funext j
    cases j with
    | inl r => simp only [fibre_inl, CurveContactSum.coordinateOrder_constant_eq_zero,
        Int.cast_zero, Sum.elim_inl]
    | inr i => rfl
  unfold WeightedPolynomialPole.coordinatePole
  rw [he]
  exact weightedPole_zero_left w _

/-- Constant longitudinal coordinates contribute zero to weighted degree. -/
theorem weightedDegree_const_left {α β : Type*} [Fintype α] [Fintype β]
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (a : α → ℂ) (w : α ⊕ β → ℚ) (x : β → E) :
    CurveContactSum.weightedDegree hfinite (fibre a x) w =
      CurveContactSum.weightedDegree hfinite x (fun i => w (Sum.inr i)) := by
  have he : CurveContactSum.weightedPoleDivisor hfinite (fibre a x) w =
      CurveContactSum.weightedPoleDivisor hfinite x (fun i => w (Sum.inr i)) := by
    ext p
    exact coordinatePole_const_left p a w x
  unfold CurveContactSum.weightedDegree
  rw [he]

/-- Tuple injectivity suffices; separate injectivity in each longitudinal
coordinate is unnecessary, and would exclude Cartesian center grids. -/
theorem center_index_unique_of_longitudinal_constants {α β J : Type*}
    (z : α ⊕ β → E) (c : J → α ⊕ β → ℂ)
    (hc : Function.Injective (fun j => fun r : α => c j (Sum.inl r)))
    (a : α → ℂ) (ha : ∀ r, z (Sum.inl r) = algebraMap ℂ E (a r))
    (j l : J) (p q : NormalizedPlace ℂ E)
    (hp : Centered z (c j) p) (hq : Centered z (c l) q) : j = l := by
  apply hc
  funext r
  exact (hp.constant_coordinate (Sum.inl r) (a r) (ha r)).symm.trans
    (hq.constant_coordinate (Sum.inl r) (a r) (ha r))

theorem fibre_transcendental {α β : Type*} (a : α → ℂ) (x : β → E)
    (hz : ∃ j, Transcendental ℂ (fibre a x j)) :
    ∃ i, Transcendental ℂ (x i) := by
  obtain ⟨j, hj⟩ := hz
  cases j with
  | inl r => exact (hj (isAlgebraic_algebraMap (a r))).elim
  | inr i => exact ⟨i, hj⟩

theorem fibre_nonconstant {α β : Type*} (a : α → ℂ) (x : β → E)
    (c : α ⊕ β → ℂ) (hz : ∃ j, Transcendental ℂ (fibre a x j)) :
    ∃ i, x i ≠ algebraMap ℂ E (c (Sum.inr i)) :=
  Centered.exists_nonzero_difference x (fun i => c (Sum.inr i))
    (fibre_transcendental a x hz)

variable {k m : ℕ}

/-- The single-center theta discount, with the contact-to-ordinary identity
explicitly supplied by the caller. -/
theorem ordinary_contact_discount
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (a : Fin k → ℂ) (x : Fin m → E) (c : Fin m → ℂ)
    (w v : Fin k ⊕ Fin m → ℚ)
    (hw : ∀ i, 0 < w (Sum.inr i)) (hv : ∀ i, 0 < v (Sum.inr i))
    (θ : ℝ) (hratio : ∀ i, (w (Sum.inr i) : ℝ) = θ * (v (Sum.inr i) : ℝ))
    (hnc : ∃ i, x i ≠ algebraMap ℂ E (c i))
    (S : Finset (NormalizedPlace ℂ E)) (hc : ∀ p ∈ S, Centered x c p)
    (hres : ∀ p ∈ S, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (μ : NormalizedPlace ℂ E → ℝ)
    (hcontact : ∀ p (hp : p ∈ S), letI := hres p hp;
      μ p = (PlaceCenteredBranch.ordinaryContact p x c (hc p hp) hnc
        (fun i => v (Sum.inr i)) : ℝ)) :
    ∑ p ∈ S, μ p ≤ θ * CurveContactSum.weightedDegree hfinite (fibre a x) w := by
  obtain ⟨i, hi⟩ := hnc
  have hb := CoordinateContactBound.coordinate_contact_sum_le hfinite x c
    (fun i => w (Sum.inr i)) (fun i => v (Sum.inr i)) hw hv i (sub_ne_zero.mpr hi)
    S hc hres μ hcontact
  rw [hratio i] at hb
  rw [weightedDegree_const_left]
  apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < v (Sum.inr i) by exact_mod_cast hv i)).mp
  calc
    (v (Sum.inr i) : ℝ) * ∑ p ∈ S, μ p ≤
        (θ * (v (Sum.inr i) : ℝ)) *
          CurveContactSum.weightedDegree hfinite x (fun i => w (Sum.inr i)) := hb
    _ = (v (Sum.inr i) : ℝ) *
        (θ * CurveContactSum.weightedDegree hfinite x (fun i => w (Sum.inr i))) := by ring

/-- On a constant-longitudinal fibre, a center family with injective longitudinal
tuples has the theta contact discount. `hcontact` is the still-required branch
adapter: the supplied contact must equal ordinary transverse contact. -/
theorem multifibre_contact_sum_le {J : Type*}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (a : Fin k → ℂ) (x : Fin m → E) (c : J → Fin k ⊕ Fin m → ℂ)
    (hcenters : Function.Injective (fun j => fun r : Fin k => c j (Sum.inl r)))
    (hz : ∃ j, Transcendental ℂ (fibre a x j))
    (w v : Fin k ⊕ Fin m → ℚ)
    (hw : ∀ i, 0 < w (Sum.inr i)) (hv : ∀ i, 0 < v (Sum.inr i))
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hratio : ∀ i, (w (Sum.inr i) : ℝ) = θ * (v (Sum.inr i) : ℝ))
    (S : Finset (NormalizedPlace ℂ E)) (index : ∀ p, p ∈ S → J)
    (hc : ∀ p (hp : p ∈ S), Centered (fibre a x) (c (index p hp)) p)
    (hres : ∀ p ∈ S, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (μ : NormalizedPlace ℂ E → ℝ)
    (hcontact : ∀ p (hp : p ∈ S), letI := hres p hp;
      μ p = (PlaceCenteredBranch.ordinaryContact p x
        (fun i => c (index p hp) (Sum.inr i)) (fun i => hc p hp (Sum.inr i))
        (fibre_nonconstant a x (c (index p hp)) hz) (fun i => v (Sum.inr i)) : ℝ)) :
    ∑ p ∈ S, μ p ≤ θ * CurveContactSum.weightedDegree hfinite (fibre a x) w := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hS
    let j₀ := index p₀ hp₀
    have hi : ∀ p (hp : p ∈ S), index p hp = j₀ := by
      intro p hp
      exact center_index_unique_of_longitudinal_constants (fibre a x) c hcenters a
        (fun _ => rfl) (index p hp) j₀ p p₀ (hc p hp) (hc p₀ hp₀)
    have hc₀ : ∀ p ∈ S, Centered x (fun i => c j₀ (Sum.inr i)) p := by
      intro p hp i
      simpa only [hi p hp, fibre_inr] using hc p hp (Sum.inr i)
    apply ordinary_contact_discount hfinite a x (fun i => c j₀ (Sum.inr i))
      w v hw hv θ hratio (fibre_nonconstant a x (c j₀) hz) S hc₀ hres μ
    intro p hp
    let := hres p hp
    simpa only [hi p hp] using hcontact p hp
  · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hSe, Finset.sum_empty]
    exact mul_nonneg hθ (CurveContactSum.weightedDegree_nonneg hfinite (fibre a x) w)

/-- The theta discount excludes excess contact whenever the amplified theta
factor is at most one. This arithmetic conclusion does not assume positivity
of the individual contacts. -/
theorem no_excess_of_contact_discount {P : Type*} (S : Finset P) (μ : P → ℝ)
    (degree θ σ : ℝ) (hdegree : 0 ≤ degree) (hσ : 0 ≤ 1 + σ)
    (hθ : (1 + σ) * θ ≤ 1) (hdiscount : ∑ p ∈ S, μ p ≤ θ * degree) :
    ¬ degree < (1 + σ) * ∑ p ∈ S, μ p := by
  apply not_lt.mpr
  calc
    (1 + σ) * ∑ p ∈ S, μ p ≤ (1 + σ) * (θ * degree) :=
      mul_le_mul_of_nonneg_left hdiscount hσ
    _ = ((1 + σ) * θ) * degree := (mul_assoc _ _ _).symm
    _ ≤ 1 * degree := mul_le_mul_of_nonneg_right hθ hdegree
    _ = degree := one_mul degree

end
end GeneralizedLogarithms.MultifibreContact

/-- info: 'GeneralizedLogarithms.MultifibreContact.contact_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultifibreContact.contact_zero_left

/-- info: 'GeneralizedLogarithms.MultifibreContact.weightedDegree_const_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultifibreContact.weightedDegree_const_left

/-- info: 'GeneralizedLogarithms.MultifibreContact.multifibre_contact_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultifibreContact.multifibre_contact_sum_le

/-- info: 'GeneralizedLogarithms.MultifibreContact.no_excess_of_contact_discount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultifibreContact.no_excess_of_contact_discount
