import GeneralizedLogarithms.MultivariateJetProductLocalization
import LogIrrationalityMeasure.Jets.CompactLogJetIdeal

/-!
# The compactified multilogarithmic center ideal

The product of the polynomial center ideals extends to any suitable
compactification. Its support is exactly the finite center set, its restriction
recovers the affine ideal, and it is coherent on a locally Noetherian ambient
scheme. No ampleness or jet-surjectivity assertion is made here.
-/

namespace GeneralizedLogarithms.MultivariateCompactLogJetIdeal

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
open LogIrrationalityMeasure
open LogExponent
open MultivariateCompactJetPolynomial MultivariateLogPolynomialAdapter
open MultivariateJetProductLocalization

variable {k m : ℕ}

abbrev coordinateRing (k m : ℕ) := MvPolynomial (Fin k ⊕ Fin m) ℂ
abbrev affineSpace (k m : ℕ) : Scheme := Spec (CommRingCat.of (coordinateRing k m))
abbrev base : Scheme := Spec (CommRingCat.of ℂ)

def structureMap (k m : ℕ) : affineSpace k m ⟶ base :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (coordinateRing k m)))

def point (c : Fin k ⊕ Fin m → ℂ) : base ⟶ affineSpace k m :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval c).toRingHom)

theorem point_section (c : Fin k ⊕ Fin m → ℂ) : point c ≫ structureMap k m = 𝟙 base := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℂ (coordinateRing k m)) ≫
      CommRingCat.ofHom (MvPolynomial.aeval c).toRingHom = 𝟙 (CommRingCat.of ℂ) := by
    ext a
    simp
  rw [h, Spec.map_id]

theorem range_point (c : Fin k ⊕ Fin m → ℂ) : Set.range (point c) = {centerPoint c} := by
  change Set.range (PrimeSpectrum.comap (MvPolynomial.aeval c).toRingHom) = _
  rw [range_comap_of_surjective _ _ (by intro a; exact ⟨MvPolynomial.C a, by simp⟩)]
  exact PrimeSpectrum.zeroLocus_eq_singleton (WeightedBezout.pointIdeal c)

theorem zeroLocus_finset_prod {J : Type*} (s : Finset J)
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (hc : ∀ j r, c j (Sum.inl r) ≠ 0) (T : Fin m → Fin k → ℕ)
    (e : Fin k ⊕ Fin m → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus
        ((∏ j ∈ s, logPowerIdeal a (c j) T e : Ideal (coordinateRing k m)) : Set _) =
      (fun j => centerPoint (c j)) '' (s : Set J) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hsingle : PrimeSpectrum.zeroLocus (logPowerIdeal a (c j) T e : Set _) =
        {centerPoint (c j)} :=
      zeroLocus_powerIdeal (c j) (hc j) (logPolynomials a T)
        (logPolynomials_aeval_zero a T) e he
    rw [Finset.prod_insert hj, PrimeSpectrum.zeroLocus_mul, hsingle, ih]
    simp

theorem zeroLocus_polynomialIdeal {J : Type*} [Fintype J]
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (hc : ∀ j r, c j (Sum.inl r) ≠ 0) (T : Fin m → Fin k → ℕ)
    (e : Fin k ⊕ Fin m → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (polynomialIdeal a c T e : Set _) =
      Set.range (fun j => centerPoint (c j)) := by
  simpa only [polynomialIdeal, Finset.coe_univ, Set.image_univ] using
    zeroLocus_finset_prod Finset.univ a c hc T e he

def affineIdeal {J : Type*} [Fintype J] (a : Fin m → Fin k → ℤ)
    (c : J → Fin k ⊕ Fin m → ℂ) (T : Fin m → Fin k → ℕ)
    (e : Fin k ⊕ Fin m → ℕ) : (affineSpace k m).IdealSheafData :=
  LogExponentSeshadri.IdealPullback.specIdeal (polynomialIdeal a c T e)

theorem support_affineIdeal {J : Type*} [Fintype J]
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (hc : ∀ j r, c j (Sum.inl r) ≠ 0) (T : Fin m → Fin k → ℕ)
    (e : Fin k ⊕ Fin m → ℕ) (he : ∀ i, 0 < e i) :
    ((affineIdeal a c T e).support : Set (affineSpace k m)) =
      ⋃ j, Set.range (point (c j)) := by
  rw [affineIdeal, CompactLogJetIdeal.support_specIdeal,
    zeroLocus_polynomialIdeal a c hc T e he]
  simp only [range_point]
  ext p
  constructor
  · rintro ⟨j, rfl⟩
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_singleton _⟩
  · intro hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
    exact ⟨j, (Set.mem_singleton_iff.mp hj).symm⟩

def compactIdeal {J : Type*} [Fintype J] (a : Fin m → Fin k → ℤ)
    (c : J → Fin k ⊕ Fin m → ℂ) (T : Fin m → Fin k → ℕ)
    (e : Fin k ⊕ Fin m → ℕ) {X : Scheme} (j : affineSpace k m ⟶ X) :
    X.IdealSheafData := CompactJetIdeal.extend (affineIdeal a c T e) j

theorem restrict_compactIdeal {J : Type*} [Fintype J] (a : Fin m → Fin k → ℤ)
    (c : J → Fin k ⊕ Fin m → ℂ) (T : Fin m → Fin k → ℕ)
    (e : Fin k ⊕ Fin m → ℕ) {X : Scheme} (j : affineSpace k m ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] :
    (compactIdeal a c T e j).comap j = affineIdeal a c T e :=
  CompactJetIdeal.restrict_extend _ j

theorem support_compactIdeal {J : Type*} [Fintype J]
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (hc : ∀ j r, c j (Sum.inl r) ≠ 0) (T : Fin m → Fin k → ℕ)
    (e : Fin k ⊕ Fin m → ℕ) (he : ∀ i, 0 < e i)
    {X : Scheme} (j : affineSpace k m ⟶ X) [QuasiCompact j]
    (π : X ⟶ base) [IsSeparated π] (hπ : j ≫ π = structureMap k m) :
    ((compactIdeal a c T e j).support : Set X) =
      ⋃ b, Set.range (point (c b) ≫ j) := by
  rw [compactIdeal, CompactJetIdeal.support_extend (affineIdeal a c T e) j π
    (fun b => point (c b)) (fun b => by rw [Category.assoc, hπ, point_section])
    (support_affineIdeal a c hc T e he), support_affineIdeal a c hc T e he,
    Set.image_iUnion]
  congr 1
  funext b
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

theorem compactIdeal_isFinitePresentation {J : Type*} [Fintype J]
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ)
    {X : Scheme} [IsLocallyNoetherian X] (j : affineSpace k m ⟶ X) :
    (LogExponentSeshadri.IdealModule.closedModule (compactIdeal a c T e j)).IsFinitePresentation :=
  CompactJetIdeal.extend_isFinitePresentation _ j

end
end GeneralizedLogarithms.MultivariateCompactLogJetIdeal

/-- info: 'GeneralizedLogarithms.MultivariateCompactLogJetIdeal.support_affineIdeal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCompactLogJetIdeal.support_affineIdeal

/-- info: 'GeneralizedLogarithms.MultivariateCompactLogJetIdeal.support_compactIdeal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCompactLogJetIdeal.support_compactIdeal

/-- info: 'GeneralizedLogarithms.MultivariateCompactLogJetIdeal.compactIdeal_isFinitePresentation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCompactLogJetIdeal.compactIdeal_isFinitePresentation
