import GeneralizedLogarithms.MultivariateAffineJetPackets
import LogIrrationalityMeasure.Jets.AffineJetCoefficientInterface
import LogIrrationalityMeasure.Approximation.AdmissibleMatrixFrame
import LogIrrationalityMeasure.Approximation.WeightedGlobalSectionBound

/-!
# Geometric generation and weighted multilogarithmic packets

Surjectivity of the geometric jet restriction supplies actual multilogarithmic
packets through the affine coefficient map. An eventual weighted bound for
global sections then gives degree-controlled polynomial interpolation. The
last theorem obtains that coefficient bound for a monomial compactification.
Eventual geometric jet generation remains an explicit hypothesis; the
threshold is for the fixed geometric and center data.
-/

namespace GeneralizedLogarithms.MultivariateAffineJetFramedPackets

noncomputable section
open AlgebraicGeometry CategoryTheory Filter
open LogIrrationalityMeasure
open LogExponent
open LogExponentSeshadri.Geometry LogExponentSeshadri.IdealPullback
open AffineJetCoefficientInterface BlowupJetSurjectivity
open MultivariateJetProductLocalization

attribute [local irreducible] WeightedCompactification.lineBundle
  WeightedCompactification.affineChartMap

variable {k m : ℕ} {J : Type} [Fintype J] {X : Scheme}

theorem surjective_of_jetRestriction
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (hc : Function.Injective c) (hcY : ∀ b r, c b (Sum.inl r) ≠ 0)
    (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ) (hepos : ∀ s, 0 < e s)
    (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ s, 0 < v s)
    (hT : ∀ i r, v (Sum.inr i) ≤ (T i r : ℚ) * v (Sum.inl r))
    (R : ℚ) (he : ∀ s, R ≤ (e s : ℚ) * v s) (n : ℕ)
    (j : Spec (CommRingCat.of (MvPolynomial (Fin k ⊕ Fin m) ℂ)) ⟶ X)
    [IsOpenImmersion j] (I : X.IdealSheafData) (A : LineBundle X) (frame : Frame j A)
    (hI : I.comap j = specIdeal (polynomialIdeal a c T e))
    (hs : ((I ^ n).support : Set X) ⊆ j.opensRange)
    (hjet : Function.Surjective (jetRestriction I A n)) :
    Function.Surjective (fun s : Sections A n => fun b =>
      JetGeometry.rationalCoefficientPacket v (n * R)
        (MultivariateFormalJet.formalJet a (c b) (coefficient j A n frame s))) := by
  apply MultivariateAffineJetPackets.packets_surjective_of_polynomialIdeal_quotient
    a c hc hcY T e hepos v hv hT R he n (coefficient j A n frame)
  exact AffineJetPolynomial.polynomialQuotient_surjective_of_jetRestriction
    I A n j frame (polynomialIdeal a c T e) hI hs hjet

/-- Actual weighted-degree interpolation from two explicit geometric inputs:
eventual jet generation and eventual bounds for section coefficients. -/
theorem eventual_weighted_packets_of_eventual_jetRestriction
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (hc : Function.Injective c) (hcY : ∀ b r, c b (Sum.inl r) ≠ 0)
    (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ) (hepos : ∀ s, 0 < e s)
    (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ s, 0 < v s)
    (hT : ∀ i r, v (Sum.inr i) ≤ (T i r : ℚ) * v (Sum.inl r))
    (R : ℚ) (he : ∀ s, R ≤ (e s : ℚ) * v s)
    (j : Spec (CommRingCat.of (MvPolynomial (Fin k ⊕ Fin m) ℂ)) ⟶ X)
    [IsOpenImmersion j] (I : X.IdealSheafData) (A : LineBundle X)
    (hframe : Nonempty (Frame j A))
    (hI : I.comap j = specIdeal (polynomialIdeal a c T e))
    (hs : (I.support : Set X) ⊆ j.opensRange)
    (w : Fin k ⊕ Fin m → ℝ) (B : ℝ)
    (hdegree : ProjectiveCoefficientBound.EventualBound j A w B)
    (hjet : ∀ᶠ n : ℕ in atTop, Function.Surjective (jetRestriction I A n)) :
    ∀ᶠ n : ℕ in atTop,
      Function.Surjective (fun P : {P : MvPolynomial (Fin k ⊕ Fin m) ℂ //
          WeightedSliceDegree.SupportBound w ((n : ℝ) * B) P} => fun b =>
        JetGeometry.rationalCoefficientPacket v (n * R)
          (MultivariateFormalJet.formalJet a (c b) P.val)) := by
  obtain ⟨N, hN⟩ := hdegree
  obtain ⟨frame⟩ := hframe
  filter_upwards [hjet, eventually_ge_atTop N] with n hn hnN
  have hs' : ((I ^ n).support : Set X) ⊆ j.opensRange := by
    cases n with
    | zero => simp
    | succ n => simpa using hs
  intro packets
  obtain ⟨s, hpacket⟩ := surjective_of_jetRestriction a c hc hcY T e hepos v hv hT
    R he n j I A frame hI hs' hn packets
  exact ⟨⟨coefficient j A n frame s, hN n hnN frame s⟩, hpacket⟩

/-- For a monomial compactification the frame and weighted degree bound follow
from the original generic projective-section results. Only eventual geometric
jet generation, ideal identification and affine support remain as inputs. -/
theorem eventual_weighted_packets_of_monomial_jetRestriction {σ : Type} [Fintype σ]
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (hc : Function.Injective c) (hcY : ∀ b r, c b (Sum.inl r) ≠ 0)
    (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ) (hepos : ∀ s, 0 < e s)
    (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ s, 0 < v s)
    (hT : ∀ i r, v (Sum.inr i) ≤ (T i r : ℚ) * v (Sum.inl r))
    (R : ℚ) (he : ∀ s, R ≤ (e s : ℚ) * v s)
    (exponents : σ → (Fin k ⊕ Fin m) →₀ ℕ)
    (z : σ) (hz : exponents z = 0)
    (coordinate : (Fin k ⊕ Fin m) → σ)
    (hcoordinate : ∀ s, exponents (coordinate s) = Finsupp.single s 1)
    (w : Fin k ⊕ Fin m → ℝ) (B : ℝ)
    (hexponents : ∀ b, Finsupp.weight w (exponents b) ≤ B)
    (I : (Proj (WeightedCompactification.imageGrade (R := ℂ) exponents)).IdealSheafData)
    (hI : I.comap (WeightedCompactification.affineChartMap (R := ℂ)
      exponents z hz coordinate hcoordinate) = specIdeal (polynomialIdeal a c T e))
    (hs : (I.support : Set (Proj (WeightedCompactification.imageGrade (R := ℂ) exponents))) ⊆
      (WeightedCompactification.affineChartMap (R := ℂ)
        exponents z hz coordinate hcoordinate).opensRange)
    (hjet : ∀ᶠ n : ℕ in atTop, Function.Surjective
      (jetRestriction I (WeightedCompactification.lineBundle (R := ℂ) exponents) n)) :
    ∀ᶠ n : ℕ in atTop,
      Function.Surjective (fun P : {P : MvPolynomial (Fin k ⊕ Fin m) ℂ //
          WeightedSliceDegree.SupportBound w ((n : ℝ) * B) P} => fun b =>
        JetGeometry.rationalCoefficientPacket v (n * R)
          (MultivariateFormalJet.formalJet a (c b) P.val)) := by
  exact eventual_weighted_packets_of_eventual_jetRestriction a c hc hcY T e hepos v hv hT
    R he (WeightedCompactification.affineChartMap (R := ℂ)
      exponents z hz coordinate hcoordinate) I
    (WeightedCompactification.lineBundle (R := ℂ) exponents)
    (AdmissibleMatrixInterpolation.monomialFrame_exists (R := ℂ)
      exponents z hz coordinate hcoordinate) hI hs w B
    (WeightedGlobalSectionBound.eventual_supportBound
      exponents z hz coordinate hcoordinate w B hexponents) hjet

end
end GeneralizedLogarithms.MultivariateAffineJetFramedPackets

/-- info: 'GeneralizedLogarithms.MultivariateAffineJetFramedPackets.surjective_of_jetRestriction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateAffineJetFramedPackets.surjective_of_jetRestriction

/-- info: 'GeneralizedLogarithms.MultivariateAffineJetFramedPackets.eventual_weighted_packets_of_eventual_jetRestriction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateAffineJetFramedPackets.eventual_weighted_packets_of_eventual_jetRestriction

/-- info: 'GeneralizedLogarithms.MultivariateAffineJetFramedPackets.eventual_weighted_packets_of_monomial_jetRestriction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateAffineJetFramedPackets.eventual_weighted_packets_of_monomial_jetRestriction
