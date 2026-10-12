import GeneralizedLogarithms.MultivariateFormalLogShift
import GeneralizedLogarithms.MultivariateJetProductLocalization
import LogIrrationalityMeasure.Jets.PolynomialJetPackets
import LogIrrationalityMeasure.Jets.JetPowerIdealCoprime
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Simultaneous multilogarithmic jet packets

Finite weighted packets are realized by polynomials at one center using the
triangular polynomial inverse and the formal logarithmic shift. Distinct
centers have coprime positive coordinate-power ideals, so the Chinese
remainder theorem realizes simultaneous packets. A surjective polynomial
ideal quotient map therefore supplies the same actual formal jet packets.
-/

namespace GeneralizedLogarithms.MultivariateAffineJetPackets

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open JetGeometry MultivariateLogPolynomialAdapter MultivariateFormalLogShift
open MultivariateJetProductLocalization

variable {k m : ℕ}

theorem finite_low_indices (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 < v j) (H : ℚ) :
    Finite {d : (Fin k ⊕ Fin m) →₀ ℕ // Finsupp.weight v d < H} := by
  classical
  let E : Fin (k + m) ≃ Fin k ⊕ Fin m := finSumFinEquiv.symm
  let I := {d : (Fin k ⊕ Fin m) →₀ ℕ // Finsupp.weight v d < H}
  let B := {d : Fin (k + m) →₀ ℕ // Finsupp.weight (fun j => v (E j)) d < H}
  letI : Fintype B := Fintype.ofEquiv _
    (FormalMatrixBridge.rationalJetIndexEquiv (fun j => v (E j)) (fun j => hv (E j)) H).symm
  have hw (d : (Fin k ⊕ Fin m) →₀ ℕ) :
      Finsupp.weight (fun j => v (E j))
        (Finsupp.equivFunOnFinite.symm (fun j => d (E j))) = Finsupp.weight v d := by
    simp only [Finsupp.weight_eq_sum, Finsupp.equivFunOnFinite_symm_apply_apply]
    exact E.sum_comp (fun j => d j • v j)
  let f : I → B := fun d =>
    ⟨Finsupp.equivFunOnFinite.symm (fun j => d.val (E j)), by rw [hw]; exact d.property⟩
  apply Finite.of_injective f
  intro d e h
  apply Subtype.ext
  ext j
  have hh := DFunLike.congr_fun (congrArg Subtype.val h) (E.symm j)
  simpa only [f, Finsupp.equivFunOnFinite_symm_apply_apply, Equiv.apply_symm_apply] using hh

theorem polynomial_packet_surjective {R : Type*} [CommRing R]
    (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 < v j) (H : ℚ) :
    Function.Surjective (fun P : MvPolynomial (Fin k ⊕ Fin m) R =>
      rationalCoefficientPacket v H (P : MvPowerSeries (Fin k ⊕ Fin m) R)) := by
  classical
  let I := {d : (Fin k ⊕ Fin m) →₀ ℕ // Finsupp.weight v d < H}
  letI : Finite I := finite_low_indices v hv H
  letI : Fintype I := Fintype.ofFinite I
  intro packet
  change I → R at packet
  let P : MvPolynomial (Fin k ⊕ Fin m) R := ∑ d : I, MvPolynomial.monomial d.val (packet d)
  refine ⟨P, ?_⟩
  funext d
  change MvPowerSeries.coeff d.val (P : MvPowerSeries (Fin k ⊕ Fin m) R) = packet d
  simp only [P, MvPolynomial.coeff_coe, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial, Subtype.val_inj]
  change (∑ x : I, if x = (d : I) then packet x else 0) = packet d
  exact Fintype.sum_ite_eq' (d : I) packet

theorem truncatedFormalJet_inverse (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℂ)
    (hc : ∀ r, c (Sum.inl r) ≠ 0) (T : Fin m → Fin k → ℕ)
    (P : MvPolynomial (Fin k ⊕ Fin m) ℂ) :
    truncatedFormalJet a c T
      (MultivariateCompactJetPolynomial.inverseTriangularMap c (logPolynomials a T) P) =
      (P : MvPowerSeries (Fin k ⊕ Fin m) ℂ) := by
  have h := AlgHom.congr_fun
    (MultivariateCompactJetPolynomial.triangularMap_comp_inverse c hc (logPolynomials a T)) P
  simp only [AlgHom.comp_apply, AlgHom.id_apply] at h
  simp [truncatedFormalJet, h]

theorem truncatedFormalJet_packet_surjective
    (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℂ)
    (hc : ∀ r, c (Sum.inl r) ≠ 0) (T : Fin m → Fin k → ℕ)
    (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 < v j) (H : ℚ) :
    Function.Surjective (fun P : MvPolynomial (Fin k ⊕ Fin m) ℂ =>
      rationalCoefficientPacket v H (truncatedFormalJet a c T P)) := by
  intro packet
  obtain ⟨P, hP⟩ := polynomial_packet_surjective v hv H packet
  refine ⟨MultivariateCompactJetPolynomial.inverseTriangularMap c (logPolynomials a T) P, ?_⟩
  simpa only [truncatedFormalJet_inverse a c hc] using hP

theorem formalJet_packet_surjective
    (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℂ)
    (hc : ∀ r, c (Sum.inl r) ≠ 0)
    (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 < v j) (H : ℚ) :
    Function.Surjective (fun P : MvPolynomial (Fin k ⊕ Fin m) ℂ =>
      rationalCoefficientPacket v H (MultivariateFormalJet.formalJet a c P)) := by
  let T : Fin m → Fin k → ℕ := fun i r => Nat.ceil (v (Sum.inr i) / v (Sum.inl r))
  have hT : ∀ i r, v (Sum.inr i) ≤ (T i r : ℚ) * v (Sum.inl r) :=
    fun i r => (div_le_iff₀ (hv (Sum.inl r))).mp (Nat.le_ceil _)
  let E := shiftEquiv (logarithmicTails a T) (logarithmicTails_constantCoeff a T)
  have hE : ∀ f ∈ rationalWeightedIdeal v (fun j => (hv j).le) H,
      E f ∈ rationalWeightedIdeal v (fun j => (hv j).le) H := by
    intro f hf
    exact (shiftEquiv_mem_iff _ _ v (fun j => (hv j).le)
      (logarithmicTails_mem a T v (fun j => (hv j).le) hT) H f).mpr hf
  have hs := FormalLogTruncation.packet_surjective_comp_equiv v (fun j => (hv j).le) H
    E hE (truncatedFormalJet a c T) (truncatedFormalJet_packet_surjective a c hc T v hv H)
  simpa only [E, shiftEquiv_apply, shiftMap_truncatedFormalJet] using hs

theorem logPowerIdeal_pairwise_isCoprime {J : Type*}
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (hc : Function.Injective c) (hcY : ∀ j r, c j (Sum.inl r) ≠ 0)
    (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ) (he : ∀ s, 0 < e s) :
    Pairwise (fun i j => IsCoprime (logPowerIdeal a (c i) T e) (logPowerIdeal a (c j) T e)) := by
  intro i j hij
  have hp : IsCoprime (WeightedBezout.pointIdeal (c i)) (WeightedBezout.pointIdeal (c j)) := by
    apply Ideal.isCoprime_of_isMaximal
    intro heq
    exact hij (hc (JetPowerIdealCoprime.pointIdeal_injective heq))
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.radical_eq_top.mp
  rw [Ideal.radical_sup, radical_logPowerIdeal a (c i) (hcY i) T e he,
    radical_logPowerIdeal a (c j) (hcY j) T e he, hp.sup_eq, Ideal.radical_top]

theorem logPowerIdeal_pow_pairwise_isCoprime {J : Type*}
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (hc : Function.Injective c) (hcY : ∀ j r, c j (Sum.inl r) ≠ 0)
    (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ) (he : ∀ s, 0 < e s) (n : ℕ) :
    Pairwise (fun i j => IsCoprime (logPowerIdeal a (c i) T e ^ n)
      (logPowerIdeal a (c j) T e ^ n)) := by
  intro i j hij
  exact (logPowerIdeal_pairwise_isCoprime a c hc hcY T e he hij).pow

theorem formalJet_packet_eq_of_sub_mem_pow
    (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℂ)
    (hc : ∀ r, c (Sum.inl r) ≠ 0) (T : Fin m → Fin k → ℕ)
    (e : Fin k ⊕ Fin m → ℕ) (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 ≤ v j)
    (hT : ∀ i r, v (Sum.inr i) ≤ (T i r : ℚ) * v (Sum.inl r))
    (R : ℚ) (he : ∀ j, R ≤ (e j : ℚ) * v j) (n : ℕ)
    (P Q : MvPolynomial (Fin k ⊕ Fin m) ℂ) (hPQ : P - Q ∈ logPowerIdeal a c T e ^ n) :
    rationalCoefficientPacket v (n * R) (MultivariateFormalJet.formalJet a c P) =
      rationalCoefficientPacket v (n * R) (MultivariateFormalJet.formalJet a c Q) := by
  apply (FormalLogTruncation.rationalCoefficientPacket_eq_iff v hv (n * R) _ _).mpr
  simpa only [map_sub] using formalJet_mem_weighted_of_mem_pow a c hc T e v hv hT R he n
    (P - Q) hPQ

theorem formalJet_packets_surjective {J : Type*} [Fintype J]
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (hc : Function.Injective c) (hcY : ∀ j r, c j (Sum.inl r) ≠ 0)
    (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ) (hepos : ∀ j, 0 < e j)
    (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 < v j)
    (hT : ∀ i r, v (Sum.inr i) ≤ (T i r : ℚ) * v (Sum.inl r))
    (R : ℚ) (he : ∀ j, R ≤ (e j : ℚ) * v j) (n : ℕ) :
    Function.Surjective (fun P : MvPolynomial (Fin k ⊕ Fin m) ℂ => fun j =>
      rationalCoefficientPacket v (n * R) (MultivariateFormalJet.formalJet a (c j) P)) := by
  classical
  intro packets
  choose P hP using fun j => formalJet_packet_surjective a (c j) (hcY j) v hv (n * R) (packets j)
  have hcop := logPowerIdeal_pow_pairwise_isCoprime a c hc hcY T e hepos n
  obtain ⟨Q, hQ⟩ := Ideal.exists_forall_sub_mem_ideal hcop P
  refine ⟨Q, ?_⟩
  funext j
  exact (formalJet_packet_eq_of_sub_mem_pow a (c j) (hcY j) T e v (fun s => (hv s).le)
    hT R he n Q (P j) (hQ j)).trans (hP j)

theorem polynomialIdeal_pow_le {J : Type*} [Fintype J]
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ) (n : ℕ) (j : J) :
    polynomialIdeal a c T e ^ n ≤ logPowerIdeal a (c j) T e ^ n := by
  classical
  apply pow_le_pow_left'
  exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ j))

theorem packets_surjective_of_polynomialIdeal_quotient {α J : Type*} [Fintype J]
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (hc : Function.Injective c) (hcY : ∀ j r, c j (Sum.inl r) ≠ 0)
    (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ) (hepos : ∀ j, 0 < e j)
    (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 < v j)
    (hT : ∀ i r, v (Sum.inr i) ≤ (T i r : ℚ) * v (Sum.inl r))
    (R : ℚ) (he : ∀ j, R ≤ (e j : ℚ) * v j) (n : ℕ)
    (f : α → MvPolynomial (Fin k ⊕ Fin m) ℂ)
    (hf : Function.Surjective (fun b => Ideal.Quotient.mk (polynomialIdeal a c T e ^ n) (f b))) :
    Function.Surjective (fun b j => rationalCoefficientPacket v (n * R)
      (MultivariateFormalJet.formalJet a (c j) (f b))) := by
  intro packets
  obtain ⟨P, hP⟩ := formalJet_packets_surjective a c hc hcY T e hepos v hv hT R he n packets
  obtain ⟨b, hb⟩ := hf (Ideal.Quotient.mk _ P)
  have hdiff : f b - P ∈ polynomialIdeal a c T e ^ n := Ideal.Quotient.eq.mp hb
  refine ⟨b, ?_⟩
  funext j
  exact (formalJet_packet_eq_of_sub_mem_pow a (c j) (hcY j) T e v (fun s => (hv s).le)
    hT R he n (f b) P (polynomialIdeal_pow_le a c T e n j hdiff)).trans (congrFun hP j)

end
end GeneralizedLogarithms.MultivariateAffineJetPackets

/-- info: 'GeneralizedLogarithms.MultivariateAffineJetPackets.polynomial_packet_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateAffineJetPackets.polynomial_packet_surjective

/-- info: 'GeneralizedLogarithms.MultivariateAffineJetPackets.formalJet_packet_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateAffineJetPackets.formalJet_packet_surjective

/-- info: 'GeneralizedLogarithms.MultivariateAffineJetPackets.formalJet_packets_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateAffineJetPackets.formalJet_packets_surjective

/-- info: 'GeneralizedLogarithms.MultivariateAffineJetPackets.packets_surjective_of_polynomialIdeal_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateAffineJetPackets.packets_surjective_of_polynomialIdeal_quotient
