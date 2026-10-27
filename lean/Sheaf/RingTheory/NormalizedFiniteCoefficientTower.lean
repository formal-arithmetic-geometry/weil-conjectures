module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Normalization in a finite coefficient-field tower

Source: Stacks Project, Tags 09EM, 09ES and 0307
(blueprint: lem-sfb-normalized-finite-coefficient-tower).
-/

@[expose] public section

set_option autoImplicit false

universe uA uB uK uL uH uN

open scoped TensorProduct

namespace NormalizedCoefficientTower

/-- The reduced coefficient tensor is the tensor product modulo all nilpotents.
Source: Stacks Project, Tags 09EM and 09ES
(blueprint: lem-sfb-normalized-finite-coefficient-tower). -/
abbrev reducedTensor (K : Type uK) (L : Type uL) (P : Type uH)
    [CommRing K] [CommRing L] [CommRing P] [Algebra K L] [Algebra K P] :=
  (L ⊗[K] P) ⧸ nilradical (L ⊗[K] P)

/-- The canonical left structural map into the reduced tensor.
Source: Stacks Project, Tag 09EM
(blueprint: lem-sfb-normalized-finite-coefficient-tower). -/
def left (K : Type uK) (L : Type uL) (P : Type uH)
    [CommRing K] [CommRing L] [CommRing P] [Algebra K L] [Algebra K P] :
    L →+* reducedTensor K L P :=
  (Ideal.Quotient.mk (nilradical (L ⊗[K] P))).comp
    (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] P).toRingHom

/-- The canonical right structural map into the reduced tensor.
Source: Stacks Project, Tag 09EM
(blueprint: lem-sfb-normalized-finite-coefficient-tower). -/
def right (K : Type uK) (L : Type uL) (P : Type uH)
    [CommRing K] [CommRing L] [CommRing P] [Algebra K L] [Algebra K P] :
    P →+* reducedTensor K L P :=
  (Ideal.Quotient.mk (nilradical (L ⊗[K] P))).comp
    Algebra.TensorProduct.includeRight.toRingHom

/-- Normalized local branches commute with a finite coefficient-field tower.

Source: Stacks Project, Tags 09EM, 09ES and 0307
(blueprint: lem-sfb-normalized-finite-coefficient-tower).

Proof:
1. Apply lem-sfb-dvr-algebraic-normalization-structure to H and N; products of
   finite bases show N/K finite. The finite-extension integral-closure fraction-field
   lemma gives fraction field H for the lower branch, unchanged by localization.
2. Tensor universality identifies (L tensor_K H) tensor_H N with L tensor_K N.
   The field-extension tensor-injectivity lemma makes the transition injective.
   An injective map reflects nilpotence, so reduction preserves this injection.
   Map monic equations to restrict it to the integral closures.
3. Original monic equations give integrality of both transitions. Integral transitivity
   (lem-sfb-integral-element-tower-descent) identifies normalization over R_H and C_H
   with R_N and C_N respectively, without asserting E_N integral over C_H.
4. Integral injective lying-over and prime-over-maximal-is-maximal give maximal Q over q.
5. The tensor universal property and quotient surjectivity identify E_N with the reduction
   of E_H tensor_H N: maps both ways fix L and N, hence are inverse.
6. Write E_H as a finite product of finite extensions F_i of L. Its integral closure is
   the product of their integral closures D_i (multiply their monic equations).
   Exactly one orthogonal idempotent avoids q, so product-prime localization selects D_i.
   The finite-extension fraction-field lemma gives Frac(D_i) = F_i. Thus localization
   of E_H at C_H minus q is the branch fraction field L_q, compatibly with H.
7. Apply integral-closure-commutes-localization to R_H -> N. All nonzero denominators
   are already units in N, giving the lower comparison with fraction formula r/v.
8. The iterated reduced-tensor identification localizes to the reduction of L_q tensor_H N.
   Its maps are determined by pure tensors and inverse denominators. A localization of
   a reduced ring is reduced: if (x/s)^d=0, some t has tx^d=0, hence (tx)^d=0 and tx=0.
9. Apply integral-closure-commutes-localization to C_H -> E_N and use step 8 for
   the upper comparison. This kills the other generic factors rather than assuming
   E_H a field.
10. For Q over q, m = Q intersect R_N contracts to n. The extended ideals in both
    intermediate localizations are maximal, as their quotients are the corresponding
    residue fields. Localizing again gives (R_N)_m and (C_N)_Q by inverse fraction
    formulas (r/v)/(t/w) -> rw/(vt) and r/t -> (r/1)/(t/1).
11. Every square commutes on original ring elements, pure tensors and inverse
    denominators; these generate all the rings concerned. No completeness,
    separability, module-finiteness of normalization or perfect residue field is used.
-/
theorem normalized_finite_coefficient_tower
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    (H : Type uH) (N : Type uN)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field H] [Field N]
    [Algebra A B] [Algebra A K] [Algebra B L] [Algebra A L] [Algebra K L]
    [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra K H] [Algebra H N] [Algebra K N] [IsScalarTower K H N]
    [Algebra A H] [Algebra A N] [IsScalarTower A K H] [IsScalarTower A K N]
    [IsScalarTower A H N] [FiniteDimensional K H] [FiniteDimensional H N]
    (hinj : Function.Injective (algebraMap A B))
    (hlocal : (IsLocalRing.maximalIdeal B).comap (algebraMap A B) =
      IsLocalRing.maximalIdeal A) :
    ∃ (e : reducedTensor K L H →+* reducedTensor K L N)
      (c : integralClosure B (reducedTensor K L H) →+*
        integralClosure B (reducedTensor K L N))
      (iH : integralClosure A H →+* integralClosure B (reducedTensor K L H))
      (iN : integralClosure A N →+* integralClosure B (reducedTensor K L N)),
    (∀ (l : L) (h : H), e (left K L H l * right K L H h) =
      left K L N l * right K L N (algebraMap H N h)) ∧
    (∀ x : integralClosure B (reducedTensor K L H), (c x).val = e x.val) ∧
    (∀ x : integralClosure A H, (iH x).val = right K L H x.val) ∧
    (∀ x : integralClosure A N, (iN x).val = right K L N x.val) ∧
    Function.Injective (IsScalarTower.toAlgHom A H N).mapIntegralClosure ∧
    (IsScalarTower.toAlgHom A H N).mapIntegralClosure.toRingHom.IsIntegral ∧
    Function.Injective c ∧ c.IsIntegral ∧
    (∀ x : integralClosure A H,
      c (iH x) = iN ((IsScalarTower.toAlgHom A H N).mapIntegralClosure x)) ∧
    (∀ q : MaximalSpectrum (integralClosure B (reducedTensor K L H)),
      ∃ Q : MaximalSpectrum (integralClosure B (reducedTensor K L N)),
        Q.asIdeal.comap c = q.asIdeal) ∧
    ∀ q : MaximalSpectrum (integralClosure B (reducedTensor K L H)),
    (q.asIdeal.comap iH).IsMaximal ∧
    ∀ (Aq : Type uH) (Bq : Type (max uL uH)) [CommRing Aq] [CommRing Bq]
      (a : integralClosure A H →+* Aq)
      (b : integralClosure B (reducedTensor K L H) →+* Bq),
    (q.asIdeal.comap iH).primeCompl.IsLocalizationMap a →
    q.asIdeal.primeCompl.IsLocalizationMap b →
    ∃ (_hA : IsDomain Aq) (_hB : IsDomain Bq),
    IsDiscreteValuationRing Aq ∧ IsDiscreteValuationRing Bq ∧
    ∃ (α : Aq →+* H),
    (∀ x : integralClosure A H, α (a x) = x.val) ∧
    (nonZeroDivisors Aq).IsLocalizationMap α ∧
    ∀ (Lq : Type (max uL uH)) [Field Lq] (β : Bq →+* Lq),
    (nonZeroDivisors Bq).IsLocalizationMap β →
    ∃ (_aHL : Algebra H Lq) (αN : Aq →+* N)
      (ab : Aq →+* Bq) (s : reducedTensor K L H →+* Lq)
      (j : reducedTensor K L N →+* reducedTensor H Lq N),
    (∀ x : Aq, αN x = algebraMap H N (α x)) ∧
    (∀ x : integralClosure A H, ab (a x) = b (iH x)) ∧
    (∀ x : Aq, β (ab x) = algebraMap H Lq (α x)) ∧
    (∀ x : integralClosure B (reducedTensor K L H), s x.val = β (b x)) ∧
    (∀ h : H, s (right K L H h) = algebraMap H Lq h) ∧
    (∀ (l : L) (z : N), j (left K L N l * right K L N z) =
      left H Lq N (s (left K L H l)) * right H Lq N z) ∧
    ∀ (Rloc : Type uN) (Cloc : Type (max uL uN)) [CommRing Rloc] [CommRing Cloc]
      (r : integralClosure A N →+* Rloc)
      (d : integralClosure B (reducedTensor K L N) →+* Cloc),
    ((q.asIdeal.comap iH).primeCompl.map
      (IsScalarTower.toAlgHom A H N).mapIntegralClosure.toRingHom.toMonoidHom).IsLocalizationMap r →
    (q.asIdeal.primeCompl.map c.toMonoidHom).IsLocalizationMap d →
    ∃ (ρ : Rloc →+* N) (σ : Cloc →+* reducedTensor H Lq N)
      (δ : Rloc →+* Cloc),
    Function.Injective ρ ∧ Function.Injective σ ∧
    (∀ x : integralClosure A N, ρ (r x) = x.val) ∧
    (∀ x : integralClosure B (reducedTensor K L N), σ (d x) = j x.val) ∧
    ρ.range = (@Subalgebra.toSubring Aq N _ _ αN.toAlgebra
      (@integralClosure Aq N _ _ αN.toAlgebra)) ∧
    σ.range = (@Subalgebra.toSubring Bq (reducedTensor H Lq N) _ _
      ((left H Lq N).comp β).toAlgebra
      (@integralClosure Bq (reducedTensor H Lq N) _ _
        ((left H Lq N).comp β).toAlgebra)) ∧
    (∀ x : integralClosure A N, δ (r x) = d (iN x)) ∧
    (∀ x : Rloc, σ (δ x) = right H Lq N (ρ x)) ∧
    ∀ Q : MaximalSpectrum (integralClosure B (reducedTensor K L N)),
    Q.asIdeal.comap c = q.asIdeal →
    (Q.asIdeal.comap iN).IsMaximal ∧
    ∃ (_hm : ((Q.asIdeal.comap iN).map r).IsMaximal)
      (_hQ : (Q.asIdeal.map d).IsMaximal)
      (_hDA : IsDomain (Localization.AtPrime (Q.asIdeal.comap iN)))
      (_hDB : IsDomain (Localization.AtPrime Q.asIdeal)),
    IsDiscreteValuationRing (Localization.AtPrime (Q.asIdeal.comap iN)) ∧
    IsDiscreteValuationRing (Localization.AtPrime Q.asIdeal) ∧
    ∃ (a' : Rloc →+* Localization.AtPrime (Q.asIdeal.comap iN))
      (b' : Cloc →+* Localization.AtPrime Q.asIdeal)
      (ab' : Localization.AtPrime (Q.asIdeal.comap iN) →+*
        Localization.AtPrime Q.asIdeal),
    ((Q.asIdeal.comap iN).map r).primeCompl.IsLocalizationMap a' ∧
    (Q.asIdeal.map d).primeCompl.IsLocalizationMap b' ∧
    (∀ x : integralClosure A N,
      a' (r x) = algebraMap _ (Localization.AtPrime (Q.asIdeal.comap iN)) x) ∧
    (∀ x : integralClosure B (reducedTensor K L N),
      b' (d x) = algebraMap _ (Localization.AtPrime Q.asIdeal) x) ∧
    (∀ x : integralClosure A N,
      ab' (algebraMap _ (Localization.AtPrime (Q.asIdeal.comap iN)) x) =
        algebraMap _ (Localization.AtPrime Q.asIdeal) (iN x)) ∧
    (∀ x : Rloc, ab' (a' x) = b' (δ x)) := by
  sorry

end NormalizedCoefficientTower
