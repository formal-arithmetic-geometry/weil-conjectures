/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.SixFunctors.Coefficient.CoefficientHomTensorSquare
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteTensorCoherence
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteHomInvertible
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteEquationDescent
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomDomainCalculus
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric

/-! # Finite Hom site descent and coherence

Source: blueprint `lem-coef-finite-hom-site-descent`. The predicates and canonical
comparisons are publicly re-exported from `CoefFiniteHomSiteDescentData`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem finiteHomSupportInterval (Z : ℤ → Prop) (hf : Set.Finite {q | ¬ Z q}) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) → Z q := by
  classical
  obtain ⟨a, ha⟩ := hf.bddBelow
  obtain ⟨b, hb⟩ := hf.bddAbove
  refine ⟨min a b, max a b, min_le_max, ?_⟩
  intro q hq
  by_contra hnz
  rcases hq with hq | hq
  · exact (not_lt_of_ge (ha hnz)) (lt_of_lt_of_le hq (min_le_left _ _))
  · exact (not_lt_of_ge (hb hnz)) (lt_of_le_of_lt (le_max_right _ _) hq)

-- The Tor predicate tests all representatives; conjugating their presentation isomorphism
-- therefore transports the predicate without changing a resolution or tensor calculation.
private theorem finiteHomTorOfIso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {P Q : proEtaleDerivedCategory T A} (e : P ≅ Q) {a b : ℤ}
    (hP : HasProEtaleTorAmplitude T A P a b) : HasProEtaleTorAmplitude T A Q a b := by
  refine ⟨hP.1, ?_⟩
  intro L R hL f hf hR M i hi
  exact hP.2 L R (hL.map (fun eL ↦ eL ≪≫ e.symm)) f hf hR M i hi

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Constructible descent component of the finite Hom site descent theorem.
Source: blueprint `lem-coef-finite-hom-site-descent`, proof step 1.
(blueprint: lem-coef-finite-hom-site-descent-core-descent).

Proof: the finite-field characteristic and the structure morphism make l invertible
in every residue field. The intrinsic comparison instances give exactness. Bound the
finite cohomological support of an intrinsic constructible object and apply the
intrinsic finite-ring essential-image criterion to obtain a bounded constructible
etale witness. Its lower bound makes it bounded below, so comparison reflects each
Tor interval, giving finite Tor amplitude of the witness. Comparison preserves each
etale Tor interval as well; transport along the witness isomorphism gives the forward
implication for every witness. Apply preservation to any one interval of an arbitrary
finite-Tor etale input to obtain intrinsic constructibility and finite Tor amplitude,
and apply it separately to each specified interval for the last clause. -/
theorem coefFiniteHomSiteDescent_descent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    ∀ n : ℕ, CoefFiniteHomDescent l E X n := by
  classical
  let : EssentiallySmall.{u + 1, u, u + 1} X.ProEt :=
    essentiallySmallSelf.{0, u, u + 1} _
  have hunit : IsUnit (l : D.k) := by
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
    let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
    exact (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
      (fun h ↦ _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 h).symm)
  let residueMap (x : X) : D.k →+* X.residueField x :=
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫
      (X ↘ Spec (.of D.k)).appTop ≫ X.Γevaluation x).hom
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (map_natCast (residueMap x) l) ▸ (hunit.map (residueMap x)).invertible
  intro n
  let := HasDerivedCategory.standard (normalizedDVRModules.{u, u} l E X n)
  let B := Padic.coefficientExtensionRing l E (n + 1)
  have : Finite B := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have hplus (P' : finiteHomEtale l E X n)
      (hP' : coefFiniteHomEtaleConstructible l E X n P') :
      DerivedCategory.TStructure.t.plus P' := by
    obtain ⟨a, b, _, hz⟩ := hP'.2
    exact ⟨a, (DerivedCategory.isGE_iff P' a).mpr (fun q hq ↦ hz q (Or.inl hq))⟩
  have hpres (P' : finiteHomEtale l E X n)
      (hP' : coefFiniteHomEtaleConstructible l E X n P') (a b : ℤ) (hab : a ≤ b)
      (ht : Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1, u} B) X a b P') :=
    finiteCoefficient_comparison_preserves_torAmplitude.{u} D l _hl E (n + 1)
      (Nat.succ_pos n) X a b hab P' hP' ht
  have hrefl (P : normalizedDVRDerived.{u, u} l E X n) (P' : finiteHomEtale l E X n)
      (hP : finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X P)
      (hP' : coefFiniteHomEtaleConstructible l E X n P')
      (e : (finiteHomNu l E X n).obj P' ≅ P) (a b : ℤ)
      (ht : HasProEtaleTorAmplitude X B P a b) :=
    finiteCoefficient_comparison_reflects_torAmplitude.{u} D l _hl E (n + 1)
      (Nat.succ_pos n) X a b P' (hplus P' hP') P hP.1 ht e.symm
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro P hP
    have hbound := finiteHomSupportInterval _ hP.1.1
    obtain ⟨P', ⟨e⟩⟩ :=
      ((finiteRing_constructibleDerived_origin.{u} X B).2.2.1 P).mpr ⟨hP.1.2, hbound⟩
    obtain ⟨a, b, ht⟩ := hP.2
    exact ⟨P'.obj, ⟨P'.property, a, b, ht.1,
      hrefl P P'.obj hP P'.property e a b ht⟩, ⟨e⟩⟩
  · intro P P' hP hP' he a b hab
    let e := he.some
    exact ⟨fun ht ↦ finiteHomTorOfIso.{u} X B e (hpres P' hP' a b hab ht).2,
      hrefl P P' hP hP' e a b⟩
  · intro P' hP'
    let a := hP'.2.choose
    let b := hP'.2.choose_spec.choose
    have hab := hP'.2.choose_spec.choose_spec.1
    have ht := hP'.2.choose_spec.choose_spec.2
    have hp := hpres P' hP'.1 a b hab ht
    exact ⟨⟨hp.1, a, b, hp.2⟩, fun a b hab ht ↦ (hpres P' hP'.1 a b hab ht).2⟩

private theorem finiteHomEtaleSymmetric (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ) :
    ∃ β : @SymmetricCategory (finiteHomEtale l E X n) _
        (finiteHomEtaleClosed l E X n).monoidal,
      ∀ P Q : finiteHomEtale l E X n,
        HEq (β.toBraidedCategory.braiding P Q)
          (finiteHomKoszulIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) P Q) := by
  let R := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))
  have hc : finiteHomEtaleClosed l E X n =
      finiteHomEtaleClosedGeneral (ModuleCat.{u + 1} R) X :=
    eq_of_heq ((finiteHomEtaleData_existsUnique l E X).choose_spec.1.closed n)
  have hm : (finiteHomEtaleClosed l E X n).monoidal =
      (inferInstance : MonoidalCategory (finiteHomEtale l E X n)) := by
    rw [hc]
    exact (finiteHomEtaleClosed_existsUnique (ModuleCat.{u + 1} R) X).choose_spec.1.1
  rw [hm]
  refine ⟨DerivedCategory.symmetricCategory'
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)), ?_⟩
  intro P Q
  rfl

/-- Monoidal, symmetry, quotient, square, and transport component.
Source: blueprint `lem-coef-finite-hom-site-descent`, proof steps 2--7.
(blueprint: lem-coef-finite-hom-site-descent-core-coherence).

Proof (source steps 2--7):
1. Compute the scalar/site comparison on flat-term K-flat representatives using
algebra-diagram pullback/extension coherence. Its balancing map is inverse to the
fixed restriction mate. K-flat resolution independence descends this identification.
2. Give the etale derived tensor its Koszul symmetry and the intrinsic tensor its
ringed-derived symmetric structure. The representative normalizations identify their
fixed tensorators with pullback of the ordinary tensor map. Cochain pullback/tensor
coherence proves compatibility with associators, unitors and the signed swap.
3. Compute the tensor square and its unit square on those representatives. Both
successive scalar/site routes multiply the same scalar coefficients, proving the
quotient coherence equation for the specified adjunction mates after localization.
4. Finite Hom domain calculus keeps reductions finite-Tor constructible. The finite
duality site comparison makes the evaluation-defined site Hom maps invertible on
both the original and reduced pairs; scalar Hom invertibility is not needed.
5. Apply monoidal-square Hom transport to these four fixed functors. Its transpose
identity is the square in CoefFiniteHomSquare, with the inverse site isomorphism in
the contravariant Hom argument and the forward one in the covariant argument.
6. The same evaluation and transpose calculation carries naturality, arbitrary
transposes and internal composition across that square. Successive monoidal scalar
comparisons give the successive-quotient equation; the mate of identity restriction
gives the identity equation with normalizedOriginScalarUnit. Use the proved descent
component to choose etale witnesses of every intrinsic finite-Tor constructible pair.
Naturality conjugates these equations by their witness isomorphisms, giving the
intrinsic laws and successive equations independently of the witnesses. -/
theorem coefFiniteHomSiteDescent_coherence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    ∃ βet : ∀ n : ℕ, @SymmetricCategory (finiteHomEtale l E X n) _
        (finiteHomEtaleClosed l E X n).monoidal,
      ∃ βpro : ∀ n : ℕ, @SymmetricCategory (normalizedDVRDerived l E X n) _
          (finiteIntrinsicClosed l E X n).monoidal,
        (∀ (n : ℕ) (P Q : finiteHomEtale l E X n),
          HEq ((βet n).toBraidedCategory.braiding P Q)
            (finiteHomKoszulIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) P Q)) ∧
        (∀ n : ℕ, Nonempty (RingedDerivedTensorCoherence
          (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
          (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n) (βpro n))) ∧
        (∀ n : ℕ, CoefFiniteHomSymmetry
          (finiteHomEtaleClosed l E X n) (finiteIntrinsicClosed l E X n)
          (βet n) (βpro n) (finiteHomNu l E X n) (finiteHomNuTensor l E X n)) ∧
        ∀ (n m : ℕ) (h : m ≤ n),
          CoefFiniteHomMonoidalSquare
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
            (finiteHomEtaleReduction l E X h) (coefficientFiniteQuotientDerived l E X h)
            (finiteHomNu l E X n) (finiteHomNu l E X m)
            (finiteHomEtaleTensor l E X h) (coefFiniteHomProTensor l E X h)
            (finiteHomNuTensor l E X n) (finiteHomNuTensor l E X m)
            (coefFiniteHomSiteIso l E X h) ∧
          CoefFiniteHomSymmetry
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (βet n) (βet m) (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h) ∧
          CoefFiniteHomSymmetry
            (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
            (βpro n) (βpro m) (coefficientFiniteQuotientDerived l E X h)
            (coefFiniteHomProTensor l E X h) ∧
          CoefFiniteHomQuotientCoherence l E X h ∧ CoefFiniteHomSquare l E X h ∧
          (CoefFiniteHomLawsOn
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h)
            (finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X) →
            CoefFiniteHomLawsOn
              (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
              (coefficientFiniteQuotientDerived l E X h) (coefFiniteHomProTensor l E X h)
              (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X)) ∧
          CoefFiniteHomSuccessive l E X h := by
  classical
  choose βet hβet using fun n ↦ finiteHomEtaleSymmetric l E X n
  obtain ⟨βpro, hβpro, hν, htensor⟩ :=
    finiteHomSiteTensorCoherence D l _hl E X βet hβet
  have hmono (n m : ℕ) (h : m ≤ n) := (htensor n m h).1
  have hquot (n m : ℕ) (h : m ≤ n) := (htensor n m h).2.2.2
  have hred {n m : ℕ} (h : m ≤ n) (K : finiteHomEtale l E X n)
      (hK : finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K) :
      finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) X
        ((finiteHomEtaleReduction l E X h).obj K) := by
    obtain ⟨a, b, hab, hTor⟩ := hK.2
    have hmodel := finiteHomDomain_flatModel D l _hl E X h a b hab K hK.1 hTor
    exact ⟨hmodel.2.2.1, a, b, hab, hmodel.2.2.2⟩
  have hsquare (n m : ℕ) (h : m ≤ n) : CoefFiniteHomSquare l E X h := by
    intro K M hK hM
    have hKr := hred h K hK
    have hMr := hred h M hM
    refine ⟨finiteHomSiteHomInvertible D l _hl E X n K M hK hM.1,
      finiteHomSiteHomInvertible D l _hl E X m _ _ hKr hMr.1, ?_⟩
    obtain ⟨sF, sG, sU, sV, ht, _⟩ := hmono n m h
    exact coefficientHomTensorSquare
      (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
      (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
      (finiteHomEtaleReduction l E X h) (coefficientFiniteQuotientDerived l E X h)
      (finiteHomNu l E X n) (finiteHomNu l E X m)
      (finiteHomEtaleTensor l E X h) (coefFiniteHomProTensor l E X h)
      (finiteHomNuTensor l E X n) (finiteHomNuTensor l E X m)
      (coefFiniteHomSiteIso l E X h) ht K M
  have hlaws := finiteHomSiteEquationDescent D l _hl E X
    (coefFiniteHomSiteDescent_descent D l _hl E X) hsquare hmono hquot
  refine ⟨βet, βpro, hβet, hβpro, hν, ?_⟩
  intro n m h
  exact ⟨hmono n m h, (htensor n m h).2.1, (htensor n m h).2.2.1,
    hquot n m h, hsquare n m h, (hlaws n m h).1, (hlaws n m h).2⟩

/-- Finite-Tor constructible descent and the canonical scalar/site Hom square.
Source: blueprint thm-coef-finite-hom, final paragraph and final sentence
(blueprint: lem-coef-finite-hom-site-descent).

Proof (the node's seven steps):
1. Exact comparison identifies constant rings (lem-sf-comparison-pullback-exact).
Constructible origin supplies an etale witness. Comparison Tor-amplitude reflection
applies because that witness is bounded below; preservation and reflection identify
all ordered Tor intervals for every witness (lem-sf-proetale-constructible-origin,
lem-sf-comparison-tor-amplitude).
2. The terminal-diagram case of lem-pur-algebra-diagram-pullback-extension-coherence
constructs the scalar/site isomorphism. On flat-term K-flat resolutions its map is
inverse image of x tensor b mapped to the tensor of the inverse image of x and b.
K-flat resolutions, ringed pullback preservation and derived-pullback computation
identify this with the inverse of the fixed restriction mate.
3. The ringed-derived closed symmetric monoidal theorem supplies the four ambient
structures. Canonical tensor pullback and its shift/unit normalization identify their
comparisons with the cochain maps of lem-pur-cochain-pullback-tensor-coherence.
These respect associators, unitors and signed symmetry even for nonflat quotients.
4. The cochain scalar-association equation proves monoidality of h; the unit sends
one to one. Both successive routes send (x tensor b) tensor c to the inverse image
of x tensor the image of b times c. Localization preserves these equations.
5. Finite Hom domain calculus puts reductions in the finite-Tor constructible domain.
The finite-duality site comparison makes the specified evaluation-defined beta maps
invertible, both before and after reduction. This uses no invertibility of v.
6. Apply lem-coef-monoidal-square-hom-transport to the four functors and the monoidal h.
Its transpose equation is exactly the displayed square; Hom uses h inverse in its
contravariant input and h in its covariant input.
7. Assuming the corresponding etale equations, that same categorical transport carries
naturality, evaluation, arbitrary transposes, internal composition, identities and successive
quotients to the intrinsic equations. The etale identity uses normalizedOriginScalarUnit,
the adjunction mate of identity restriction. Every intrinsic
finite-Tor constructible pair has etale witnesses by step 1; naturality conjugates the
equations by the witness isomorphisms, independently of their choice. -/
theorem coefFiniteHomSiteDescent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    (∀ n : ℕ, CoefFiniteHomDescent l E X n) ∧
    ∃ βet : ∀ n : ℕ, @SymmetricCategory (finiteHomEtale l E X n) _
        (finiteHomEtaleClosed l E X n).monoidal,
      ∃ βpro : ∀ n : ℕ, @SymmetricCategory (normalizedDVRDerived l E X n) _
          (finiteIntrinsicClosed l E X n).monoidal,
        (∀ (n : ℕ) (P Q : finiteHomEtale l E X n),
          HEq ((βet n).toBraidedCategory.braiding P Q)
            (finiteHomKoszulIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) P Q)) ∧
        (∀ n : ℕ, Nonempty (RingedDerivedTensorCoherence
          (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
          (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n) (βpro n))) ∧
        (∀ n : ℕ, CoefFiniteHomSymmetry
          (finiteHomEtaleClosed l E X n) (finiteIntrinsicClosed l E X n)
          (βet n) (βpro n) (finiteHomNu l E X n) (finiteHomNuTensor l E X n)) ∧
        ∀ (n m : ℕ) (h : m ≤ n),
          CoefFiniteHomMonoidalSquare
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
            (finiteHomEtaleReduction l E X h) (coefficientFiniteQuotientDerived l E X h)
            (finiteHomNu l E X n) (finiteHomNu l E X m)
            (finiteHomEtaleTensor l E X h) (coefFiniteHomProTensor l E X h)
            (finiteHomNuTensor l E X n) (finiteHomNuTensor l E X m)
            (coefFiniteHomSiteIso l E X h) ∧
          CoefFiniteHomSymmetry
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (βet n) (βet m) (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h) ∧
          CoefFiniteHomSymmetry
            (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
            (βpro n) (βpro m) (coefficientFiniteQuotientDerived l E X h)
            (coefFiniteHomProTensor l E X h) ∧
          CoefFiniteHomQuotientCoherence l E X h ∧ CoefFiniteHomSquare l E X h ∧
          (CoefFiniteHomLawsOn
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h)
            (finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X) →
            CoefFiniteHomLawsOn
              (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
              (coefficientFiniteQuotientDerived l E X h) (coefFiniteHomProTensor l E X h)
              (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X)) ∧
          CoefFiniteHomSuccessive l E X h := by
  exact ⟨coefFiniteHomSiteDescent_descent D l _hl E X,
    coefFiniteHomSiteDescent_coherence D l _hl E X⟩

end WeilConjectures
