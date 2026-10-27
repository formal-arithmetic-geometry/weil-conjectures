/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.EtaleResidueDirectImageTorWindow
import Sheaf.AlgebraicGeometry.EtaleScalarFlatModel
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import all Sheaf.Paper.FiniteCoefficientDirectImage
import all Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite-Tor direct image and change of finite coefficients

Source: blueprint main-20261015, smooth purity, reduction exceptional proof,
Locality and Charts; Bhatt--Scholze, Lemma 6.7.17 and Theorem 6.7.1
(blueprint: lem-pur-etale-finite-tor-direct-image-coefficients).

All categories are ordinary constant-ring module derived categories on small etale sites.
The scalar mate is the existing counit transpose, with its canonical projection normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
open Padic
namespace AlgebraicGeometry.Etale

-- Match the quotient-ring instance path and keep canonical derived functors abstract.
attribute [local instance 20000] CommRing.toRing
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar
  scalarMate rightDerivedLowerStarProjectionMap

private theorem bounded_of_constructible
    {A : Type (u + 1)} [CommRing A] [Finite A] {T : Scheme.{u}}
    {K : DerivedCategoryModule A T} (hK : DerivedCategory.isBoundedConstructible A T K) :
    _root_.DerivedCategory.TStructure.t.bounded K := by
  obtain ⟨_, a, b, _, hv⟩ := hK
  exact ⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).2
    (fun i hi ↦ hv i (Or.inl hi))⟩,
    ⟨b, (_root_.DerivedCategory.isLE_iff K b).2
      (fun i hi ↦ hv i (Or.inr hi))⟩⟩

private theorem scalar_constructible_tor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) [IsNoetherian T]
    (K : DerivedCategoryModule A T) (a b : ℤ) (hab : a ≤ b)
    (hK : DerivedCategory.isBoundedConstructible A T K)
    (ht : DerivedCategory.hasTorAmplitudeIn A T a b K) :
    DerivedCategory.isBoundedConstructible B T ((scalarExtension φ T).obj K) ∧
      DerivedCategory.hasTorAmplitudeIn B T a b ((scalarExtension φ T).obj K) := by
  let J : _root_.DerivedCategory.Bounded
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨K, bounded_of_constructible hK⟩
  obtain ⟨_, _, ⟨L, ⟨e⟩⟩, hc, htor⟩ :=
    exists_etaleScalarFlatModel T A B φ a b hab J hK.1 ht
  refine ⟨⟨hc, ?_⟩, htor⟩
  obtain ⟨c, hge⟩ := L.property.1
  obtain ⟨d, hle⟩ := L.property.2
  refine ⟨min c d, d, min_le_right _ _, fun i hi ↦ ?_⟩
  apply IsZero.of_iso _ ((_root_.DerivedCategory.homologyFunctor _ i).mapIso e).symm
  rcases hi with hi | hi
  · exact (_root_.DerivedCategory.isGE_iff L.obj c).1 hge i
      (lt_of_lt_of_le hi (min_le_left _ _))
  · exact (_root_.DerivedCategory.isLE_iff L.obj d).1 hle i hi

private theorem coefficient_killed
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    ((l ^ n : ℕ) : coefficientExtensionRing l E n) = 0 := by
  have h := (extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have habv : coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    calc
      coefficientExtensionAbsoluteValue l E (l : E) = ‖(l : Padic l)‖ := by
        change spectralNorm (Padic l) E (l : E) = ‖(l : Padic l)‖
        simpa only [map_natCast] using
          (spectralNorm_extends (K := Padic l) (L := E) (l : Padic l))
      _ < 1 := Padic.norm_p_lt_one
  have hlm : (l : coefficientExtensionIntegers l E) ∈
      coefficientExtensionMaximalIdeal l E :=
    (h.2.1 _).2 (by simpa only [SubringClass.coe_natCast] using habv)
  have hgen : Ideal.span ({coefficientExtensionUniformizer l E} :
      Set (coefficientExtensionIntegers l E)) = coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hpow : (l : coefficientExtensionIntegers l E) ^ n ∈
      coefficientExtensionIdeal l E n := by
    change _ ∈ Ideal.span ({coefficientExtensionUniformizer l E} :
      Set (coefficientExtensionIntegers l E)) ^ n
    rw [hgen]
    exact Ideal.pow_mem_pow hlm n
  change ((l ^ n : ℕ) :
    coefficientExtensionIntegers l E ⧸ coefficientExtensionIdeal l E n) = 0
  rw [← map_natCast (Ideal.Quotient.mk (coefficientExtensionIdeal l E n)),
    Ideal.Quotient.eq_zero_iff_mem]
  simpa only [Nat.cast_pow] using hpow

/-- Finite-type direct image over an arbitrary positive-characteristic field has a uniform
all-module-sheaf bound and preserves bounded constructible finite-Tor complexes with the
indicated interval. Finite scalar extension preserves the interval on both schemes, and the
canonical B-linear counit mate is invertible and restricts to the projection morphism.

Source: blueprint main-20261015, sec-smooth-purity, sk-lem-sp-reduction,
reduction-exceptional proof, Locality and Charts; Bhatt--Scholze Lemma 6.7.17;
Stacks 0F10(1), 0F0Z, and 0GL6
(blueprint: lem-pur-etale-finite-tor-direct-image-coefficients).

Proof:
1. The DVR and finite-quotient statements lem-weil-l-adic-extension-integers-dvr and
lem-weil-valued-dvr-finite-quotients make A finite local Noetherian. Its residue field
and every finite A-algebra are finitely presented A-modules. The extending valuation
puts ell in (t), so ell^n kills A and B and is invertible in k.
2. Apply the relative clause of lem-kun-0f10 and def-kun-cd. Every A-module sheaf is
ell^n-torsion. The canonical restriction/direct-image comparison of
lem-sbc-canonical-restrict-scalars-functor-comparisons identifies its underlying higher
direct images with the abelian ones. Exact restriction detects zero, giving c_h.
3. Apply thm-dg-finite-type-constructibility to obtain bounded constructibility of Rh_*K;
its arbitrary-field statement allows nonseparated morphisms.
4. Set L = K tensor_A^L kappa. The Tor hypothesis bounds its cohomology in [a,b].
The module-sheaf categories are Grothendieck abelian and direct image is additive left
exact by lem-weil-pbc-module-sheaves-grothendieck-abelian and
lem-weil-pbc-module-direct-image-left-exact. The spectral sequence thm-sp-truncation-e2
has E2^{r,q} = R^r h_* H^q(L), supported in [0,c_h] times [a,b]. Its finite abutment
filtration therefore gives vanishing outside [a,b+c_h].
5. The finite-constant projection formula lem-sf-projection-finite-constant identifies
Rh_*L with Rh_*K tensor_A^L kappa. Apply lem-exc-residue-tor-test to deduce the
specified full Tor interval of Rh_*K.
6. The actual scalar extension of lem-pur-derived-change-of-rings has underlying
A-complex J tensor_A^L B. Evaluating the Tor bound at B shows it is bounded without
flatness. Restriction of scalars changes no cohomology groups.
7. Finite-type schemes over a field are Noetherian. Apply
lem-weil-pbc-finite-type-over-noetherian, det-pe-finite-tor-comparison-noetherian, and
det-sp-scalar-extension-functor to obtain constructibility and the unchanged B-Tor
interval after pro-etale comparison. The adjunction of
lem-pur-sheaf-ring-derived-coefficient-adjunction and uniqueness of left adjoints
identify the actual scalar functors with those in
lem-weil-pbc-derived-scalar-extension-local-systems. Essential surjectivity of the
finite-Tor comparison supplies an etale finite-Tor object. Both it and the actual
scalar extension are bounded below by step 6. Full faithfulness in
sk-prop-sf-comparison lifts their isomorphism, giving bounded constructibility;
the interval-detection clause gives precisely the original Tor interval.
8. Apply lem-pur-etale-scalar-mate-projection: the restricted mate followed by the
canonical direct-image restriction comparison is the specified projection map.
The finite-constant projection theorem makes that map invertible. The restriction
comparison is invertible on these bounded objects. Exact restriction reflects
isomorphisms, so the B-linear mate itself is invertible. -/
theorem finiteTor_directImage_coefficients
    (p l : ℕ) (_hp : 0 < p) [Fact l.Prime] (_hlp : l ≠ p)
    (k : Type u) [Field k] [CharP k p]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (U V : Scheme.{u}) [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    (h : U ⟶ V) [h.IsOver (Spec (.of k))] :
    ∃ c : ℕ,
      (∀ (M : Sheaf U.smallEtaleTopology
          (ModuleCat.{u + 1} (coefficientExtensionRing l E n))) (q : ℕ), c < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
          (R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj M)))) ∧
      (∀ (K : DerivedCategoryModule (coefficientExtensionRing l E n) U)
        (a b : ℤ), a ≤ b →
        @DerivedCategory.isBoundedConstructible (coefficientExtensionRing l E n) _
          (finite_coefficientExtensionRing l E n hn) U K →
        DerivedCategory.hasTorAmplitudeIn (coefficientExtensionRing l E n) U a b K →
        @DerivedCategory.isBoundedConstructible (coefficientExtensionRing l E n) _
            (finite_coefficientExtensionRing l E n hn) V
            (R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).obj K) ∧
          DerivedCategory.hasTorAmplitudeIn (coefficientExtensionRing l E n) V a (b + c)
            (R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).obj K) ∧
          ∀ (B : Type (u + 1)) [CommRing B] [Finite B]
            (φ : coefficientExtensionRing l E n →+* B),
            IsIso ((scalarMate φ h).app K) ∧
              (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ).map
                  ((scalarMate φ h).app K) ≫
                  (scalarRestrictionDirectImageMap φ h).app ((scalarExtension φ U).obj K) =
                (scalarTensorIso φ V).hom.app
                    (R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).obj K) ≫
                  ((rightDerivedLowerStarProjectionMap
                    (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).app K).app
                    (scalarCoefficient φ V) ≫
                  R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).map
                    (((derivedTensor
                        (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) U).obj K).map
                        (scalarCoefficientPullbackIso φ h).hom ≫
                      (scalarTensorIso φ U).inv.app K)) ∧
      (∀ (B : Type (u + 1)) [CommRing B] [Finite B]
        (φ : coefficientExtensionRing l E n →+* B)
        (W : Scheme.{u}), (W = U ∨ W = V) →
        ∀ (J : DerivedCategoryModule (coefficientExtensionRing l E n) W)
          (r s : ℤ), r ≤ s →
          @DerivedCategory.isBoundedConstructible (coefficientExtensionRing l E n) _
            (finite_coefficientExtensionRing l E n hn) W J →
          DerivedCategory.hasTorAmplitudeIn (coefficientExtensionRing l E n) W r s J →
          DerivedCategory.isBoundedConstructible B W ((scalarExtension φ W).obj J) ∧
            DerivedCategory.hasTorAmplitudeIn B W r s ((scalarExtension φ W).obj J)) := by
  let A := coefficientExtensionRing l E n
  let : Finite A := finite_coefficientExtensionRing l E n hn
  have : IsNoetherianRing A := isNoetherian_of_finite A A
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian
    (U ↘ Spec (.of k))
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian
    (V ↘ Spec (.of k))
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace
    (U ↘ Spec (.of k))
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace
    (V ↘ Spec (.of k))
  have : IsNoetherian U := ⟨⟩
  have : IsNoetherian V := ⟨⟩
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (U ↘ Spec (.of k))
  have hcd (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ)
      (hq : 2 * d < q) : IsZero (((lowerStar (ModuleCat.{u + 1} A) h).rightDerived q).obj M) :=
    isZero_rightDerived_lowerStar_of_two_mul_lt A isAddTorsion_of_finite
      (U ↘ Spec (.of k)) (V ↘ Spec (.of k)) h (comp_over h _) d hd M q hq
  have hcd' (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ)
      (hq : 2 * d < q) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        (R(lowerStar (ModuleCat.{u + 1} A) h).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj M))) :=
    (hcd M q hq).of_iso
      ((lowerStar (ModuleCat.{u + 1} A) h).homologyRightDerivedFunctorObjSingleFunctorIso M q)
  have hlk : (l : k) ≠ 0 := by
    intro hz
    have hpl : p ∣ l := (CharP.cast_eq_zero_iff k p l).1 hz
    rcases (Nat.dvd_prime (Fact.out : l.Prime)).1 hpl with hp | hp
    · have hone : (1 : k) = 0 := by simpa only [hp, Nat.cast_one] using (CharP.cast_eq_zero k p)
      exact one_ne_zero hone
    · exact _hlp hp.symm
  have hcoeff : IsSmoothBaseChangeCoefficients (l ^ n) A (Spec (.of k)) :=
    ⟨pow_pos (Fact.out : l.Prime).pos _, inferInstance, coefficient_killed l E n, by
      simpa only [map_pow, map_natCast, Nat.cast_pow] using
        (hlk.isUnit.pow n).map (Scheme.ΓSpecIso (.of k)).inv.hom⟩
  have scalar (B : Type (u + 1)) [CommRing B] [Finite B] (φ : A →+* B)
      (W : Scheme.{u}) (hW : W = U ∨ W = V)
      (J : DerivedCategoryModule A W) (r s : ℤ) (hrs : r ≤ s)
      (hJ : DerivedCategory.isBoundedConstructible A W J)
      (ht : DerivedCategory.hasTorAmplitudeIn A W r s J) :
      DerivedCategory.isBoundedConstructible B W ((scalarExtension φ W).obj J) ∧
        DerivedCategory.hasTorAmplitudeIn B W r s ((scalarExtension φ W).obj J) := by
    have : IsNoetherian W := by rcases hW with rfl | rfl <;> infer_instance
    exact scalar_constructible_tor φ W J r s hrs hJ ht
  refine ⟨2 * d, hcd', ?_, scalar⟩
  intro K a b hab hK hTor
  have hF := isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field
    k A (l ^ n) hcoeff (U ↘ Spec (.of k)) (V ↘ Spec (.of k)) h (comp_over h _) K hK
  have htF := hasTorAmplitudeIn_rightDerivedLowerStar_of_relative_bound l E n hn h
    (2 * d) (by positivity) (fun M q hq ↦ hcd M q (by exact_mod_cast hq))
    a b hab K hK hTor hF
  refine ⟨hF, htF, ?_⟩
  intro B _ _ φ
  have hsK := scalar B φ U (Or.inl rfl) K a b hab hK hTor
  have hsF := scalar B φ V (Or.inr rfl)
    (R(lowerStar (ModuleCat.{u + 1} A) h).obj K) a (b + (2 * d : ℕ))
    (by omega) hF htF
  obtain ⟨c, hc⟩ := (bounded_of_constructible hK).1
  obtain ⟨r, hr⟩ := (bounded_of_constructible hsK.1).1
  obtain ⟨s, hs⟩ := (bounded_of_constructible hsF.1).1
  let J : _root_.DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) := ⟨K, ⟨c, hc⟩⟩
  let N : _root_.DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
    ⟨(scalarExtension φ U).obj K, ⟨r, hr⟩⟩
  let M : _root_.DerivedCategory.Plus
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
    ⟨(scalarExtension φ V).obj (R(lowerStar (ModuleCat.{u + 1} A) h).obj K), ⟨s, hs⟩⟩
  have heq := scalarMate_restrict_eq_projection φ h J ⟨N, rfl⟩ ⟨M, rfl⟩
  let BM := (ModuleCat.restrictScalars φ).obj (ModuleCat.of B B)
  have : Finite BM := inferInstanceAs (Finite B)
  have : Module.Finite A BM := Module.Finite.of_finite
  have : Module.FinitePresentation A BM := Module.finitePresentation_of_finite A BM
  obtain ⟨_, x, y, _, hv⟩ := hK
  have hp := finiteConstantProjectionComponent_isIso A h (2 * d) hcd' K
    ⟨y, fun i hi ↦ hv i (Or.inr hi)⟩ BM
  let e : scalarCoefficient φ V ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)).obj BM) :=
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso (scalarCoefficientSheafIsoConstant φ V)
  have : IsIso (((rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} A) h).app K).app (scalarCoefficient φ V)) :=
    (NatTrans.isIso_app_iff_of_iso
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) h).app K) e).2 hp
  have : K.IsGE c := hc
  have : ((scalarExtension φ U).obj K).IsGE r := hr
  refine ⟨?_, heq⟩
  exact scalarMate_isIso_of_projection (A := A) (B := B) φ h K r c

end AlgebraicGeometry.Etale
