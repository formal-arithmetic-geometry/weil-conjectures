/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.Paper.AdmissibleLattices
public import Sheaf.Paper.SbcCompletedOperations
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.AdicSmoothBaseChange
import Mathlib.GroupTheory.PGroup
import all Sheaf.Paper.PbcFinitePullbackConstructibility
import all Sheaf.Paper.BoundedConstructibleComplete
import all Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import all Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalObjectComparison
import Sheaf.AlgebraicGeometry.FiniteCoefficientRealizationDirectImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-! # Smooth base change with finite-extension rational coefficients
Source: blueprint, sec-smooth-base-change/sk-rem-rest, order 1445
(blueprint: sbc-thm-e-coefficient-smooth-base-change).
The exchange lives in the raw rationalization of the ambient complete category.
Constructible landing is represented through the fully faithful integral inclusion
and the specified lattice presentation. It makes no integral constructibility claim
about an arbitrary representative merely rationally isomorphic to a constructible one.

## Main statements

- `sbcRationalExchange`: the localized canonical integral mate.
- `sbcTransportedExchange`: transport along a specified presentation.
- `eCoefficientSmoothBaseChange`: invertibility, independence and constructible landing.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (sq : ChosenCartesianSquare h e f g)

/-- The scalar localization of the left integral composite, on all complete complexes.
Equivalently this is successive rational direct image and rational completed pullback:
both send a tensor r tensor a to r tensor P_f(D_g(a)).
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcRationalLeft : PbcRationalComplete l E T ⥤ PbcRationalComplete l E X :=
  ScalarLocalization.between (PbcIntegralRing l E)
    (pbcUniformizer l E) (sbcPush l E g ⋙ sbcPull l E f)

/-- The scalar localization of the right integral composite, without constructibility
assumptions on its outputs. Source: blueprint order 1445
(blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcRationalRight : PbcRationalComplete l E T ⥤ PbcRationalComplete l E X :=
  ScalarLocalization.between (PbcIntegralRing l E)
    (pbcUniformizer l E) (sbcPull l E e ⋙ sbcPush l E h)

/-- Rational exchange is exactly scalar localization of the specified integral mate.
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcRationalExchange : sbcRationalLeft l E (f := f) (g := g) ⟶
    sbcRationalRight l E (e := e) (h := h) :=
  ScalarLocalization.betweenNat (PbcIntegralRing l E)
    (pbcUniformizer l E) (sbcExchange l E sq)

/-- Localize an ambient integral complete complex by the same raw construction.
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
abbrev sbcCompleteRationalize (W : Scheme.{u}) :=
  ScalarLocalization.localization (PbcIntegralRing l E)
    (PbcComplete l E W) (pbcUniformizer l E)

/-- Transport of the lattice exchange along the specified rational presentation.
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcTransportedExchange [IsNoetherian T]
    (hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (hlT : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) {K : PbcRationalConstructible l E T}
    (L : IntegralLattice l E T hT hlT K) :
    (sbcRationalLeft l E (f := f) (g := g)).obj ((pbcRationalInclusion l E T).obj K) ⟶
      (sbcRationalRight l E (e := e) (h := h)).obj ((pbcRationalInclusion l E T).obj K) :=
  (sbcRationalLeft l E (f := f) (g := g)).map
      ((pbcRationalInclusion l E T).map L.rationalization.inv) ≫
    (sbcRationalExchange l E sq).app
      ((sbcCompleteRationalize l E T).obj ((pbcConstructibleInclusion l E T).obj L.integral)) ≫
    (sbcRationalRight l E (e := e) (h := h)).map
      ((pbcRationalInclusion l E T).map L.rationalization.hom)

/-- Constructible landing means a constructible rational isomorphism representing the
ambient exchange, with the endpoints identified using this lattice presentation.
The integral endpoint identifications precede rationalization, so an arbitrary rational
representative is never inferred to have a constructible integral model.
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def SbcConstructibleExchangeRepresentation [IsNoetherian T]
    (hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (hlT : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) {K : PbcRationalConstructible l E T}
    (L : IntegralLattice l E T hT hlT K) : Prop :=
  ∃ (J J' : PbcIntegralConstructible l E X)
    (a : (pbcConstructibleInclusion l E X).obj J ≅
      (sbcPull l E f).obj ((sbcPush l E g).obj
        ((pbcConstructibleInclusion l E T).obj L.integral)))
    (b : (pbcConstructibleInclusion l E X).obj J' ≅
      (sbcPush l E h).obj ((sbcPull l E e).obj
        ((pbcConstructibleInclusion l E T).obj L.integral)))
    (β : (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj J ≅
      (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj J'),
    (pbcRationalInclusion l E X).map β.hom ≫
        ((sbcCompleteRationalize l E X).mapIso b ≪≫
          (sbcRationalRight l E (e := e) (h := h)).mapIso
            ((pbcRationalInclusion l E T).mapIso L.rationalization)).hom =
      ((sbcCompleteRationalize l E X).mapIso a ≪≫
        (sbcRationalLeft l E (f := f) (g := g)).mapIso
          ((pbcRationalInclusion l E T).mapIso L.rationalization)).hom ≫
        (sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)

set_option linter.unusedSectionVars false in
/-- Pulling an invertible global integer back to every stalk preserves invertibility.
Source: blueprint order 1445, invertibility on every corner in proof step 1
(blueprint: sbc-thm-e-coefficient-smooth-base-change).
Proof: map the global section through q.appTop and the global-to-stalk germ. Ring maps
preserve units and natural-number casts. This also handles an empty source scheme. -/
theorem sbcPrimeUnitOnSource {U V : Scheme.{u}} (q : U ⟶ V)
    (_hl : IsUnit (l : Γ(V, ⊤))) : ∀ t : U, IsUnit (l : U.presheaf.stalk t) := by
  intro t
  simpa using (_hl.map q.appTop.hom).map (U.presheaf.Γgerm t).hom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem transportedExchange_eq [IsNoetherian T]
    (hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (hlT : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) {K : PbcRationalConstructible l E T}
    (L : IntegralLattice l E T hT hlT K) :
    sbcTransportedExchange l E sq hT hlT L =
      (sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K) := by
  change (sbcRationalLeft l E (f := f) (g := g)).map
      ((pbcRationalInclusion l E T).map L.rationalization.inv) ≫
    (sbcRationalExchange l E sq).app
      ((pbcRationalInclusion l E T).obj
        ((pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj
          L.integral)) ≫
    (sbcRationalRight l E (e := e) (h := h)).map
      ((pbcRationalInclusion l E T).map L.rationalization.hom) = _
  rw [← NatTrans.naturality, ← Functor.map_comp_assoc, ← Functor.map_comp]
  simp

private theorem quotientOrderUnit {R : Type*} [CommRing R] (hl : IsUnit (l : R))
    (n : ℕ) :
    IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : R) := by
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hlmem : (l : Padic.coefficientExtensionIntegers l E) ∈
      Ideal.span {Padic.coefficientExtensionUniformizer l E} := by
    rw [hgen]
    apply (h.2.1 _).mpr
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E) l, spectralNorm_extends]
    exact Padic.norm_p_lt_one
  have hlmem' : (l : PbcIntegralRing l E) ∈ (pbcIntegralDatum l E).ideal := by
    change (l : PbcIntegralRing l E) ∈ Ideal.span {pbcUniformizer l E}
    rw [Ideal.mem_span_singleton] at hlmem ⊢
    exact map_dvd ULift.ringEquiv.symm hlmem
  let Q := ProEtale.PbcQuotient (pbcIntegralDatum l E) n
  have hz : (l : Q) ^ (n + 1) = 0 := by
    change (Ideal.Quotient.mk ((pbcIntegralDatum l E).ideal ^ (n + 1))
      (l : PbcIntegralRing l E)) ^ (n + 1) = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hlmem' (n + 1)
  have hp : IsPGroup l (Multiplicative Q) := by
    intro x
    refine ⟨n + 1, ?_⟩
    change (l ^ (n + 1)) • Multiplicative.toAdd x = 0
    rw [nsmul_eq_mul, Nat.cast_pow, hz, zero_mul]
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hcard : Nat.card Q = l ^ k := hk
  rw [hcard, Nat.cast_pow]
  exact hl.pow k

private def scalarRealization (W : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  pbcAssociatedModule W A (adicLisseRing W A) (adicLisseConstantUnit W A)

private local instance scalarRealization_equiv (W : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (scalarRealization W A).IsEquivalence :=
  ProEtale.coefficientRealization_isEquivalence (ProEt.topology W) A _ _

private def scalarRealizationUnit (W : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    𝟭 (Sheaf (ProEt.topology W) (ModuleCat.{u + 1} A)) ≅
      scalarRealization W A ⋙ scalarRestriction W A := by
  let D := scalarEmbedding W A
  let η := Functor.whiskerLeft D
    (PresheafOfModules.sheafificationAdjunction (adicLisseConstantUnit W A)).unit
  have hη : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro F
    dsimp only [η, Functor.whiskerLeft_app]
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology W)
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj F).property
  exact Functor.fullyFaithfulCancelRight D (asIso η)

private theorem levelScalarSquare (W : Scheme.{u}) (n : ℕ) :
    adicLisseConstantUnit W (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) ≫
      ((adicLisseForget W).map
        (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom).hom =
      pbcFunctionScalars W (pbcIntegralDatum l E) n := by
  rw [functionScalars_eq]
  ext U b
  exact (pbcLevelConstantComparison_exists W (pbcIntegralDatum l E) n).exists.choose_spec U b

private def realizationConstant (W : Scheme.{u}) (n : ℕ) :
    pbcFunctionRealization W (pbcIntegralDatum l E) n ⋙
      pbcRestrict (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom ≅
    scalarRealization W (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) := by
  let P := ProEtale.PbcQuotient (pbcIntegralDatum l E) n
  have h := pbcAssociatedRestriction_exists W P P
    (adicLisseRing W P)
    ((adicLisseForget W).obj ((pbcAdicRings W (pbcIntegralDatum l E)).obj (op n)))
    (adicLisseConstantUnit W P) (pbcFunctionScalars W (pbcIntegralDatum l E) n)
    (RingHom.id P)
    ((adicLisseForget W).map (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom)
    (by simpa using levelScalarSquare l E W n)
  exact h.exists.choose.symm

private local instance scalarRestriction_additive (W : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] : (scalarRestriction W A).Additive :=
  Functor.additive_of_preserves_binary_products _

private local instance scalarRealization_additive (W : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] : (scalarRealization W A).Additive :=
  Functor.additive_of_preserves_binary_products _

private def finiteEncoding (W : Scheme.{u}) (n : ℕ) :=
  pbcRestrict (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom ⋙
    scalarRestriction W (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)

private local instance finiteEncoding_equiv (W : Scheme.{u}) (n : ℕ) :
    (finiteEncoding l E W n).IsEquivalence := by
  have : (pbcRestrict (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom).IsEquivalence :=
    inferInstanceAs (proEtaleScalarEquivalence W ((adicLisseForget W).mapIso
      (pbcLevelConstantComparison W (pbcIntegralDatum l E) n))).functor.IsEquivalence
  unfold finiteEncoding
  infer_instance

private local instance finiteEncoding_additive (W : Scheme.{u}) (n : ℕ) :
    (finiteEncoding l E W n).Additive := by unfold finiteEncoding; infer_instance

private def finiteEncodingUnit (W : Scheme.{u}) (n : ℕ) :
    pbcFunctionRealization W (pbcIntegralDatum l E) n ⋙ finiteEncoding l E W n ≅ 𝟭 _ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (realizationConstant l E W n) _ ≪≫
    (scalarRealizationUnit W _).symm

private def finiteDerivedEncodingUnit (W : Scheme.{u}) (n : ℕ) :
    pbcDerivedFunctionRealization W (pbcIntegralDatum l E) n ⋙
      (finiteEncoding l E W n).mapDerivedCategory ≅ 𝟭 _ :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (finiteEncodingUnit l E W n) ≪≫
    Functor.mapDerivedCategoryIdIso _

private theorem levelCoefficientSquare {U V : Scheme.{u}} (q : U ⟶ V) (n : ℕ) :
    (constantCoefficients q (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)).hom ≫
      (pbcLevelConstantComparison U (pbcIntegralDatum l E) n).hom =
    (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map
      (pbcLevelConstantComparison V (pbcIntegralDatum l E) n).hom ≫
        completedFiniteCoefficientMap q (pbcIntegralDatum l E) n := by
  simp only [constantCoefficients, asIso_hom, completedFiniteCoefficientMap,
    ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
  rw [(proEtaleSheafInverseImage q CommRingCat.{u + 1}).map_id, Category.id_comp]
  rfl

private def finitePullEncoding {U V : Scheme.{u}} (q : U ⟶ V) (n : ℕ) :
    sbcFinitePull l E q n ⋙ (finiteEncoding l E U n).mapDerivedCategory ≅
      (finiteEncoding l E V n).mapDerivedCategory ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1}
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) q).mapDerivedCategory := by
  let P := ProEtale.PbcQuotient (pbcIntegralDatum l E) n
  let Rc := pbcRestrict (pbcLevelConstantComparison U (pbcIntegralDatum l E) n).hom
  let Rv := pbcRestrict (pbcLevelConstantComparison V (pbcIntegralDatum l E) n).hom
  let C := proEtaleRingModulePullback q (adicLisseConstantRing V P)
    (adicLisseConstantRing U P) (constantCoefficients q P)
  let F := proEtaleRingModulePullback q
    ((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n))
    ((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n)) (sbcFiniteCoefficientIso l E q n)
  let enc : F ⋙ (Rc ⋙ scalarRestriction U P) ≅
      (Rv ⋙ scalarRestriction V P) ⋙ ProEtale.upperStar (ModuleCat.{u + 1} P) q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (levelPullbackEncoding q (pbcIntegralDatum l E) n).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft Rv (pullbackEncoding q P)
  exact (Functor.mapDerivedCategoryCompIso F _).symm ≪≫
    Functor.mapDerivedCategoryNatIso enc ≪≫ Functor.mapDerivedCategoryCompIso _ _

private def finitePushEncoding {U V : Scheme.{u}} (q : U ⟶ V) (n : ℕ) :
    sbcFinitePush l E q n ⋙ (finiteEncoding l E V n).mapDerivedCategory ≅
      (finiteEncoding l E U n).mapDerivedCategory ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1}
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) q).rightDerivedFunctor := by
  let P := ProEtale.PbcQuotient (pbcIntegralDatum l E) n
  let Rc := pbcRestrict (pbcLevelConstantComparison U (pbcIntegralDatum l E) n).hom
  let Rv := pbcRestrict (pbcLevelConstantComparison V (pbcIntegralDatum l E) n).hom
  let C := proEtaleRingModuleDirectImage q (adicLisseConstantRing V P)
    (adicLisseConstantRing U P) (constantCoefficients q P)
  let F := proEtaleRingModuleDirectImage q
    ((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n))
    ((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n)) (sbcFiniteCoefficientIso l E q n)
  let level : F ⋙ Rv ≅ Rc ⋙ C :=
    proEtaleRingRestrictionDirectImage q _ _ _ _
      (pbcLevelConstantComparison V (pbcIntegralDatum l E) n).hom
      (pbcLevelConstantComparison U (pbcIntegralDatum l E) n).hom
      (constantCoefficients q P) (sbcFiniteCoefficientIso l E q n)
      (levelCoefficientSquare l E q n)
  let enc : F ⋙ finiteEncoding l E V n ≅
      finiteEncoding l E U n ⋙ ProEtale.lowerStar (ModuleCat.{u + 1} P) q :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight level _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Rc (directImageEncoding q P)
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F _).symm ≪≫
    Functor.rightDerivedFunctorNatIso enc ≪≫
      Functor.mapDerivedCategoryCompRightDerivedFunctorIso _ _

private def witnessPullEncoding {U V : Scheme.{u}} (q : U ⟶ V) (n : ℕ) :
    ProEtale.pbcWitnessPullback q (pbcIntegralDatum l E) n ≅
      (ProEtale.upperStar (ModuleCat.{u + 1}
        (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) q).mapDerivedCategory := by
  let P := ProEtale.PbcQuotient (pbcIntegralDatum l E) n
  let RV := ProEtale.finiteCoefficientRealization V P
  let RU := ProEtale.finiteCoefficientRealization U P
  let IV := ProEtale.finiteCoefficientUnrealization V P
  let IU := ProEtale.finiteCoefficientUnrealization U P
  let Q := ProEtale.upperStar (ModuleCat.{u + 1} P) q
  let enc : RV ⋙ ProEtale.finiteCoefficientPullback V P q ⋙ IU ≅ Q :=
    Functor.isoWhiskerLeft (RV ⋙ IV ⋙ Q) RU.asEquivalence.unitIso.symm ≪≫
      Functor.rightUnitor _ ≪≫
      Functor.isoWhiskerRight RV.asEquivalence.unitIso.symm Q ≪≫ Functor.leftUnitor Q
  exact Functor.isoWhiskerLeft RV.mapDerivedCategory
      (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫ Functor.mapDerivedCategoryNatIso enc

private def witnessPushEncoding {U V : Scheme.{u}} (q : U ⟶ V) (n : ℕ) :
    ProEtale.pbcWitnessDirectImage q (pbcIntegralDatum l E) n ≅
      (ProEtale.lowerStar (ModuleCat.{u + 1}
        (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) q).rightDerivedFunctor := by
  let P := ProEtale.PbcQuotient (pbcIntegralDatum l E) n
  let RU := ProEtale.finiteCoefficientRealization U P
  let RV := ProEtale.finiteCoefficientRealization V P
  let IV := ProEtale.finiteCoefficientUnrealization V P
  let Q := ProEtale.lowerStar (ModuleCat.{u + 1} P) q
  let D := ProEtale.finiteCoefficientModuleDirectImage q P
  let enc : RU ⋙ D ⋙ IV ≅ Q :=
    Functor.isoWhiskerRight (ProEtale.finiteCoefficientRealization_directImage q P).some IV ≪≫
      Functor.isoWhiskerLeft Q RV.asEquivalence.unitIso.symm ≪≫ Functor.rightUnitor _
  exact Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryCompRightDerivedFunctorIso RU D).symm _ ≪≫
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso (RU ⋙ D) IV).symm ≪≫
      Functor.rightDerivedFunctorNatIso enc

private def encodingInverse (W : Scheme.{u}) (n : ℕ) :
    (finiteEncoding l E W n).mapDerivedCategory ≅
      (pbcDerivedFunctionRealization W (pbcIntegralDatum l E) n).asEquivalence.inverse := by
  let F := (pbcDerivedFunctionRealization W (pbcIntegralDatum l E) n).asEquivalence
  let R := (finiteEncoding l E W n).mapDerivedCategory
  exact (Functor.leftUnitor R).symm ≪≫
    Functor.isoWhiskerRight F.counitIso.symm R ≪≫
      Functor.isoWhiskerLeft F.inverse (finiteDerivedEncodingUnit l E W n) ≪≫
        Functor.rightUnitor F.inverse

private theorem finiteCohomologyTransfer (W : Scheme.{u}) (n : ℕ)
    (J : DerivedCategory (pbcModules W
      ((pbcAdicRings W (pbcIntegralDatum l E)).obj (op n))))
    (N : ProEtale.PbcWitnessAmbient W (pbcIntegralDatum l E) n)
    (c : (finiteEncoding l E W n).mapDerivedCategory.obj J ≅ N)
    (a b : ℤ) (hN : sbcIntrinsicConstructibleIn W
      (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) a b N) (i : ℤ) :
    IsConstructibleProEtaleCoefficientModuleSheaf W
      (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
      (sbcAdicFiniteCohomology l E W n J i) ∧
    ((i < a ∨ b < i) → IsZero (sbcAdicFiniteCohomology l E W n J i)) := by
  let P := ProEtale.PbcQuotient (pbcIntegralDatum l E) n
  let M := sbcAdicFiniteCohomology l E W n J i
  let e : (scalarRestriction W P).obj M ≅
      (DerivedCategory.homologyFunctor _ i).obj N :=
    ((finiteEncoding l E W n).mapDerivedCategoryHomologyFunctorIso i).app J ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso c
  refine ⟨(coefficientConstructible_iff W P M).mpr ?_, ?_⟩
  · exact ProEtale.isConstructible_of_iso e.symm
      ((ProEtale.fixed_constructible_iff P W _).mp (hN i).1)
  · intro hi
    have hz := ((hN i).2 hi).of_iso e
    exact IsZero.of_full_of_faithful_of_isZero (scalarRestriction W P) M hz

private def finitePushTransport {U V : Scheme.{u}} (q : U ⟶ V) (n : ℕ)
    {J : DerivedCategory (pbcModules U
      ((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n)))}
    {N : ProEtale.PbcWitnessAmbient U (pbcIntegralDatum l E) n}
    (c : (finiteEncoding l E U n).mapDerivedCategory.obj J ≅ N) :
    (finiteEncoding l E V n).mapDerivedCategory.obj ((sbcFinitePush l E q n).obj J) ≅
      (ProEtale.pbcWitnessDirectImage q (pbcIntegralDatum l E) n).obj N :=
  (finitePushEncoding l E q n).app J ≪≫
    (ProEtale.lowerStar (ModuleCat.{u + 1}
      (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) q).rightDerivedFunctor.mapIso c ≪≫
      ((witnessPushEncoding l E q n).app N).symm

private def finitePullTransport {U V : Scheme.{u}} (q : U ⟶ V) (n : ℕ)
    {J : DerivedCategory (pbcModules V
      ((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n)))}
    {N : ProEtale.PbcWitnessAmbient V (pbcIntegralDatum l E) n}
    (c : (finiteEncoding l E V n).mapDerivedCategory.obj J ≅ N) :
    (finiteEncoding l E U n).mapDerivedCategory.obj ((sbcFinitePull l E q n).obj J) ≅
      (ProEtale.pbcWitnessPullback q (pbcIntegralDatum l E) n).obj N :=
  (finitePullEncoding l E q n).app J ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1}
      (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) q).mapDerivedCategory.mapIso c ≪≫
      ((witnessPullEncoding l E q n).app N).symm

private theorem latticeAdic [IsNoetherian X] [IsNoetherian S]
    [IsNoetherian T] [IsNoetherian Y] [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (hl : IsUnit (l : Γ(S, ⊤))) (K : PbcRationalConstructible l E T)
    (L : IntegralLattice l E T hT (sbcPrimeUnitOnSource l g hl) K)
    (hL : L.IsFiniteLevelEtaleAdmissible l E T hT (sbcPrimeUnitOnSource l g hl)) :
    IsIso (sbcExchangeApp l E sq ((pbcConstructibleInclusion l E T).obj L.integral)) ∧
    ((∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞)) →
      (∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ, ∀ i : ℤ,
        (IsConstructibleProEtaleCoefficientModuleSheaf S
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E S n
          ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj L.integral.obj)) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E S n
          ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj L.integral.obj)) i))) ∧
        (IsConstructibleProEtaleCoefficientModuleSheaf X
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePull l E f n).obj
            ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj L.integral.obj))) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePull l E f n).obj
            ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj L.integral.obj))) i))) ∧
        (IsConstructibleProEtaleCoefficientModuleSheaf Y
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E Y n
          ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj L.integral.obj)) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E Y n
          ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj L.integral.obj)) i))) ∧
        (IsConstructibleProEtaleCoefficientModuleSheaf X
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePush l E h n).obj
            ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj L.integral.obj))) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePush l E h n).obj
            ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj L.integral.obj))) i)))) →
      ∃ (hB : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
          ((sbcPull l E f).obj ((sbcPush l E g).obj
            ((pbcConstructibleInclusion l E T).obj L.integral))).obj)
        (hD : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
          ((sbcPush l E h).obj ((sbcPull l E e).obj
            ((pbcConstructibleInclusion l E T).obj L.integral))).obj),
        IsIso (ObjectProperty.homMk
          (P := PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E))
          (X := ⟨((sbcPull l E f).obj ((sbcPush l E g).obj
            ((pbcConstructibleInclusion l E T).obj L.integral))).obj, hB⟩)
          (Y := ⟨((sbcPush l E h).obj ((sbcPull l E e).obj
            ((pbcConstructibleInclusion l E T).obj L.integral))).obj, hD⟩)
          (sbcExchangeApp l E sq ((pbcConstructibleInclusion l E T).obj L.integral)).hom)) := by
  have horder : ∀ n : ℕ,
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(S, ⊤)) ∧
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(X, ⊤)) ∧
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(T, ⊤)) ∧
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(Y, ⊤)) := fun n ↦
    ⟨quotientOrderUnit l E hl n,
    quotientOrderUnit l E (by simpa using hl.map f.appTop.hom) n,
    quotientOrderUnit l E (by simpa using hl.map g.appTop.hom) n,
    quotientOrderUnit l E (by simpa using hl.map (e ≫ g).appTop.hom) n⟩
  have horigin : ∀ n : ℕ, ∃ M : Etale.BoundedConstructibleDerivedCategory
      (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) T,
    Nonempty ((pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n).obj
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ProEtale.PbcQuotient (pbcIntegralDatum l E) n))
        T).mapDerivedCategory.obj M.obj) ≅ (sbcReduction l E T n).obj L.integral.obj) := by
    intro n
    obtain ⟨M, ⟨a⟩⟩ := hL n
    exact ⟨M, ⟨(pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n).mapIso a ≪≫
      (pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n).asEquivalence.counitIso.app
        ((sbcReduction l E T n).obj L.integral.obj)⟩⟩
  exact adicSmoothBaseChange l E sq hT hl horder L.integral horigin

/-- Smooth base change for E coefficients, including lattice independence and
constructible landing with the specified endpoint identifications.
The integral and rational constructible categories and both lattice predicates are
the landed Q06 declarations. Their full inclusion into the complete category uses the
same completed coefficient ring and published intrinsic predicate. Completed pullback
is the strict tower construction with its maps. No additional universe equality is required.
Source: blueprint order 1445, sec-smooth-base-change/sk-rem-rest
(blueprint: sbc-thm-e-coefficient-smooth-base-change).

Proof: the coefficient datum already supplies finite perfect quotients. The DVR
maximal ideal contains l, since its extended p-adic norm is less than one. Thus
l^(n+1) kills the n-th quotient. Its finite additive group is an l-group, so its
cardinality is a power of l and is invertible on every corner. Transport each
admissible etale origin through the canonical realization equivalence and apply
adicSmoothBaseChange to the integral lattice. Localization preserves the resulting
isomorphism. Naturality identifies its transport along the presentation with the
rational exchange at K, and gives independence of every other presentation.

For the conditional clause, restrict the function-ring presentation along its
canonical constant-ring comparison and then to fixed scalars. This is an exact
equivalence inverse to the specified realization. Ordinary pullback and direct image
commute with it. Exact descent and the right-derived composition isomorphisms give
the corresponding comparisons for all four derived outputs. Exactness identifies
cohomology, intrinsic constructibility is invariant under these comparisons, and
full faithfulness reflects zero objects. Hence the admissible fixed-scalar interval
supplies exactly the interval required by the adic theorem. Its two constructible
integral endpoints and the integral exchange define the desired isomorphism after
rationalization. Use identity integral endpoint identifications and the given lattice
presentation; the representation equation is naturality of the rational exchange. -/
theorem eCoefficientSmoothBaseChange
    [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
    [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (_hX : ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (_hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (_hl : IsUnit (l : Γ(S, ⊤)))
    (K : PbcRationalConstructible l E T)
    (L : IntegralLattice l E T _hT (sbcPrimeUnitOnSource l g _hl) K)
    (_hL : L.IsFiniteLevelEtaleAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl)) :
    IsIso ((sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)) ∧
    (sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L =
      (sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)) ∧
    (∀ L' : IntegralLattice l E T _hT (sbcPrimeUnitOnSource l g _hl) K,
      L'.IsFiniteLevelEtaleAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl) →
      sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L' =
        sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L) ∧
    (L.IsSquareConstructiblyAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl) sq →
      SbcConstructibleExchangeRepresentation l E sq _hT (sbcPrimeUnitOnSource l g _hl) L) := by
  have hadic := latticeAdic l E sq _hT _hl K L _hL
  have htransport := transportedExchange_eq l E sq _hT (sbcPrimeUnitOnSource l g _hl) L
  have hlocal : IsIso ((sbcRationalExchange l E sq).app
      ((sbcCompleteRationalize l E T).obj
        ((pbcConstructibleInclusion l E T).obj L.integral))) := by
    have := hadic.1
    change IsIso ((sbcCompleteRationalize l E X).map
      (sbcExchangeApp l E sq ((pbcConstructibleInclusion l E T).obj L.integral)))
    infer_instance
  refine ⟨?_, htransport, ?_, ?_⟩
  · rw [← htransport]
    unfold sbcTransportedExchange
    infer_instance
  · intro L' _
    exact (transportedExchange_eq l E sq _hT (sbcPrimeUnitOnSource l g _hl) L').trans
      htransport.symm
  · intro hsquare
    have hinterval := hsquare.2
    obtain ⟨hB, hD, hiso⟩ := hadic.2 _hX (by
      obtain ⟨a, b, hab, hw⟩ := hinterval
      refine ⟨a, b, hab, fun n i ↦ ?_⟩
      let c := (encodingInverse l E T n).app ((sbcReduction l E T n).obj L.integral.obj)
      let cg := finitePushTransport l E g n c
      let cf := finitePullTransport l E f n cg
      let ce := finitePullTransport l E e n c
      let ch := finitePushTransport l E h n ce
      exact ⟨finiteCohomologyTransfer l E S n _ _ cg a b (hw n).1 i,
        finiteCohomologyTransfer l E X n _ _ cf a b (hw n).2.1 i,
        finiteCohomologyTransfer l E Y n _ _ ce a b (hw n).2.2.1 i,
        finiteCohomologyTransfer l E X n _ _ ch a b (hw n).2.2.2 i⟩)
    let B : PbcIntegralConstructible l E X := ⟨_, hB⟩
    let D : PbcIntegralConstructible l E X := ⟨_, hD⟩
    let γ : B ⟶ D := ObjectProperty.homMk
      (sbcExchangeApp l E sq ((pbcConstructibleInclusion l E T).obj L.integral)).hom
    have : IsIso γ := hiso
    let a : (pbcConstructibleInclusion l E X).obj B ≅
        (sbcPull l E f).obj ((sbcPush l E g).obj
          ((pbcConstructibleInclusion l E T).obj L.integral)) := Iso.refl _
    let b : (pbcConstructibleInclusion l E X).obj D ≅
        (sbcPush l E h).obj ((sbcPull l E e).obj
          ((pbcConstructibleInclusion l E T).obj L.integral)) := Iso.refl _
    refine ⟨B, D, a, b,
      (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).mapIso
        (asIso γ), ?_⟩
    change (pbcRationalInclusion l E X).map
        ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map γ) ≫
        𝟙 _ ≫ (sbcRationalRight l E (e := e) (h := h)).map
          ((pbcRationalInclusion l E T).map L.rationalization.hom) =
      (𝟙 _ ≫ (sbcRationalLeft l E (f := f) (g := g)).map
          ((pbcRationalInclusion l E T).map L.rationalization.hom)) ≫
        (sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)
    simp only [Category.id_comp]
    have hmap : (pbcRationalInclusion l E X).map
        ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map γ) =
        (sbcRationalExchange l E sq).app
          ((pbcRationalInclusion l E T).obj
            ((pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj
              L.integral)) := by
      dsimp only [pbcRationalInclusion, ScalarLocalization.between,
        ScalarLocalization.betweenHom, pbcRationalization, ScalarLocalization.localization]
      rw [LinearMap.baseChange_tmul]
      rfl
    rw [hmap]
    exact ((sbcRationalExchange l E sq).naturality
      ((pbcRationalInclusion l E T).map L.rationalization.hom)).symm

end WeilConjectures
