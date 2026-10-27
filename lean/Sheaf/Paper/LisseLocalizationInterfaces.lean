module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.CompletedCoefficientRegularQuotients
public import Sheaf.Paper.CompletedCoefficientRingedCoherence
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Targets.SliceRestrictionStrictDerivedLimit
public import Sheaf.Paper.RationalContinuousCoefficientDerivedLocalization

/-! # Definition interfaces for scalar localization and slice restriction

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2);
Stacks Tags 04IX, 04J0, 0940 and 0941
(blueprint: def-tw-lisse-localization-interfaces).

These transparent aliases re-export existing constructions. They assert no exactness,
restriction comparison isomorphism, derived-limit existence, or lisse-image theorem.
The host theorem modules remain available as proof dependencies of consumers.

## Main definitions

* `completedScalarSection` and `coefficientRestriction`: completed coefficient interfaces.
* `towerRestriction` and `derivedTowerRestriction`: ordinary and derived restrictions.
* `limitComplex`, `limitComparison`, `limitProjection`: strict inverse-limit interfaces.
* `derivedLinear` and `coefficientMap`: canonical localized coefficient actions.
* `LisseLocalization.StrictLimitRealizes` and `LisseLocalization.SliceLimitCompatibility`:
  the normalized derived-limit realization and restriction predicates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.LisseLocalizationInterfaces

section CompletedCoefficients
universe t u
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

/-- Constant integral scalar in the actual completed ring, via constant sheafification
and the completion map. Source: BS 6.8.2(1)
(blueprint: def-tw-lisse-localization-interfaces). -/
abbrev completedScalarSection (a : Padic.coefficientExtensionIntegers l E) :
    ((completedIntegralCommRingSheafUnrestricted l E T).obj ⋙
      forget CommRingCat.{max u (t + 1)}).sections :=
  AlgebraicGeometry.ProEtale.spCompletedScalarSection l E T a

/-- Actual sectionwise ring restriction along a pro-etale chart, equivalently restriction
to the slice transported to its pro-etale site. Source: Stacks 04IX and 04J0
(blueprint: def-tw-lisse-localization-interfaces). -/
abbrev coefficientRestriction {W : Scheme.{t}} (U : W.ProEt) :
    Sheaf (ProEt.topology W) CommRingCat.{max u (t + 1)} ⥤
      Sheaf (ProEt.topology U.left) CommRingCat.{max u (t + 1)} :=
  WeilConjectures.completedRingRestriction.{t, u} U

end CompletedCoefficients

section StrictTowers
universe u v w r
/-- Transparent re-export of the recorded levelwise slice restriction.
Source: Stacks 04IX, 0940 and 0941
(blueprint: def-tw-lisse-localization-interfaces). -/
abbrev towerRestriction
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C) :
    (ℕᵒᵖ ⥤ ringedSiteModules.{r} R) ⥤
      (ℕᵒᵖ ⥤ ringedSiteModules.{r} (Sheaf.over R U)) :=
  CategoryTheory.sliceTowerRestriction R U

/-- Transparent re-export of the recorded exact derived tower restriction.
Source: Stacks 04IX, 0940 and 0941
(blueprint: def-tw-lisse-localization-interfaces). -/
abbrev derivedTowerRestriction
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C)
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify (J.over U) AddCommGrpCat.{r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r} (Sheaf.over R U))]
    [(SheafOfModules.overFunctor R U).Additive]
    [PreservesFiniteLimits (towerRestriction R U)]
    [PreservesFiniteColimits (towerRestriction R U)] :
    DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r} R) ⥤
      DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r} (Sheaf.over R U)) :=
  CategoryTheory.sliceTowerDerivedRestriction R U

/-- Transparent re-export of the recorded termwise strict inverse limit.
Source: Stacks 04IX, 0940 and 0941
(blueprint: def-tw-lisse-localization-interfaces). -/
abbrev limitComplex
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) :=
  CategoryTheory.sliceStrictTowerLimitComplex R

/-- Transparent re-export of the recorded degreewise compatible-tuple limit.post map.
Source: Stacks 04IX, 0940 and 0941
(blueprint: def-tw-lisse-localization-interfaces). -/
abbrev limitComparison
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C)
    [(SheafOfModules.overFunctor.{r} R U).Additive]
    (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r} R) ℤ) :
    ((SheafOfModules.overFunctor R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((limitComplex R).obj I) ⟶
      (limitComplex (Sheaf.over R U)).obj
        (((towerRestriction R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  CategoryTheory.sliceStrictTowerLimitComparison R U I

/-- Transparent re-export of the recorded nth strict-limit cochain projection.
Source: Stacks 04IX, 0940 and 0941
(blueprint: def-tw-lisse-localization-interfaces). -/
abbrev limitProjection
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r})
    (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r} R) ℤ) (n : ℕ) :=
  CategoryTheory.sliceStrictTowerLimitProjection R I n

end StrictTowers

section CoefficientActions
universe uC vC u v w
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- Transparent re-export of the canonical derived coefficient action.
Source: BS 6.8.14(2)
(blueprint: def-tw-lisse-localization-interfaces). -/
abbrev derivedLinear (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))] :
    Linear A (DerivedCategory
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) :=
  CategoryTheory.scalarLocalizationDerivedLinearOfUniverses A R a

/-- Transparent re-export of the canonical localized coefficient-ring map.
Source: BS 6.8.14(2)
(blueprint: def-tw-lisse-localization-interfaces). -/
abbrev coefficientMap (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A) :
    Localization.Away t →+* RingCat.sectionsSubring
      ((ringedLocalizationRingOfUniverses R (a t)).obj ⋙
        forget₂ CommRingCat RingCat) :=
  CategoryTheory.scalarLocalizationCoefficientMapOfUniverses A R a t

end CoefficientActions

end WeilConjectures.LisseLocalizationInterfaces

-- The concrete site's canonical instances and the normalized comparison predicates
-- live with this definition owner so each statement module compiles within its limit.
universe u c v r w
open WeilConjectures.LisseLocalizationInterfaces
attribute [-instance] WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
namespace WeilConjectures.LisseLocalization

/-- Canonical ring sheafification at the fixed coefficient universe.
Source: Stacks 03CO (blueprint: def-tw-lisse-localization-interfaces). -/
instance ringSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} X

/-- Canonical additive sheafification at the fixed coefficient universe.
Source: Stacks 03CO (blueprint: def-tw-lisse-localization-interfaces). -/
instance abSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} X

/-- The canonical local description of sheaf equivalences.
Source: Stacks 03CO (blueprint: def-tw-lisse-localization-interfaces). -/
instance abLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} X

/-- The site has its recorded size; its object and morphism universes remain distinct.
Source: Stacks 09A5 (blueprint: def-tw-lisse-localization-interfaces). -/
instance siteSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0} _

/-- Additive sheafification on the actual slice site at the fixed size.
Source: Stacks 03CO (blueprint: def-tw-lisse-localization-interfaces). -/
instance sliceAbSheafify {X : Scheme.{u}} (U : X.ProEt) :
    HasSheafify ((ProEt.topology X).over U) AddCommGrpCat.{u + 1} :=
  instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover.{
    u + 1, u + 2, u, u + 1, u + 1} _ _

/-- The standard derived category of modules on the actual slice.
Source: Stacks 06XP (blueprint: def-tw-lisse-localization-interfaces). -/
instance sliceDerived {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf ((ProEt.topology X).over U) RingCat.{u + 1}) :
    HasDerivedCategory.{u + 2} (ringedSiteModules.{u + 1} R) :=
  HasDerivedCategory.standard _

/-- The standard derived category of strict slice towers.
Source: Stacks 0941 (blueprint: def-tw-lisse-localization-interfaces). -/
instance sliceTowerDerived {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf ((ProEt.topology X).over U) RingCat.{u + 1}) :
    HasDerivedCategory.{u + 2} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} R) :=
  HasDerivedCategory.standard _

/-- The specified total right derived limit realizes the recorded derived-limit triangle,
with projections normalized on K-injective strict towers.
Source: Stacks 0941 and 08TC (blueprint: def-tw-lisse-localization-interfaces). -/
def StrictLimitRealizes {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (R : Sheaf J RingCat.{r})
    [HasDerivedCategory.{w} (ringedSiteModules.{r} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r} R)]
    (L : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r} R) ⥤
      DerivedCategory.{w} (ringedSiteModules.{r} R))
    (η : limitComplex R ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ L) : Prop :=
  ∃ hp : HasCountableProducts (DerivedCategory.{w} (ringedSiteModules.{r} R)),
    (fun [_products : HasCountableProducts (DerivedCategory.{w} (ringedSiteModules.{r} R))] ↦
      ∃ (ev : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r} R) ⥤
          (ℕᵒᵖ ⥤ DerivedCategory.{w} (ringedSiteModules.{r} R)))
        (ε : DerivedCategory.Q.{w} ⋙ ev ≅
          HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
            (Functor.whiskeringRight ℕᵒᵖ
              (CochainComplex (ringedSiteModules.{r} R) ℤ)
              (DerivedCategory.{w} (ringedSiteModules.{r} R))).obj DerivedCategory.Q.{w})
        (p : ∀ Z, L.obj Z ⟶ ∏ᶜ (fun n : ℕ ↦ (ev.obj Z).obj (op n)))
        (δ : ∀ Z, (∏ᶜ (fun n : ℕ ↦ (ev.obj Z).obj (op n))) ⟶ (L.obj Z)⟦(1 : ℤ)⟧),
        (∀ Z, IsDerivedLimitTriangle
          (fun n : ℕ ↦ (ev.obj Z).map (homOfLE (Nat.le_succ n)).op)
          (L.obj Z) (p Z) (δ Z)) ∧
        (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r} R) ℤ),
          CochainComplex.IsKInjective I → ∃ _hη : IsIso (η.app I),
            ∀ n : ℕ, p (DerivedCategory.Q.obj I) ≫
              Pi.π (fun n : ℕ ↦ (ev.obj (DerivedCategory.Q.obj I)).obj (op n)) n =
                inv (η.app I) ≫ DerivedCategory.Q.map (limitProjection R I n) ≫
                  (ε.inv.app I).app (op n))) (_products := hp)

/-- Full normalized strict-derived-limit restriction assertion on the literal slice.
The last equation fixes every projection; the earlier equation fixes the comparison
on arbitrary complexes, rather than choosing unrelated cones.
Source: Stacks 0941, 04IX, 03DJ
(blueprint: def-tw-lisse-localization-interfaces). -/
def SliceLimitCompatibility {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) : Prop :=
    ∃ (_hadd : (SheafOfModules.overFunctor.{u + 1} R U).Additive)
      (_hfl : PreservesFiniteLimits (SheafOfModules.overFunctor.{u + 1} R U))
      (_hfc : PreservesFiniteColimits (SheafOfModules.overFunctor.{u + 1} R U))
      (_htl : PreservesFiniteLimits (towerRestriction R U))
      (_htc : PreservesFiniteColimits (towerRestriction R U))
      (L : DerivedCategory.{u + 2} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} R) ⥤
        DerivedCategory.{u + 2} (ringedSiteModules.{u + 1} R))
      (LU : DerivedCategory.{u + 2} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (Sheaf.over R U)) ⥤
        DerivedCategory.{u + 2} (ringedSiteModules.{u + 1} (Sheaf.over R U)))
      (η : limitComplex R ⋙ DerivedCategory.Q.{u + 2} ⟶
        DerivedCategory.Q.{u + 2} ⋙ L)
      (ηU : limitComplex (Sheaf.over R U) ⋙ DerivedCategory.Q.{u + 2} ⟶
        DerivedCategory.Q.{u + 2} ⋙ LU)
      (e : L ⋙ (SheafOfModules.overFunctor R U).mapDerivedCategory ≅
        derivedTowerRestriction R U ⋙ LU),
      StrictLimitRealizes R L η ∧
      StrictLimitRealizes (Sheaf.over R U) LU ηU ∧
      L.IsRightDerivedFunctor η
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} R)
          (ComplexShape.up ℤ)) ∧
      LU.IsRightDerivedFunctor ηU
        (HomologicalComplex.quasiIso
          (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (Sheaf.over R U)) (ComplexShape.up ℤ)) ∧
      (∀ I, CochainComplex.IsKInjective I → IsIso (η.app I)) ∧
      (∀ I, CochainComplex.IsKInjective I → IsIso (ηU.app I)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} R) ℤ),
        (SheafOfModules.overFunctor R U).mapDerivedCategory.map (η.app I) ≫
            e.hom.app (DerivedCategory.Q.obj I) ≫
            LU.map ((towerRestriction R U).mapDerivedCategoryFactors.hom.app I) =
          (SheafOfModules.overFunctor R U).mapDerivedCategoryFactors.hom.app
              ((limitComplex R).obj I) ≫
            DerivedCategory.Q.map (limitComparison R U I) ≫
            ηU.app (((towerRestriction R U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} R) ℤ),
        CochainComplex.IsKInjective I →
        ∃ (_hη : IsIso (η.app I))
          (_hηU : IsIso (ηU.app (((towerRestriction R U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I))),
          ∀ n : ℕ,
            e.hom.app (DerivedCategory.Q.obj I) ≫
                LU.map ((towerRestriction R U).mapDerivedCategoryFactors.hom.app I) ≫
                inv (ηU.app (((towerRestriction R U).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj I)) ≫
                DerivedCategory.Q.map (limitProjection (Sheaf.over R U)
                  (((towerRestriction R U).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj I) n) =
              (SheafOfModules.overFunctor R U).mapDerivedCategory.map (inv (η.app I)) ≫
                (SheafOfModules.overFunctor R U).mapDerivedCategoryFactors.hom.app
                  ((limitComplex R).obj I) ≫
                DerivedCategory.Q.map
                  (((SheafOfModules.overFunctor R U).mapHomologicalComplex
                    (ComplexShape.up ℤ)).map (limitProjection R I n)))

end WeilConjectures.LisseLocalization
