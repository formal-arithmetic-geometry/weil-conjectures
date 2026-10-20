/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.TraceFormula.BigSmallEtalePullbackFormula
public import Sheaf.CategoryTheory.DerivedBaseChangeMap
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.DerivedExactSquare
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import Sheaf.TraceFormula.BiggerSiteRetraction
import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects
import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact
import Sheaf.CategoryTheory.Sites.OverPullbackPreservesInjectives
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Sheaf.TraceFormula.BigSmallEtaleExactRetraction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Localization of big étale derived direct images

Source: Stacks Project, Étale Cohomology, Tags 075A(3),(5), 0DDJ(2), and
Topologies, Tags 021F, 021I, 0DDA
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Restriction to the small site over an arbitrary big-site object. The composite
site functor sends `U/V` to `U/W`, including its action on arrows.
Source: Stacks, Topologies, Tag 021F
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def smallEtaleRestriction {V W : Scheme.{u}} (a : V ⟶ W) :
    Sheaf (Scheme.etaleTopology.over W) AddCommGrpCat.{u + 1} ⥤
      Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  letI := Functor.isContinuous_comp (Scheme.Etale.forget V) (Over.map a)
    V.smallEtaleTopology (Scheme.etaleTopology.over V) (Scheme.etaleTopology.over W)
  (Scheme.Etale.forget V ⋙ Over.map a).sheafPushforwardContinuous
    AddCommGrpCat V.smallEtaleTopology (Scheme.etaleTopology.over W)

/-- The big-site direct image is precomposition with base change, hence has sections
`F(U ×_W V/V)`. Source: Stacks, Topologies, Tag 021H
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def bigEtaleDirectImage {V W : Scheme.{u}} (a : V ⟶ W) :
    Sheaf (Scheme.etaleTopology.over V) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Scheme.etaleTopology.over W) AddCommGrpCat.{u + 1} :=
  (Over.pullback a).sheafPushforwardContinuous AddCommGrpCat
    (Scheme.etaleTopology.over W) (Scheme.etaleTopology.over V)

/-- The canonical map identifying the two fibre products over a big-site object.
It is specified by the projections, not chosen among isomorphisms.
Source: Stacks, Topologies, Tag 0DDA
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def etaleLocalizationFibreMap {T S S' U : Scheme.{u}} (f : T ⟶ S)
    (g : S' ⟶ S) (a : U ⟶ S') :
    (Over.map (pullback.fst f g)).obj
        ((Over.pullback (pullback.snd f g)).obj (Over.mk a)) ⟶
      (Over.pullback f).obj ((Over.map g).obj (Over.mk a)) :=
  Over.homMk
    (pullback.lift (pullback.fst a (pullback.snd f g))
      (pullback.snd a (pullback.snd f g) ≫ pullback.fst f g)
      (by change pullback.fst a (pullback.snd f g) ≫ (a ≫ g) = _
          rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition]
          exact Category.assoc _ _ _))
    (by simp)

/-- The site and exactness part of the canonical localization statement. These are
conclusions, not hypotheses imposed on the schemes. All abelian restriction functors
and big direct images are the actual sectionwise functors above.
Source: Stacks, Topologies, Tags 021F, 021H, 021I, 0DDA
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
class BigSmallEtaleLocalizationSites where
  pi : ∀ V : Scheme.{u}, BigSmallEtaleRetractionData V
  [bigAdditive : ∀ {V W : Scheme.{u}} (a : V ⟶ W), (bigEtaleRestriction a).Additive]
  [bigLimits : ∀ {V W : Scheme.{u}} (a : V ⟶ W),
    PreservesFiniteLimits (bigEtaleRestriction a)]
  [bigColimits : ∀ {V W : Scheme.{u}} (a : V ⟶ W),
    PreservesFiniteColimits (bigEtaleRestriction a)]
  [smallAdditive : ∀ {V W : Scheme.{u}} (a : V ⟶ W), (smallEtaleRestriction a).Additive]
  [smallLimits : ∀ {V W : Scheme.{u}} (a : V ⟶ W),
    PreservesFiniteLimits (smallEtaleRestriction a)]
  [smallColimits : ∀ {V W : Scheme.{u}} (a : V ⟶ W),
    PreservesFiniteColimits (smallEtaleRestriction a)]
  [directAdditive : ∀ {V W : Scheme.{u}} (a : V ⟶ W), (bigEtaleDirectImage a).Additive]
  [piAdditive : ∀ V : Scheme.{u}, (pi V).morphism.inverse.Additive]
  [piLimits : ∀ V : Scheme.{u}, PreservesFiniteLimits (pi V).morphism.inverse]
  [piColimits : ∀ V : Scheme.{u}, PreservesFiniteColimits (pi V).morphism.inverse]
  bigAdj : ∀ {V W : Scheme.{u}} (a : V ⟶ W),
    bigEtaleRestriction a ⊣ bigEtaleDirectImage a


  bigUnit : ∀ {V W : Scheme.{u}} (a : V ⟶ W)
    (F : Sheaf (Scheme.etaleTopology.over W) AddCommGrpCat.{u + 1}) (U : Over W),
    ((bigAdj a).unit.app F).hom.app (op U) =
      F.obj.map (Over.homMk (pullback.fst U.hom a) pullback.condition).op
  bigTopos : ∀ {V W : Scheme.{u}} (_a : V ⟶ W),
    GeometricMorphism (Sheaf (Scheme.etaleTopology.over V) (Type (u + 1)))
      (Sheaf (Scheme.etaleTopology.over W) (Type (u + 1)))
  bigToposInverse : ∀ {V W : Scheme.{u}} (a : V ⟶ W),
    (bigTopos a).inverse ≅ (Over.map a).sheafPushforwardContinuous (Type (u + 1))
      (Scheme.etaleTopology.over V) (Scheme.etaleTopology.over W)
  smallTopos : ∀ {V W : Scheme.{u}} (_a : V ⟶ W),
    GeometricMorphism (Sheaf V.smallEtaleTopology (Type (u + 1)))
      (Sheaf W.smallEtaleTopology (Type (u + 1)))
  smallToposDirect : ∀ {V W : Scheme.{u}} (a : V ⟶ W),
    (smallTopos a).direct ≅
      (MorphismProperty.Over.pullback @Etale ⊤ a).sheafPushforwardContinuous
        (Type (u + 1)) (W.smallGrothendieckTopology @Etale)
        (V.smallGrothendieckTopology @Etale)
  i : ∀ {V W : Scheme.{u}} (_a : V ⟶ W),
    GeometricMorphism (Sheaf V.smallEtaleTopology (Type (u + 1)))
      (Sheaf (Scheme.etaleTopology.over W) (Type (u + 1)))
  iRestriction : ∀ {V W : Scheme.{u}} (a : V ⟶ W),
    (i a).inverse ⋙ sheafToPresheaf V.smallEtaleTopology (Type (u + 1)) ≅
      sheafToPresheaf (Scheme.etaleTopology.over W) (Type (u + 1)) ⋙
        (Functor.whiskeringLeft _ _ _).obj (Scheme.Etale.forget V ⋙ Over.map a).op
  continuous : ∀ {V W : Scheme.{u}} (a : V ⟶ W),
    (Scheme.Etale.forget V ⋙ Over.map a).IsContinuous V.smallEtaleTopology
      (Scheme.etaleTopology.over W)
  cocontinuous : ∀ {V W : Scheme.{u}} (a : V ⟶ W),
    (Scheme.Etale.forget V ⋙ Over.map a).IsCocontinuous V.smallEtaleTopology
      (Scheme.etaleTopology.over W)
  iFactor : ∀ {V W : Scheme.{u}} (a : V ⟶ W),
    (i a).direct ≅ ((i (𝟙 V)).comp (bigTopos a)).direct
  piComp : ∀ {V W : Scheme.{u}} (a : V ⟶ W),
    ((i a).comp (pi W).topos).direct ≅ (smallTopos a).direct
  restrictionFactor : ∀ {V W : Scheme.{u}} (a : V ⟶ W),
    smallEtaleRestriction a ≅ bigEtaleRestriction a ⋙ (pi V).morphism.direct
  restrictionFactor_sections : ∀ {V W : Scheme.{u}} (a : V ⟶ W)
    (F : Sheaf (Scheme.etaleTopology.over W) AddCommGrpCat.{u + 1}) (U : V.Etale),
    ((restrictionFactor a).hom.app F).hom.app (op U) ≫
      ((pi V).direct_restrict.hom.app ((bigEtaleRestriction a).obj F)).app (op U) =
        𝟙 _
  directSquare : ∀ {V W : Scheme.{u}} (a : V ⟶ W),
    bigEtaleDirectImage a ⋙ (pi W).morphism.direct ≅
      (pi V).morphism.direct ⋙ Etale.lowerStar AddCommGrpCat.{u + 1} a
  directSquare_sections : ∀ {V W : Scheme.{u}} (a : V ⟶ W)
    (F : Sheaf (Scheme.etaleTopology.over V) AddCommGrpCat.{u + 1}) (U : W.Etale),
    ((directSquare a).hom.app F).hom.app (op U) ≫
      ((pi V).direct_restrict.hom.app F).app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ a).obj U)) =
      ((pi W).direct_restrict.hom.app ((bigEtaleDirectImage a).obj F)).app (op U)
  c : ∀ {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S),
    bigEtaleDirectImage f ⋙ smallEtaleRestriction g ≅
      smallEtaleRestriction (pullback.fst f g) ⋙
        Etale.lowerStar AddCommGrpCat.{u + 1} (pullback.snd f g)
  c_sections : ∀ {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S)
    (F : Sheaf (Scheme.etaleTopology.over T) AddCommGrpCat.{u + 1}) (U : S'.Etale),
    ((c f g).hom.app F).hom.app (op U) =
      F.obj.map (etaleLocalizationFibreMap f g U.hom).op
  ell : ∀ {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S),
    bigEtaleDirectImage f ⋙ bigEtaleRestriction g ≅
      bigEtaleRestriction (pullback.fst f g) ⋙ bigEtaleDirectImage (pullback.snd f g)
  ell_sections : ∀ {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S)
    (F : Sheaf (Scheme.etaleTopology.over T) AddCommGrpCat.{u + 1}) (U : Over S'),
    ((ell f g).hom.app F).hom.app (op U) =
      F.obj.map (etaleLocalizationFibreMap f g U.hom).op



attribute [instance] BigSmallEtaleLocalizationSites.bigAdditive
  BigSmallEtaleLocalizationSites.bigLimits BigSmallEtaleLocalizationSites.bigColimits
  BigSmallEtaleLocalizationSites.smallAdditive BigSmallEtaleLocalizationSites.smallLimits
  BigSmallEtaleLocalizationSites.smallColimits BigSmallEtaleLocalizationSites.directAdditive
  BigSmallEtaleLocalizationSites.piAdditive BigSmallEtaleLocalizationSites.piLimits
  BigSmallEtaleLocalizationSites.piColimits

namespace BigSmallEtaleLocalizationSites

variable [P : BigSmallEtaleLocalizationSites.{u}]

/-- The big/small inverse-image square is the conjugate of the sectionwise direct
image identity. This fixes its units and counits. Source: Stacks, Topologies, Tag 021I
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def inverseSquare {V W : Scheme.{u}} (a : V ⟶ W) :
    (P.pi W).morphism.inverse ⋙ bigEtaleRestriction a ≅
      Etale.upperStar AddCommGrpCat.{u + 1} a ⋙ (P.pi V).morphism.inverse :=
  ((conjugateIsoEquiv ((P.pi W).morphism.adj.comp (P.bigAdj a))
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).comp
      (P.pi V).morphism.adj)).symm (P.directSquare a)).symm

/-- The standard bounded-below derived functor, named here to keep the comparison
signatures compact. Source: Stacks, Étale Cohomology, Tags 075A and 07A7
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def bigInverse {V W : Scheme.{u}} (a : V ⟶ W) :
    DerivedCategory.Plus (Sheaf (Scheme.etaleTopology.over W) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (Scheme.etaleTopology.over V) AddCommGrpCat.{u + 1}) :=
  (bigEtaleRestriction a).mapDerivedCategoryPlus

/-- The standard bounded-below derived functor, named here to keep the comparison
signatures compact. Source: Stacks, Étale Cohomology, Tags 075A and 07A7
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def smallRestriction {V W : Scheme.{u}} (a : V ⟶ W) :
    DerivedCategory.Plus (Sheaf (Scheme.etaleTopology.over W) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (smallEtaleRestriction a).mapDerivedCategoryPlus

/-- The standard bounded-below derived functor, named here to keep the comparison
signatures compact. Source: Stacks, Étale Cohomology, Tags 075A and 07A7
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def bigDirect {V W : Scheme.{u}} (a : V ⟶ W) :
    DerivedCategory.Plus (Sheaf (Scheme.etaleTopology.over V) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (Scheme.etaleTopology.over W) AddCommGrpCat.{u + 1}) :=
  (bigEtaleDirectImage a).rightDerivedFunctorPlus

/-- The standard bounded-below derived functor, named here to keep the comparison
signatures compact. Source: Stacks, Étale Cohomology, Tags 075A and 07A7
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def smallInverse {V W : Scheme.{u}} (a : V ⟶ W) :
    DerivedCategory.Plus (Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (Etale.upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus

/-- The standard bounded-below derived functor, named here to keep the comparison
signatures compact. Source: Stacks, Étale Cohomology, Tags 075A and 07A7
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def smallDirect {V W : Scheme.{u}} (a : V ⟶ W) :
    DerivedCategory.Plus (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} a).rightDerivedFunctorPlus

/-- The standard bounded-below derived functor, named here to keep the comparison
signatures compact. Source: Stacks, Étale Cohomology, Tags 075A and 07A7
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def extension (V : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (Scheme.etaleTopology.over V) AddCommGrpCat.{u + 1}) :=
  (P.pi V).morphism.inverse.mapDerivedCategoryPlus

/-- Exact descent of the canonical big/small square to bounded-below complexes.
Source: Stacks, Étale Cohomology, Tags 075A and 07A7
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def derivedInverseSquare {V W : Scheme.{u}} (a : V ⟶ W) :
    (BigSmallEtaleLocalizationSites.extension W) ⋙
        (BigSmallEtaleLocalizationSites.bigInverse a) ≅
      (BigSmallEtaleLocalizationSites.smallInverse a) ⋙
        (BigSmallEtaleLocalizationSites.extension V) :=
  Functor.mapDerivedCategoryPlusSquareIso _ _ _ _ (inverseSquare a)

/-- The canonical beta on abelian sheaves, with the same mate formula as the
constant-integer-ring specialization of `derivedBaseChangeMap`. Its adjunctions
are the standard derived adjunctions, not freely chosen adjunctions.
Source: Stacks, Étale Cohomology, Tags 07A7 and 0DDJ
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def beta {T S : Scheme.{u}} (f : T ⟶ S) :
    (BigSmallEtaleLocalizationSites.smallDirect f) ⋙
        (BigSmallEtaleLocalizationSites.extension S) ⟶
      (BigSmallEtaleLocalizationSites.extension T) ⋙
        (BigSmallEtaleLocalizationSites.bigDirect f) :=
  (mateEquiv (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus
    (P.bigAdj f).derivedPlus (TwoSquare.mk _ _ _ _ (derivedInverseSquare f).hom)).natTrans

/-- The inverse-image transformation whose mate is restriction of direct image.
It is intentionally a transformation, since it need not be invertible.
Source: Stacks, Topologies, Tag 0DDA
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def restrictionSquare {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S) :
    smallEtaleRestriction g ⋙ Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd f g) ⟶
      bigEtaleRestriction f ⋙ smallEtaleRestriction (pullback.fst f g) :=
  ((mateEquiv (P.bigAdj f)
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (pullback.snd f g))).symm
      (TwoSquare.mk _ _ _ _ (P.c f g).hom)).natTrans

/-- The commuting localization square, using the canonical over-category
composition comparisons and the equality of the two composites of the projections.
Source: Stacks, Topologies, Tags 021H and 0DDA
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def localizationSquare {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S) :
    bigEtaleRestriction g ⋙ bigEtaleRestriction (pullback.snd f g) ≅
      bigEtaleRestriction f ⋙ bigEtaleRestriction (pullback.fst f g) :=
  Scheme.etaleTopology.overMapPullbackComp AddCommGrpCat.{u + 1} (pullback.snd f g) g ≪≫
    Scheme.etaleTopology.overMapPullbackCongr AddCommGrpCat.{u + 1}
      pullback.condition.symm ≪≫
    (Scheme.etaleTopology.overMapPullbackComp AddCommGrpCat.{u + 1}
      (pullback.fst f g) f).symm

/-- The derived localization comparison is precisely the adjunction mate of the
canonical inverse-image square. Source: Stacks, Étale Cohomology, Tags 075A(5), 07A7
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def localizationComparison {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S) :
    (BigSmallEtaleLocalizationSites.bigDirect f) ⋙
        (BigSmallEtaleLocalizationSites.bigInverse g) ⟶
      (BigSmallEtaleLocalizationSites.bigInverse (pullback.fst f g)) ⋙
        (BigSmallEtaleLocalizationSites.bigDirect (pullback.snd f g)) :=
  (mateEquiv (P.bigAdj f).derivedPlus (P.bigAdj (pullback.snd f g)).derivedPlus
    (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategoryPlusSquareIso _ _ _ _ (localizationSquare f g)).hom)).natTrans


/-- Restricting big extension to the small site, descended termwise to `D⁺`.
Source: Stacks, Topologies, Tag 021I
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def derivedRestrictionInverse {V W : Scheme.{u}} (a : V ⟶ W)
    (e : (P.pi W).morphism.inverse ⋙ smallEtaleRestriction a ≅
      Etale.upperStar AddCommGrpCat.{u + 1} a) :
    (BigSmallEtaleLocalizationSites.extension W) ⋙
        (BigSmallEtaleLocalizationSites.smallRestriction a) ≅
      (BigSmallEtaleLocalizationSites.smallInverse a) :=
  letI := comp_preservesFiniteLimits (P.pi W).morphism.inverse (smallEtaleRestriction a)
  letI := comp_preservesFiniteColimits (P.pi W).morphism.inverse (smallEtaleRestriction a)
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso e

/-- The restriction square on bounded-below homotopy categories, retaining the
canonical comparison between the termwise composites.
Source: Stacks, Étale Cohomology, Tags 075A and 07A7
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def restrictionHomotopySquare {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S) :
    (smallEtaleRestriction g).mapHomotopyCategoryPlus ⋙
        (Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd f g)).mapHomotopyCategoryPlus ⟶
      (bigEtaleRestriction f).mapHomotopyCategoryPlus ⋙
        (smallEtaleRestriction (pullback.fst f g)).mapHomotopyCategoryPlus :=
  (Functor.mapHomotopyCategoryPlusCompIso
    (Iso.refl (smallEtaleRestriction g ⋙
      Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd f g)))).hom ≫
    NatTrans.mapHomotopyCategoryPlus (restrictionSquare f g) ≫
    (Functor.mapHomotopyCategoryPlusCompIso
      (Iso.refl (bigEtaleRestriction f ⋙ smallEtaleRestriction (pullback.fst f g)))).inv

/-- The restriction comparison obtained from its fixed sectionwise comparison by
the standard derived construction. Source: Stacks, Étale Cohomology, Tag 075A(3)
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def restrictionComparison {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S) :
    bigDirect f ⋙ smallRestriction g ⟶
      smallRestriction (pullback.fst f g) ⋙ smallDirect (pullback.snd f g) :=
  Functor.rightDerivedFunctorPlusBaseChange
    (G := bigEtaleDirectImage f)
    (G' := Etale.lowerStar AddCommGrpCat.{u + 1} (pullback.snd f g))
    (β := smallEtaleRestriction (pullback.fst f g)) (γ := smallEtaleRestriction g)
    (P.c f g).hom

/-- The termwise big localization model for comparison with its derived mate.
Source: Stacks, Étale Cohomology, Tag 075A(5)
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def localizationModel {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S) :
    bigDirect f ⋙ bigInverse g ⟶
      bigInverse (pullback.fst f g) ⋙ bigDirect (pullback.snd f g) :=
  Functor.rightDerivedFunctorPlusBaseChange
    (G := bigEtaleDirectImage f) (G' := bigEtaleDirectImage (pullback.snd f g))
    (β := bigEtaleRestriction (pullback.fst f g)) (γ := bigEtaleRestriction g)
    (P.ell f g).hom

/-- The mate of a descended restriction square under the actual derived adjunctions.
Source: Stacks, Étale Cohomology, Tag 07A7
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def restrictionMate {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S)
    (sigma : smallRestriction g ⋙ smallInverse (pullback.snd f g) ⟶
      bigInverse f ⋙ smallRestriction (pullback.fst f g)) :
    bigDirect f ⋙ smallRestriction g ⟶
      smallRestriction (pullback.fst f g) ⋙ smallDirect (pullback.snd f g) :=
  (mateEquiv (P.bigAdj f).derivedPlus
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (pullback.snd f g)).derivedPlus (TwoSquare.mk _ _ _ _ sigma)).natTrans

/-- The existing small-site exchange, with its source and target written using the
same standard-functor names as the comparison. Source: Stacks, Tag 07A7
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def smallExchange {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S) :
    smallDirect f ⋙ smallInverse g ⟶
      smallInverse (pullback.fst f g) ⋙ smallDirect (pullback.snd f g) :=
  Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
    (⟨pullback.condition⟩ : CommSq (pullback.fst f g) (pullback.snd f g) f g)

/-- Restrict beta, compose with the canonical restriction comparison, and use the
upper-edge inverse-image identification. All associators are explicit.
Source: Stacks, Étale Cohomology, Tag 0DDJ(2)
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def restrictedBetaExchange {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S)
    (e : (P.pi T).morphism.inverse ⋙ smallEtaleRestriction (pullback.fst f g) ≅
      Etale.upperStar AddCommGrpCat.{u + 1} (pullback.fst f g)) :
    smallDirect f ⋙ extension S ⋙ smallRestriction g ⟶
      smallInverse (pullback.fst f g) ⋙ smallDirect (pullback.snd f g) :=
  (Functor.associator (smallDirect f) (extension S) (smallRestriction g)).inv ≫
    Functor.whiskerRight (beta f) (smallRestriction g) ≫
    (Functor.associator (extension T) (bigDirect f) (smallRestriction g)).hom ≫
    Functor.whiskerLeft (extension T) (restrictionComparison f g) ≫
    (Functor.associator (extension T) (smallRestriction (pullback.fst f g))
      (smallDirect (pullback.snd f g))).inv ≫
    Functor.whiskerRight (derivedRestrictionInverse (pullback.fst f g) e).hom
      (smallDirect (pullback.snd f g))

/-- Identify the lower-edge source, then apply the existing small-site exchange.
Source: Stacks, Étale Cohomology, Tag 0DDJ(2)
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def smallExchangeTransport {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S)
    (e : (P.pi S).morphism.inverse ⋙ smallEtaleRestriction g ≅
      Etale.upperStar AddCommGrpCat.{u + 1} g) :
    smallDirect f ⋙ extension S ⋙ smallRestriction g ⟶
      smallInverse (pullback.fst f g) ⋙ smallDirect (pullback.snd f g) :=
  Functor.whiskerLeft (smallDirect f) (derivedRestrictionInverse g e).hom ≫
    smallExchange f g

end BigSmallEtaleLocalizationSites

namespace BigSmallEtaleLocalizationSites

variable [P : BigSmallEtaleLocalizationSites.{u}]

/-- The family of small inverse-image identifications in the node.
Source: Stacks, Topologies, Tag 021I
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def EtaFamily :=
  ∀ {V W : Scheme.{u}} (a : V ⟶ W),
    (P.pi W).morphism.inverse ⋙ smallEtaleRestriction a ≅
      Etale.upperStar AddCommGrpCat.{u + 1} a

/-- The descended restriction-square transformations, without an invertibility condition.
Source: Stacks, Topologies, Tag 0DDA; Étale Cohomology, Tag 075A(3)
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def SigmaFamily :=
  ∀ {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S),
    (BigSmallEtaleLocalizationSites.smallRestriction g) ⋙
        (BigSmallEtaleLocalizationSites.smallInverse (pullback.snd f g)) ⟶
      (BigSmallEtaleLocalizationSites.bigInverse f) ⋙
        (BigSmallEtaleLocalizationSites.smallRestriction (pullback.fst f g))

/-- The `eta_unit` clause of the localization statement, named to keep the
witness package's dependent types small. Source: Stacks, Étale Cohomology,
Tags 075A(3),(5), 0DDJ(2) and 07A7; Topologies, Tags 021I and 0DDA
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def IsEtaUnit (eta : EtaFamily) : Prop :=
  ∀ {V W : Scheme.{u}} (a : V ⟶ W)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}),
    (eta a).hom.app F ≫
        (P.pi V).morphism.adj.unit.app ((Etale.upperStar AddCommGrpCat.{u + 1} a).obj F) =
      (P.restrictionFactor a).hom.app ((P.pi W).morphism.inverse.obj F) ≫
        (P.pi V).morphism.direct.map
          ((BigSmallEtaleLocalizationSites.inverseSquare a).hom.app F)

/-- The `sigma_fac` clause of the localization statement, named to keep the
witness package's dependent types small. Source: Stacks, Étale Cohomology,
Tags 075A(3),(5), 0DDJ(2) and 07A7; Topologies, Tags 021I and 0DDA
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def IsSigmaFactorization (sigma : SigmaFamily) : Prop :=
  ∀ {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S)
    (K : HomotopyCategory.Plus
      (Sheaf (Scheme.etaleTopology.over S) AddCommGrpCat.{u + 1})),
    (sigma f g).app (DerivedCategory.Plus.Qh.obj K) ≫
        (BigSmallEtaleLocalizationSites.smallRestriction (pullback.fst f g)).map
          ((bigEtaleRestriction f).mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        (smallEtaleRestriction (pullback.fst f g)).mapDerivedCategoryPlusFactorsh.hom.app
          ((bigEtaleRestriction f).mapHomotopyCategoryPlus.obj K) =
      (BigSmallEtaleLocalizationSites.smallInverse (pullback.snd f g)).map
          ((smallEtaleRestriction g).mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        (Etale.upperStar AddCommGrpCat.{u + 1}
          (pullback.snd f g)).mapDerivedCategoryPlusFactorsh.hom.app
            ((smallEtaleRestriction g).mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map
          ((BigSmallEtaleLocalizationSites.restrictionHomotopySquare f g).app K)

/-- The `restriction_iso` clause of the localization statement, named to keep the
witness package's dependent types small. Source: Stacks, Étale Cohomology,
Tags 075A(3),(5), 0DDJ(2) and 07A7; Topologies, Tags 021I and 0DDA
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def IsRestrictionIso : Prop :=
  ∀ {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S),
    IsIso (BigSmallEtaleLocalizationSites.restrictionComparison f g)

/-- The `restriction_mate` clause of the localization statement, named to keep the
witness package's dependent types small. Source: Stacks, Étale Cohomology,
Tags 075A(3),(5), 0DDJ(2) and 07A7; Topologies, Tags 021I and 0DDA
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def IsRestrictionMate (sigma : SigmaFamily) : Prop :=
  ∀ {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S),
    BigSmallEtaleLocalizationSites.restrictionComparison f g =
      BigSmallEtaleLocalizationSites.restrictionMate f g (sigma f g)

/-- The `localization_iso` clause of the localization statement, named to keep the
witness package's dependent types small. Source: Stacks, Étale Cohomology,
Tags 075A(3),(5), 0DDJ(2) and 07A7; Topologies, Tags 021I and 0DDA
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def IsLocalizationIso : Prop :=
  ∀ {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S),
    IsIso (BigSmallEtaleLocalizationSites.localizationComparison f g)

/-- The `localization_model` clause of the localization statement, named to keep the
witness package's dependent types small. Source: Stacks, Étale Cohomology,
Tags 075A(3),(5), 0DDJ(2) and 07A7; Topologies, Tags 021I and 0DDA
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def IsLocalizationModel : Prop :=
  ∀ {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S),
    BigSmallEtaleLocalizationSites.localizationComparison f g =
      BigSmallEtaleLocalizationSites.localizationModel f g

/-- The `arrow` clause of the localization statement, named to keep the
witness package's dependent types small. Source: Stacks, Étale Cohomology,
Tags 075A(3),(5), 0DDJ(2) and 07A7; Topologies, Tags 021I and 0DDA
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def IsExchangeCompatible (eta : EtaFamily) : Prop :=
  ∀ {T S S' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S),
    BigSmallEtaleLocalizationSites.restrictedBetaExchange f g (eta (pullback.fst f g)) =
      BigSmallEtaleLocalizationSites.smallExchangeTransport f g (eta g)

/-- The `jointly_conservative` clause of the localization statement, named to keep the
witness package's dependent types small. Source: Stacks, Étale Cohomology,
Tags 075A(3),(5), 0DDJ(2) and 07A7; Topologies, Tags 021I and 0DDA
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
def IsJointlyConservative : Prop :=
  ∀ (S : Scheme.{u})
    (X Y : DerivedCategory.Plus
      (Sheaf (Scheme.etaleTopology.over S) AddCommGrpCat.{u + 1})) (z : X ⟶ Y),
    (∀ (S' : Scheme.{u}) (g : S' ⟶ S),
      IsIso ((BigSmallEtaleLocalizationSites.smallRestriction g).map z)) → IsIso z

end BigSmallEtaleLocalizationSites

/-- All clauses of localization and exchange compatibility on bounded-below derived
categories. `sigma_fac` pins the possibly noninvertible inverse-image transformation
to termwise descent; `restriction_mate` and `localization_model` pin both derived
comparisons to their actual adjunction mates and their sectionwise models.
`arrow` identifies the actual canonical beta with the existing small-site exchange.
Source: Stacks, Étale Cohomology, Tags 075A(3),(5), 0DDJ(2), 07A7; Topologies 0DDA
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward). -/
structure BigSmallEtaleLocalizationDerivedData where
  [sites : BigSmallEtaleLocalizationSites.{u}]
  eta : @BigSmallEtaleLocalizationSites.EtaFamily.{u} sites
  sigma : @BigSmallEtaleLocalizationSites.SigmaFamily.{u} sites
  eta_unit : @BigSmallEtaleLocalizationSites.IsEtaUnit.{u} sites eta
  sigma_fac : @BigSmallEtaleLocalizationSites.IsSigmaFactorization.{u} sites sigma
  restriction_iso : @BigSmallEtaleLocalizationSites.IsRestrictionIso.{u} sites
  restriction_mate : @BigSmallEtaleLocalizationSites.IsRestrictionMate.{u} sites sigma
  localization_iso : @BigSmallEtaleLocalizationSites.IsLocalizationIso.{u} sites
  localization_model : @BigSmallEtaleLocalizationSites.IsLocalizationModel.{u} sites
  arrow : @BigSmallEtaleLocalizationSites.IsExchangeCompatible.{u} sites eta
  jointly_conservative : @BigSmallEtaleLocalizationSites.IsJointlyConservative.{u} sites

/-- Big étale localization and small-site restriction of derived direct image, with
canonical-mate normalization, identification with small-site exchange, and joint
conservativity. The existential package adds no assumptions on schemes or complexes.
Source: Stacks Project, Étale Cohomology, Tags 075A(3),(5), 0DDJ(2), and Topologies,
Tags 021F, 021H, 021I, 0DDA
(blueprint: lem-trf-big-small-etale-localization-derived-pushforward).

Proof:
1. The functors `U/V ↦ U/W` preserve étale coverings and their fibre products.
Every covering of an étale `U/V` lifts to that small site, by étale composition
(lem-weil-pbc-etale-composition-cancellation). The continuous-cocontinuous adjunction
(lem-weil-pbc-continuous-cocontinuous-topos-adjunction) gives the geometric morphisms
with the stated restriction inverse images. Lift to abelian sheaves by
lem-weil-pbc-sheaf-algebraic-structures-objects and
lem-weil-pbc-adjunction-lifts-group-ring-objects; inverse images are exact by
lem-pe-constant-left-module-inverse-image with integer coefficients.
2. The big right adjoint has sections `F(U ×_W V)`: compatible families are
uniquely determined by their member at the fibre product (def-pc-fibre-product).
The adjunction unit is restriction along the first projection and the counit
along the graph. These give `bigAdj` and `bigUnit` with their actual normalizations.
3. Apply lem-trf-bigger-site-retraction and lem-trf-big-small-etale-exact-retraction
to the small inclusion. Restriction factors through big localization; evaluate
small direct images using def-weil-pbc-direct-image to obtain `directSquare`.
Conjugate this identity along the actual adjunctions to obtain `inverseSquare`.
Restrict it once more and cancel the invertible retraction unit to obtain `eta`.
4. Identify `B_W/(V/W)` with `B_V`. Localization is exact and preserves injectives
by lem-weil-pbc-site-restriction-exact and new-over-pullback-preserves-injectives.
Small restriction is `pi_*`; its left adjoint is exact, so it preserves injectives
by lem-exc-rg-right-adjoint-preserves-injectives. Composite restrictions do too.
5. Over every `U/S'`, both section calculations are related by the unique
fibre-product map commuting with the projections. This is precisely
`etaleLocalizationFibreMap`, and gives `c_sections` and `ell_sections`.
6. Choose bounded-below injective representatives by
lem-weil-pbc-site-sheaves-enough-injectives and lem-weil-pbc-dplus-injective-representative.
Their restrictions remain injective. Apply lem-weil-pbc-right-derived-plus-injective
and lem-weil-pbc-exact-functor-derived-factorization termwise. The sectionwise
isomorphisms therefore give both derived isomorphisms. Naturality and independence
follow from lem-weil-pbc-kinjective-hom-derived and preservation of homotopies.
7. Take the inverse mate of `c` to obtain `restrictionSquare`; this need not be
invertible. Descend termwise to `sigma`, with equation `sigma_fac`. The derived
mate model (lem-trf-bounded-below-derived-mate-model) identifies its mate with the
computed restriction comparison. Apply the same argument to the invertible big
localization square to obtain `localization_model` and its isomorphism.
8. Paste the restriction square with the canonical conjugate `inverseSquare`.
The intermediate unit and counit cancel by the triangle identity. On sections
what remains is the canonical fibre-product square. Use
lem-weil-pbc-mate-pasting and lem-weil-pbc-derived-exact-square-factorization to
descend this identity, with all composition comparisons retained.
9. Apply mate pasting to that derived identity. The resulting composite is
restriction of `beta` followed by `c`. Its transpose is the small square followed
by the small counit, which is exactly def-weil-pbc-derived-exchange. This proves
`arrow`, with the convention of def-trf-topos-derived-base-change-map.
10. Evaluation of every restriction at its final small object detects every big
section. Thus the restrictions detect zero abelian sheaves. Exactness commutes
with cohomology, so they detect zero derived objects. Apply the cone criterion
lem-kun-distinguished-cone-zero to a derived morphism: if all restrictions are
invertible, its cone restricts to zero, is zero, and the morphism is invertible.
-/
theorem bigSmallEtaleLocalizationDerivedPushforward :
    Nonempty BigSmallEtaleLocalizationDerivedData.{u} := by
  sorry

end AlgebraicGeometry
