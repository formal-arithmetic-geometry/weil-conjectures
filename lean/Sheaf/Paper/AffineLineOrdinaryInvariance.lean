/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.Paper.RingedTopoiDerivedTensorPullback
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Sheaf.Paper.CoefficientTwistsDetailed
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.Paper.SfDerivedDirectImage
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.PurTwistSheafLocallyFree
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Sheaf.AlgebraicGeometry.KummerAffineLine
import WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem
import Sheaf.AlgebraicGeometry.StrictlyHenselianConstantCohomology
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.FiniteDirectImageComposition
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.SupportedCupFunctoriality

/-!
# Ordinary affine-line invariance

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
Reduction to a geometric fibre, Coefficients, and Base change on Y
(blueprint: lem-pur-affine-line-ordinary-invariance).

All maps below are compositions of the published adjunction units and canonical
composition comparisons. The coefficient category is abelian groups, so coefficient
maps include maps between different finite coefficient rings. Bounded-below derived
categories compute the ordinary unbounded operations on these degree-zero sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Ordinary derived global sections in the recorded small topology.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
abbrev a1OrdinarySections (X : Scheme.{u}) :=
  (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus

/-- Exact inverse image on bounded-below derived categories.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
abbrev a1OrdinaryPullback {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus

/-- The canonical derived adjunction; no monoidal or flat-resolution choice is needed.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryAdjunction {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus

/-- Leray comparison, with the ordinary equality of sections of a pushforward.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryLeray {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus ⋙
      a1OrdinarySections X ≅ a1OrdinarySections Y := by
  letI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
  exact Functor.rightDerivedFunctorPlusCompIso' _ _
    (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} f)

/-- The canonical pullback of ordinary derived sections, as a natural transformation.
Its naturality includes every morphism of underlying finite coefficient sheaves.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryGlobalPullback {X Y : Scheme.{u}} (f : Y ⟶ X) :
    a1OrdinarySections X ⟶ a1OrdinaryPullback f ⋙ a1OrdinarySections Y :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (a1OrdinaryAdjunction f).unit (a1OrdinarySections X) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (a1OrdinaryPullback f) (a1OrdinaryLeray f).hom

/-- The canonical composition identification, descended from exact sheaf inverse image.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryComp {S X Y : Scheme.{u}} (f : Y ⟶ X) (a : X ⟶ S) :
    a1OrdinaryPullback (f ≫ a) ≅ a1OrdinaryPullback a ⋙ a1OrdinaryPullback f :=
  Functor.mapDerivedCategoryPlusNatIso (upperStarComp AddCommGrpCat.{u + 1} f a) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The inverse-image identification for a specified commutative square.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinarySquare {X Y X' Y' : Scheme.{u}}
    {w : Y' ⟶ Y} {p' : Y' ⟶ X'} {p : Y ⟶ X} {v : X' ⟶ X}
    (sq : CommSq w p' p v) :
    a1OrdinaryPullback v ⋙ a1OrdinaryPullback p' ≅
      a1OrdinaryPullback p ⋙ a1OrdinaryPullback w :=
  (a1OrdinaryComp p' v).symm ≪≫
    eqToIso (congrArg a1OrdinaryPullback sq.w.symm) ≪≫ a1OrdinaryComp w p

/-- The exchange map is the counit mate of the specified inverse-image square.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryExchange {X Y X' Y' : Scheme.{u}}
    {w : Y' ⟶ Y} {p' : Y' ⟶ X'} {p : Y ⟶ X} {v : X' ⟶ X}
    (sq : CommSq w p' p v)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
  (a1OrdinaryAdjunction p').unit.app
      ((a1OrdinaryPullback v).obj
        ((lowerStar AddCommGrpCat.{u + 1} p).rightDerivedFunctorPlus.obj K)) ≫
    (lowerStar AddCommGrpCat.{u + 1} p').rightDerivedFunctorPlus.map
      ((a1OrdinarySquare sq).hom.app
          ((lowerStar AddCommGrpCat.{u + 1} p).rightDerivedFunctorPlus.obj K) ≫
        (a1OrdinaryPullback w).map ((a1OrdinaryAdjunction p).counit.app K))

/-- Naturality of the actual unit under the canonical exchange map, without
assuming the exchange invertible on arbitrary complexes.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryUnitNatural {X Y X' Y' : Scheme.{u}}
    {w : Y' ⟶ Y} {p' : Y' ⟶ X'} {p : Y ⟶ X} {v : X' ⟶ X}
    (sq : CommSq w p' p v)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) : Prop :=
  (a1OrdinaryPullback v).map ((a1OrdinaryAdjunction p).unit.app K) ≫
      a1OrdinaryExchange sq ((a1OrdinaryPullback p).obj K) =
    (a1OrdinaryAdjunction p').unit.app ((a1OrdinaryPullback v).obj K) ≫
      (lowerStar AddCommGrpCat.{u + 1} p').rightDerivedFunctorPlus.map
        ((a1OrdinarySquare sq).hom.app K)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- Ordinary derived global sections in the recorded small topology.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
abbrev a1OrdinarySections (X : Scheme.{u}) :=
  (Sheaf.Γ (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus

/-- Exact inverse image on bounded-below derived categories.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
abbrev a1OrdinaryPullback {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus

/-- The canonical derived adjunction; no monoidal or flat-resolution choice is needed.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryAdjunction {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus

/-- Leray comparison, with the ordinary equality of sections of a pushforward.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryLeray {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus ⋙
      a1OrdinarySections X ≅ a1OrdinarySections Y := by
  letI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
  exact Functor.rightDerivedFunctorPlusCompIso' _ _
    (globalSectionsLowerStarIso AddCommGrpCat.{u + 1} f)

/-- The canonical pullback of ordinary derived sections, as a natural transformation.
Its naturality includes every morphism of underlying finite coefficient sheaves.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryGlobalPullback {X Y : Scheme.{u}} (f : Y ⟶ X) :
    a1OrdinarySections X ⟶ a1OrdinaryPullback f ⋙ a1OrdinarySections Y :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (a1OrdinaryAdjunction f).unit (a1OrdinarySections X) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (a1OrdinaryPullback f) (a1OrdinaryLeray f).hom

/-- The canonical composition identification, descended from exact sheaf inverse image.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryComp {S X Y : Scheme.{u}} (f : Y ⟶ X) (a : X ⟶ S) :
    a1OrdinaryPullback (f ≫ a) ≅ a1OrdinaryPullback a ⋙ a1OrdinaryPullback f :=
  Functor.mapDerivedCategoryPlusNatIso (upperStarComp AddCommGrpCat.{u + 1} f a) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The inverse-image identification for a specified commutative square.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinarySquare {X Y X' Y' : Scheme.{u}}
    {w : Y' ⟶ Y} {p' : Y' ⟶ X'} {p : Y ⟶ X} {v : X' ⟶ X}
    (sq : CommSq w p' p v) :
    a1OrdinaryPullback v ⋙ a1OrdinaryPullback p' ≅
      a1OrdinaryPullback p ⋙ a1OrdinaryPullback w :=
  (a1OrdinaryComp p' v).symm ≪≫
    eqToIso (congrArg a1OrdinaryPullback sq.w.symm) ≪≫ a1OrdinaryComp w p

/-- The exchange map is the counit mate of the specified inverse-image square.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryExchange {X Y X' Y' : Scheme.{u}}
    {w : Y' ⟶ Y} {p' : Y' ⟶ X'} {p : Y ⟶ X} {v : X' ⟶ X}
    (sq : CommSq w p' p v)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})) :=
  (a1OrdinaryAdjunction p').unit.app
      ((a1OrdinaryPullback v).obj
        ((lowerStar AddCommGrpCat.{u + 1} p).rightDerivedFunctorPlus.obj K)) ≫
    (lowerStar AddCommGrpCat.{u + 1} p').rightDerivedFunctorPlus.map
      ((a1OrdinarySquare sq).hom.app
          ((lowerStar AddCommGrpCat.{u + 1} p).rightDerivedFunctorPlus.obj K) ≫
        (a1OrdinaryPullback w).map ((a1OrdinaryAdjunction p).counit.app K))

/-- Naturality of the actual unit under the canonical exchange map, without
assuming the exchange invertible on arbitrary complexes.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryUnitNatural {X Y X' Y' : Scheme.{u}}
    {w : Y' ⟶ Y} {p' : Y' ⟶ X'} {p : Y ⟶ X} {v : X' ⟶ X}
    (sq : CommSq w p' p v)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})) : Prop :=
  (a1OrdinaryPullback v).map ((a1OrdinaryAdjunction p).unit.app K) ≫
      a1OrdinaryExchange sq ((a1OrdinaryPullback p).obj K) =
    (a1OrdinaryAdjunction p').unit.app ((a1OrdinaryPullback v).obj K) ≫
      (lowerStar AddCommGrpCat.{u + 1} p').rightDerivedFunctorPlus.map
        ((a1OrdinarySquare sq).hom.app K)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

/-- Exact canonical comparison inverse image on bounded-below derived categories.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
abbrev a1OrdinaryComparison (X : Scheme.{u}) :=
  (comparisonUpperStar AddCommGrpCat.{u + 1} X).mapDerivedCategoryPlus

/-- The canonical global-sections comparison before deriving: restriction along
the site inclusion evaluates at the same terminal scheme.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryComparisonSectionsIso (X : Scheme.{u}) :
    comparisonLowerStar AddCommGrpCat.{u + 1} X ⋙
        Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1} ≅
      Sheaf.Γ (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerLeft _
      (Sheaf.ΓNatIsoSheafSections _ _
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)) ≪≫
    NatIso.ofComponents (fun _ => Iso.refl _) ≪≫
    (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)).symm

/-- Leray for the actual site-comparison direct image.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryComparisonLeray (X : Scheme.{u}) :
    (comparisonLowerStar AddCommGrpCat.{u + 1} X).rightDerivedFunctorPlus ⋙
        Etale.a1OrdinarySections X ≅ a1OrdinarySections X := by
  letI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (comparisonAdjunction AddCommGrpCat.{u + 1} X)
  exact Functor.rightDerivedFunctorPlusCompIso' _ _ (a1OrdinaryComparisonSectionsIso X)

/-- The canonical global comparison is the derived comparison unit followed by Leray.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryGlobalComparison (X : Scheme.{u}) :
    Etale.a1OrdinarySections X ⟶ a1OrdinaryComparison X ⋙ a1OrdinarySections X :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (comparisonAdjunction AddCommGrpCat.{u + 1} X).derivedPlus.unit
      (Etale.a1OrdinarySections X) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (a1OrdinaryComparison X) (a1OrdinaryComparisonLeray X).hom

/-- The derived pullback comparison, constructed from the canonical sheaf comparison.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryComparisonPullback {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Etale.a1OrdinaryPullback f ⋙ a1OrdinaryComparison Y ≅
      a1OrdinaryComparison X ⋙ a1OrdinaryPullback f :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (comparisonUpperStarCompUpperStarIso AddCommGrpCat.{u + 1} f).symm ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

end AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- The signed finite etale Tate sheaf, using the canonical annihilator ringChar A.
No condition that the ramification index divide the coefficient level is imposed.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryBaseTwist (P : PurityFiniteSetting.{u}) (r : ℤ) :=
  (P.forgetEtale (Spec (.of P.field.k))).obj
    (Scheme.finiteEtaleTateSheaf P.Coefficient (ringChar P.Coefficient)
      (Spec (.of P.field.k)) (CharP.cast_eq_zero P.Coefficient (ringChar P.Coefficient)) r)

/-- The finite signed twist in degree zero on the geometric base.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryBaseComplex (P : PurityFiniteSetting.{u}) (r : ℤ) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj (P.a1OrdinaryBaseTwist r)

/-- The etale coefficient family on all schemes over a fixed base, by exact pullback.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
abbrev a1OrdinaryEtaleFamily {S X : Scheme.{u}} (a : X ⟶ S) :=
  Etale.a1OrdinaryPullback a

/-- The etale-origin pro-etale coefficient family, via the actual comparison functor.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
abbrev a1OrdinaryProEtaleFamily {S X : Scheme.{u}} (a : X ⟶ S) :=
  a1OrdinaryEtaleFamily a ⋙ ProEtale.a1OrdinaryComparison X

/-- Ordinary integer-degree Etale cohomology as a functor of the base coefficient.
In negative degrees its value on a sheaf in degree zero is zero.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
abbrev a1OrdinaryEtaleH {S X : Scheme.{u}} (a : X ⟶ S) (q : ℤ) :=
  a1OrdinaryEtaleFamily a ⋙ Etale.a1OrdinarySections X ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q

/-- The canonical coefficient transport for pullback between named structure maps.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryEtaleCoefficientIso {S X Y : Scheme.{u}} (f : Y ⟶ X)
    (a : X ⟶ S) (b : Y ⟶ S) (hb : b = f ≫ a) :
    a1OrdinaryEtaleFamily a ⋙ Etale.a1OrdinaryPullback f ≅
      a1OrdinaryEtaleFamily b :=
  (Etale.a1OrdinaryComp f a).symm ≪≫
    eqToIso (congrArg a1OrdinaryEtaleFamily hb.symm)

/-- The ordinary cohomology pullback. It is a natural transformation on the entire
base coefficient category, hence respects finite coefficient maps before and after
forgetting their ring actions.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryEtaleCohomologyPullback {S X Y : Scheme.{u}} (f : Y ⟶ X)
    (a : X ⟶ S) (b : Y ⟶ S) (hb : b = f ≫ a) (q : ℤ) :
    a1OrdinaryEtaleH a q ⟶ a1OrdinaryEtaleH b q :=
  Functor.whiskerRight
    (Functor.whiskerLeft (a1OrdinaryEtaleFamily a) (Etale.a1OrdinaryGlobalPullback f) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (a1OrdinaryEtaleCoefficientIso f a b hb).hom
        (Etale.a1OrdinarySections Y))
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q)

/-- Ordinary integer-degree ProEtale cohomology as a functor of the base coefficient.
In negative degrees its value on a sheaf in degree zero is zero.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
abbrev a1OrdinaryProEtaleH {S X : Scheme.{u}} (a : X ⟶ S) (q : ℤ) :=
  a1OrdinaryProEtaleFamily a ⋙ ProEtale.a1OrdinarySections X ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q

/-- The canonical coefficient transport for pullback between named structure maps.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryProEtaleCoefficientIso {S X Y : Scheme.{u}} (f : Y ⟶ X)
    (a : X ⟶ S) (b : Y ⟶ S) (hb : b = f ≫ a) :
    a1OrdinaryProEtaleFamily a ⋙ ProEtale.a1OrdinaryPullback f ≅
      a1OrdinaryProEtaleFamily b :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ProEtale.a1OrdinaryComparisonPullback f).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (a1OrdinaryEtaleCoefficientIso f a b hb) _

/-- The ordinary cohomology pullback. It is a natural transformation on the entire
base coefficient category, hence respects finite coefficient maps before and after
forgetting their ring actions.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryProEtaleCohomologyPullback {S X Y : Scheme.{u}} (f : Y ⟶ X)
    (a : X ⟶ S) (b : Y ⟶ S) (hb : b = f ≫ a) (q : ℤ) :
    a1OrdinaryProEtaleH a q ⟶ a1OrdinaryProEtaleH b q :=
  Functor.whiskerRight
    (Functor.whiskerLeft (a1OrdinaryProEtaleFamily a) (ProEtale.a1OrdinaryGlobalPullback f) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (a1OrdinaryProEtaleCoefficientIso f a b hb).hom
        (ProEtale.a1OrdinarySections Y))
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q)

/-- The canonical comparison on ordinary integer-degree cohomology, natural in
the base coefficient sheaf and including the degree-zero coefficient transport.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryCohomologyComparison {S X : Scheme.{u}} (a : X ⟶ S) (q : ℤ) :
    a1OrdinaryEtaleH a q ⟶ a1OrdinaryProEtaleH a q :=
  Functor.whiskerRight
    (Functor.whiskerLeft (a1OrdinaryEtaleFamily a)
        (ProEtale.a1OrdinaryGlobalComparison X) ≫ (Functor.associator _ _ _).inv)
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q)

/-- The actual affine-line projection of relative dimension one.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
abbrev a1OrdinaryProjection (X : Scheme.{u}) :=
  AffineSpace (ULift.{u} (Fin 1)) X ↘ X

/-- The chosen affine-line projection square over an arbitrary base morphism.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
abbrev a1OrdinaryProjectionSquare {X X' : Scheme.{u}} (v : X' ⟶ X) :
    CommSq (AffineSpace.map (ULift.{u} (Fin 1)) v)
      (a1OrdinaryProjection X') (a1OrdinaryProjection X) v :=
  (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) v).toCommSq

/-- The common structure morphism of the affine-line projection square.
This equality retains the actual specified commutative square.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
abbrev a1OrdinarySquareBase {S X X' : Scheme.{u}} (v : X' ⟶ X) (a : X ⟶ S) :
    a1OrdinaryProjection X' ≫ (v ≫ a) =
      AffineSpace.map (ULift.{u} (Fin 1)) v ≫ (a1OrdinaryProjection X ≫ a) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ a) (a1OrdinaryProjectionSquare v).w.symm).trans
      (Category.assoc _ _ _))

/-- The projection pullback as a natural transformation in the base coefficients.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryEtaleProjection {S X : Scheme.{u}} (a : X ⟶ S) (q : ℤ) :=
  a1OrdinaryEtaleCohomologyPullback (a1OrdinaryProjection X) a
    (a1OrdinaryProjection X ≫ a) rfl q

/-- The commuting square expressing naturality in an arbitrary base scheme.
All four edges are canonical ordinary pullback maps.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryEtaleBaseNatural {S X X' : Scheme.{u}} (v : X' ⟶ X) (a : X ⟶ S)
    (q : ℤ) (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    Prop :=
  (a1OrdinaryEtaleProjection a q).app K ≫
      (a1OrdinaryEtaleCohomologyPullback (AffineSpace.map (ULift.{u} (Fin 1)) v)
        (a1OrdinaryProjection X ≫ a) (a1OrdinaryProjection X' ≫ (v ≫ a))
        (a1OrdinarySquareBase v a) q).app K =
    (a1OrdinaryEtaleCohomologyPullback v a (v ≫ a) rfl q).app K ≫
      (a1OrdinaryEtaleProjection (v ≫ a) q).app K

/-- The projection pullback as a natural transformation in the base coefficients.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryProEtaleProjection {S X : Scheme.{u}} (a : X ⟶ S) (q : ℤ) :=
  a1OrdinaryProEtaleCohomologyPullback (a1OrdinaryProjection X) a
    (a1OrdinaryProjection X ≫ a) rfl q

/-- The commuting square expressing naturality in an arbitrary base scheme.
All four edges are canonical ordinary pullback maps.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryProEtaleBaseNatural {S X X' : Scheme.{u}} (v : X' ⟶ X) (a : X ⟶ S)
    (q : ℤ) (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    Prop :=
  (a1OrdinaryProEtaleProjection a q).app K ≫
      (a1OrdinaryProEtaleCohomologyPullback (AffineSpace.map (ULift.{u} (Fin 1)) v)
        (a1OrdinaryProjection X ≫ a) (a1OrdinaryProjection X' ≫ (v ≫ a))
        (a1OrdinarySquareBase v a) q).app K =
    (a1OrdinaryProEtaleCohomologyPullback v a (v ≫ a) rfl q).app K ≫
      (a1OrdinaryProEtaleProjection (v ≫ a) q).app K

end WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison direct-image mate for underlying abelian sheaves,
using exactly the published underived mate and right-derived base-change construction.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryDirectImageMate {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  Functor.rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange f AddCommGrpCat.{u + 1})

/-- Equality of the actual etale and pro-etale unit maps under the canonical
comparison mate and the canonical pullback comparison.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryUnitsCompared {X Y : Scheme.{u}} (p : Y ⟶ X)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) : Prop :=
  (a1OrdinaryComparison X).map ((Etale.a1OrdinaryAdjunction p).unit.app K) ≫
      (a1OrdinaryDirectImageMate p).app ((Etale.a1OrdinaryPullback p).obj K) ≫
      (lowerStar AddCommGrpCat.{u + 1} p).rightDerivedFunctorPlus.map
        ((a1OrdinaryComparisonPullback p).hom.app K) =
    (a1OrdinaryAdjunction p).unit.app ((a1OrdinaryComparison X).obj K)

end AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- The same finite signed twist before forgetting its coefficient module action.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryBaseModuleComplex (P : PurityFiniteSetting.{u}) (r : ℤ) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj
    (Scheme.finiteEtaleTateSheaf P.Coefficient (ringChar P.Coefficient)
      (Spec (.of P.field.k)) (CharP.cast_eq_zero P.Coefficient (ringChar P.Coefficient)) r)

/-- The finite signed module twist on an arbitrary k-scheme, by canonical pullback.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryEtaleModule (P : PurityFiniteSetting.{u}) {X : Scheme.{u}}
    (a : X ⟶ Spec (.of P.field.k)) (r : ℤ) :=
  (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).mapDerivedCategoryPlus.obj
    (P.a1OrdinaryBaseModuleComplex r)

/-- The etale-origin module twist on the small pro-etale site.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def a1OrdinaryProEtaleModule (P : PurityFiniteSetting.{u}) {X : Scheme.{u}}
    (a : X ⟶ Spec (.of P.field.k)) (r : ℤ) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategoryPlus.obj
    (P.a1OrdinaryEtaleModule a r)

/-- The unit comparison in the fixed coefficient module derived categories.
It uses the recorded canonical direct-image mate without forgetting the scalar action.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def A1OrdinaryModuleUnitsCompared (P : PurityFiniteSetting.{u}) {X : Scheme.{u}}
    (a : X ⟶ Spec (.of P.field.k)) (r : ℤ) : Prop :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategoryPlus.map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        (a1OrdinaryProjection X)).derivedPlus.unit.app (P.a1OrdinaryEtaleModule a r)) ≫
    (ProEtale.fixedComparisonDirectImageMatePlus P.Coefficient
      (a1OrdinaryProjection X)).app
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (a1OrdinaryProjection X)).mapDerivedCategoryPlus.obj (P.a1OrdinaryEtaleModule a r)) ≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (a1OrdinaryProjection X)).rightDerivedFunctorPlus.map
        ((ProEtale.fixedComparisonPullbackPlus P.Coefficient
          (a1OrdinaryProjection X)).hom.app (P.a1OrdinaryEtaleModule a r)) =
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
      (a1OrdinaryProjection X)).derivedPlus.unit.app (P.a1OrdinaryProEtaleModule a r)

/-- The complete ordinary affine-line assertion at a fixed base and two integer
degrees. Naturality in coefficients is part of the displayed natural transformations;
no arbitrary isomorphism or coefficient trivialization enters any map.
Source: blueprint sk-prop-a1-kummer, canonical units and pullbacks
(blueprint: lem-pur-affine-line-ordinary-invariance). -/
def A1OrdinaryInvarianceAt (P : PurityFiniteSetting.{u}) {X : Scheme.{u}}
    (a : X ⟶ Spec (.of P.field.k)) (q r : ℤ) : Prop :=
  P.A1OrdinaryModuleUnitsCompared a r ∧
  IsIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
    (a1OrdinaryProjection X)).derivedPlus.unit.app (P.a1OrdinaryEtaleModule a r)) ∧
  IsIso ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
    (a1OrdinaryProjection X)).derivedPlus.unit.app (P.a1OrdinaryProEtaleModule a r)) ∧
  IsIso ((Etale.a1OrdinaryAdjunction (a1OrdinaryProjection X)).unit.app
    ((a1OrdinaryEtaleFamily a).obj (P.a1OrdinaryBaseComplex r))) ∧
  IsIso ((ProEtale.a1OrdinaryAdjunction (a1OrdinaryProjection X)).unit.app
    ((a1OrdinaryProEtaleFamily a).obj (P.a1OrdinaryBaseComplex r))) ∧
  IsIso ((a1OrdinaryEtaleProjection a q).app (P.a1OrdinaryBaseComplex r)) ∧
  IsIso ((a1OrdinaryProEtaleProjection a q).app (P.a1OrdinaryBaseComplex r)) ∧
  ProEtale.a1OrdinaryUnitsCompared (a1OrdinaryProjection X)
    ((a1OrdinaryEtaleFamily a).obj (P.a1OrdinaryBaseComplex r)) ∧
  ((a1OrdinaryEtaleProjection a q).app (P.a1OrdinaryBaseComplex r) ≫
      (a1OrdinaryCohomologyComparison (a1OrdinaryProjection X ≫ a) q).app
        (P.a1OrdinaryBaseComplex r) =
    (a1OrdinaryCohomologyComparison a q).app (P.a1OrdinaryBaseComplex r) ≫
      (a1OrdinaryProEtaleProjection a q).app (P.a1OrdinaryBaseComplex r)) ∧
  IsIso ((a1OrdinaryCohomologyComparison a q).app (P.a1OrdinaryBaseComplex r)) ∧
  IsIso ((a1OrdinaryCohomologyComparison (a1OrdinaryProjection X ≫ a) q).app
    (P.a1OrdinaryBaseComplex r)) ∧
  (∀ (X' : Scheme.{u}) (v : X' ⟶ X),
    Etale.a1OrdinaryUnitNatural (a1OrdinaryProjectionSquare v)
      ((a1OrdinaryEtaleFamily a).obj (P.a1OrdinaryBaseComplex r)) ∧
    ProEtale.a1OrdinaryUnitNatural (a1OrdinaryProjectionSquare v)
      ((a1OrdinaryProEtaleFamily a).obj (P.a1OrdinaryBaseComplex r)) ∧
    a1OrdinaryEtaleBaseNatural v a q (P.a1OrdinaryBaseComplex r) ∧
    a1OrdinaryProEtaleBaseNatural v a q (P.a1OrdinaryBaseComplex r))

/-- Ordinary affine-line homotopy invariance for every positive finite coefficient level,
every signed twist, every integer cohomological degree, and every k-scheme.
The canonical units and pullbacks, rather than chosen endpoint isomorphisms, are invertible.
Source: blueprint main-20261015, sk-prop-a1-kummer, Reduction to a geometric fibre,
Coefficients, and Base change on Y; arbitrary-base refinement in the frame-independence
shear paragraph (blueprint: lem-pur-affine-line-ordinary-invariance).

Proof (the complete DAG proof):
1. Put $m=\ell^n$. In the valuation-ring description of [def-weil-l-adic-coefficient-extension],
$|\ell|_E=\ell^{-1}<1$, so $\ell\in\mathfrak m_E=(\varpi_E)$ and $mA=0$; $A$ is finite. Here is
an explicit reading of the finite twist in either topology. Put $M_T=\mathbf Z_\ell(1)_T$. By
[lem-pur-twist-sheaf-locally-free](2), $M_T\otimes_{\widehat{\mathbf Z}_{\ell,T}}(\mathbf
Z/m)_T\cong\mu_{m,T}$; clause (3) of the same node for $E=\mathbf Q_\ell$, $\varpi_E=\ell$ (so
that $\mathcal O_E(1)_T=M_T$ and $A_{E,n}=\mathbf Z/m$) identifies this with
$M_T\otimes_{(\mathbf Z_\ell)_T}(\mathbf Z/m)_T$, which is $M_T/mM_T$: the maps $u\otimes\bar
a\mapsto\overline{au}$ and $\bar u\mapsto u\otimes1$ are well defined, are inverse on pure
tensors, and commute with restriction, hence give inverse maps after sheafification in [def-pur-
sheaf-tensor-product]. Hence $M_T/mM_T\cong\mu_{m,T}$. From the tensors defining [def-
coefficient-twists-detailed], associativity and $mA=0$ give
$$A(1)_T\cong M_T\otimes_{\mathbf Z_\ell}A\cong(M_T/mM_T)\otimes_{\mathbf
Z/m}A\cong\mu_{m,T}\otimes_{\mathbf Z/m}A.$$
On the etale site use the finite Tate line and its signed tensor powers of [lem-asd-etale-
finite-twist-pullback]. Choose a primitive $m$-th root $\zeta\in k$ by [lem-sc-primitive-root].
On every $k$-scheme $T$, $a\mapsto\zeta^a$ identifies $(\mathbf Z/m)_T$ with $\mu_{m,T}$ in both
topologies: the factorization $z^m-1=\prod_a(z-\zeta^a)$ has pairwise unit differences, so every
root on an object $V$ is uniquely one of the $\zeta^a$ on a clopen partition of $V$. Conversely
such a locally constant choice gives a root. These descriptions commute with restriction. Thus
the same root identifies $A(1)_T$ with $A_T$, and its tensor powers and dual basis identify
every $A(r)_T$ with $A_T$, including $r=0$ and $r<0$. These auxiliary trivializations commute
with every $k$-morphism and with coefficient maps at this common annihilating level. For a map
between different finite coefficient levels, choose a common power $m$ annihilating both and its
primitive root; use the compatible power of that root at a smaller exponent. The exponent-
transition clause of [lem-asd-etale-finite-twist-pullback] identifies these finite descriptions.
They also identify the etale finite twist with its pro-etale inverse image. Only the test for
invertibility uses this choice; the map being tested is always the canonical unit.

2. First compute $R\Gamma(\mathbf A^1_k,B)$ for every finite abelian group $B$ killed by a power
of $\ell$. For $B=\mathbf Z/\ell$, apply [thm-pur-kummer-affine-line](1) with $N=1$ and free
coefficient module $\mathbf Z/\ell$; the root trivialization of step 1 identifies its twist with
this constant sheaf, with its degree-zero isomorphism the constants map. The zero group has zero
cohomology by the resolution definition [def-weil-pbc-sites-and-cohomology]. For any other $B$,
argue by induction on its cardinality: choose $x\ne0$ and the least $s\geq1$ with $\ell^s x=0$.
Then $y=\ell^{s-1}x$ has order $\ell$, $C=\langle y\rangle\cong\mathbf Z/\ell$, and $D=B/C$ has
smaller cardinality and is still killed by the same power $\ell^a$. The exact sequence $0\to
C\to B\to D\to0$, regarded as modules over the finite ring $\mathbf Z/\ell^a$, remains exact for
constant sheaves by [lem-constructible-constant-exact]. We use the underlying abelian sheaves:
the kernel and cokernel of a module-sheaf map carry the induced module actions, so forgetting
those actions preserves this short exact sequence. Apply the long exact sequence of [lem-weil-
pbc-right-derived-universal-delta-functor] to global sections. The vanishing for $C$ and the
induction hypothesis for $D$ give $H^q(\mathbf A^1_k,B)=0$ for $q>0$ and a short exact sequence
$0\to H^0(C)\to H^0(B)\to H^0(D)\to0$. In its comparison with $0\to C\to B\to D\to0$, the outer
constants maps are isomorphisms. The middle map is injective because an element mapping to zero
first maps to zero in $D$ and then comes from a zero element of $C$; it is surjective because a
section can first be matched in $D$ and its remaining difference then lifted from $C$. Hence
$B\to H^0(\mathbf A^1_k,B)$ is the constants isomorphism. The same induction proves that $|B|$
is a power of $\ell$: $|0|=1$, $|C|=\ell$, and $|B|=|C||D|$ by partitioning $B$ into the cosets
of $C$. In particular this holds for the additive group of every $A_{E,n}$; no freeness of $A$
over a cyclic coefficient ring and no divisibility of $n$ by the ramification index has been
assumed.

3. Let $\bar x$ be any geometric point of the arbitrary $k$-scheme $X$ and put
$S=\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{X,\bar x}$. The local polynomial description in
[def-sbc-affine-space] makes $p$ affine: over every affine open $\operatorname{Spec}R\subset X$
its inverse image is $\operatorname{Spec}R[t]$. It is therefore quasi-compact and quasi-
separated by [lem-weil-pbc-affine-morphism-permanence], regardless of whether $X$ is quasi-
compact, separated or Noetherian. Its strict-local base change is $\mathbf A^1_S$. Apply [prop-
weil-pbc-strict-henselization-stalk-formula] to the underlying torsion abelian sheaf $A$ to
identify
$$(Rp_*A)_{\bar x}\cong R\Gamma(\mathbf A^1_S,A).$$
This is the canonical restriction identification. On degree zero the stalk of the adjunction
unit is the constants map $A\to H^0(\mathbf A^1_S,A)$: in the formula for [def-weil-pbc-direct-
image] the unit restricts a locally constant section to the fibre product, and then to the
strict-local limit.

4. Write $f:\mathbf A^1_k\to\operatorname{Spec}k$, $g:S\to\operatorname{Spec}k$, $h:\mathbf
A^1_S\to\mathbf A^1_k$ and $e:\mathbf A^1_S\to S$. The square $fh=ge$ is Cartesian. Here $f$ is
smooth by [sbc-lem-affine-space-smooth]; $g$ is affine (source and target are affine), hence
qcqs by [lem-weil-pbc-affine-morphism-permanence]. The finite additive group of $A$ has
invertible order: it is killed by $\ell^n$, so its order is a power of $\ell$, whereas
$\operatorname{char}k=p\ne\ell$. Thus [sbc-thm-smooth-base-change] applies with its smooth side
$f$ and its qcqs side $g$, and gives $f^{-1}R^qg_*A\cong R^qh_*A$. By [sbc-lem-strict-henselian-
constant-cohomology], $H^0(S,A)=A$ by constants and $H^q(S,A)=0$ for $q>0$. The natural
constant-sheaf identification of [lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant],
also for abelian sheaves by transporting their group operations, identifies $R^qg_*A$ with the
constant sheaf of its sections over $\operatorname{Spec}k$, which are its stalk at the identity
geometric point. That stalk is $H^q(S,A)$ by [prop-weil-pbc-strict-henselization-stalk-formula]
for the qcqs $g$: the strict henselization of the separably closed field $k$ at the identity
point is $k$ itself, so the fibre product is $S$. Thus $R^qg_*A$ is the constant sheaf of the
groups $H^q(S,A)$. In degree zero the base-change map [sbc-def-base-change-map] carries a
constant section to that same constant section, by its counit transpose formula. Therefore the
canonical unit $A_{\mathbf A^1_k}\to Rh_*A$ induces an isomorphism on degree zero, and its
target has zero positive cohomology sheaves; negative cohomology is zero for a sheaf's right
derived direct image. The cohomology criterion [lem-weil-pbc-unbounded-derived-iso-cohomology]
makes this unit invertible. Applying derived sections and the etale composition formula (5) of
[lem-weil-derived-direct-image-composition] gives
$$h^*:R\Gamma(\mathbf A^1_k,A)\xrightarrow{\sim}R\Gamma(\mathbf A^1_S,A).$$
The map is pullback: the composition comparison is the canonical one, and on constants both
paths send $a$ to the constant section $a$. Step 2 now implies that $A\to H^0(\mathbf A^1_S,A)$
is an isomorphism and all its higher cohomology groups vanish.

5. By steps 3 and 4, at every geometric stalk the unit $A_X\to Rp_*A_{\mathbf A^1_X}$ is an
isomorphism on degree zero and both sides have zero cohomology in every other degree. Apply
[lemma-weil-pbc-geometric-stalk-conservative] to the cohomology-sheaf maps and then [lem-weil-
pbc-unbounded-derived-iso-cohomology] to conclude that it is invertible on the etale site. This
also proves the assertion in the fixed-ring module derived category: the canonical, unit-
compatible forgetful comparison in [lem-weil-pbc-module-abelian-derived-direct-image-comparison]
identifies the underlying unit with the one just tested. Forgetting coefficients detects an
isomorphism on each cohomology module sheaf (the inverse of a bijective module homomorphism is
module-linear), and hence detects the required derived isomorphism. Conjugate by the sheaf
trivializations of step 1. Naturality of the adjunction unit then gives precisely the same
result for the canonical map $A(r)_X\to Rp_*A(r)_{\mathbf A^1_X}$, for every signed integer $r$.

6. Transport the actual unit to the pro-etale site, with constant ring $A$ and the etale finite
twist as witness. Use the notation $A_T=\nu_T^*$, $l=p_{\mathrm{et}}^{-1}$,
$r=Rp_{\mathrm{et},*}$, $P=Lp_{\mathrm{proet}}^*$, $s=Rp_{\mathrm{proet},*}$, $a:A_{\mathbf
A^1_X}l\cong PA_X$ and $b:A_Xr\to sA_{\mathbf A^1_X}$ in [lem-weil-pbc-comparison-direct-image-
canonical-mate]. Its hypotheses hold because $p$ is qcqs and the input $lL$, $L=A(r)_X$, is in
degree zero. By that node $b$ is an isomorphism and is the transpose of $A_{\mathbf
A^1_X}(\varepsilon^e)a^{-1}$. Transposing
$$s(a_L)\circ b_{lL}\circ A_X(\eta^e_L):A_XL\longrightarrow sPA_XL$$
and using naturality of $a$ gives $A_{\mathbf A^1_X}(\varepsilon^e_{lL}\circ l\eta^e_L)$
conjugated by $a_L$, hence the identity by the etale triangle identity. This composite is
consequently the pro-etale unit $\eta^p_{A_XL}$, since an adjunction transpose is a bijection.
Every factor is invertible by step 5 and the cited comparison, so the pro-etale unit is
invertible. Step 1 identifies its coefficient object with the specified detailed finite twist.
This proves equality under comparison of the canonical unit maps, not merely existence of
abstract isomorphisms of their endpoints.

7. For the etale cohomology conclusion apply $R\Gamma(X,-)$ to the unit proved invertible in
step 5. Its target identifies canonically with $R\Gamma(\mathbf A^1_X,A(r))$. To see this at the
resolution level, take a bounded-below injective resolution $I$ on $\mathbf A^1_X$. By [prop-
weil-pbc-inverse-image-modules-exact] the inverse image is exact and left adjoint to $p_*$;
hence $p_*$ sends an injective to an injective, since lifting a morphism into $p_*I$ along a
monomorphism transposes to lifting into $I$ along its inverse-image monomorphism. Thus $p_*I$
computes both $Rp_*$ and its derived sections. The section complexes agree termwise by [def-
weil-pbc-direct-image], $\Gamma(X,p_*I)=\Gamma(\mathbf A^1_X,I)$. The resulting map is the
ordinary cohomology pullback, since the unit first pulls back sections and then maps to the
resolution. It is therefore an isomorphism in every degree. For the pro-etale cohomology
conclusion use the natural global comparison [lem-weil-pbc-comparison-global-cohomology] for
both $X$ and $\mathbf A^1_X$. It applies to arbitrary schemes and degree-zero etale twists with
finite ring $A$. Compatibility with pullback is the all-support case $C=X$ of [lem-pur-
supported-cup-functoriality]. In its commuting square the horizontal comparisons and the etale
vertical pullback are isomorphisms, so the pro-etale vertical pullback is an isomorphism as
well. For $q<0$ both groups are zero by the nonnegative injective resolution convention [def-
weil-pbc-sites-and-cohomology].

8. The isomorphisms obtained are always the canonical pullback maps, with no chosen-root factor
in their definition. Fix a $k$-morphism $v:X'\to X$. For completeness, naturality also holds for
the derived units themselves. Write $w=\mathbf A^1_v$, $p'=p_{X'}$, and $L=A(r)_X$. In the etale
topology let $\theta:p'^{-1}v^{-1}\xrightarrow{\sim}w^{-1}p_X^{-1}$ be the canonical inverse-
image square identification and let $\beta:v^{-1}Rp_{X,*}\to Rp'_*w^{-1}$ be the exchange map of
[sbc-def-base-change-map], applied with the sides of the projection square exchanged. Its
transpose is $w^{-1}\varepsilon_{p_X}\circ\theta_{Rp_{X,*}}$. Consequently the transpose of
$$Rp'_*(\theta_L^{-1})\circ\beta_{p_X^{-1}L}\circ v^{-1}(\eta_{p_X,L})$$
is
$$\theta_L^{-1}\circ w^{-1}(\varepsilon_{p_X,p_X^{-1}L}\circ
p_X^{-1}\eta_{p_X,L})\circ\theta_L=\operatorname{id}.$$
Naturality of $\theta$ gives the displayed equality, and the triangle identity gives its final
value. The composite is therefore exactly $\eta_{p',v^{-1}L}$. Both units are invertible by step
5, so this also makes the exchange map invertible on this coefficient object. For the pro-etale
etale-origin twists, [lem-weil-pbc-comparison-pullback] respects the chosen square
identification. Together with the named counit-mate normalization used in step 6, it identifies
the two exchange maps: their adjoint transposes are the same square identification followed by
the same counit. The identical unit equation follows by the injectivity of the adjunction
transpose. Thus the derived-unit isomorphisms, as well as their cohomology consequences, are
natural in $X$. For a $k$-morphism $v:X'\to X$, the square of projections satisfies
$p_X\circ\mathbf A^1_v=v\circ p_{X'}$. The identity-and-composition clauses of [lem-pur-
supported-cup-functoriality], with full support, therefore give $(\mathbf
A^1_v)^*p_X^*=p_{X'}^*v^*$ in both topologies, and that node also identifies these operations
under the canonical comparison. Naturality of the sheaf inverse-image unit [def-weil-pbc-
inverse-image], and the functorial resolution definition [def-weil-pbc-sites-and-cohomology],
give $p^*\circ H^q(u)=H^q(p^{-1}u)\circ p^*$ for every finite coefficient morphism $u$,
including quotient coefficient maps; no tensor-exactness or flatness of such a map is used. The
same statement on pro-etale sites follows either from the unit identity of step 6 or from the
natural comparison of [lem-weil-pbc-comparison-global-cohomology]. The inverse isomorphisms
inherit these commuting squares by composing with inverses. If $X$ is empty, its sheaf
cohomology groups and direct-image unit have zero source and target, so that case is included.
-/
theorem affineLineOrdinaryInvariance (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))] (q r : ℤ) :
    P.A1OrdinaryInvarianceAt (X ↘ Spec (.of P.field.k)) q r := by
  sorry

end WeilConjectures.PurityFiniteSetting
