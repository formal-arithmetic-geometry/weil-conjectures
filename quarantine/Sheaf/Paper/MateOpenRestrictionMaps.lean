/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.BrownExceptionalAdjoint
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.Compactification.BoundaryRefinement

/-! # The specified comparison maps for open restriction

Source: blueprint det-sf-mate-open-restriction, clauses (1)--(2).
These are the original maps, separated from the exceptional-adjoint theorem so that
its geometric compact-support comparison can be proved independently.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Restriction of the existing exact termwise inverse image to the recorded localizing
closures. The witness certifies membership only; no functor is chosen.
Source: blueprint det-sf-mate-open-restriction (1)
(blueprint: def-sfb-mate-open-restriction-maps). -/
def mateOpenPullback {U X : Scheme.{u}} (j : U ⟶ X)
    (h : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      localizingClosureProEtale Λ U ((upperStar Λ j).mapDerivedCategory.obj K.obj)) :
    (localizingClosureProEtale Λ X).FullSubcategory ⥤
      (localizingClosureProEtale Λ U).FullSubcategory :=
  (localizingClosureProEtale Λ U).lift
    ((localizingClosureProEtale Λ X).ι ⋙ (upperStar Λ j).mapDerivedCategory) h

/-- Restriction of actual levelwise extension by zero to the localizing closures.
Source: blueprint det-sf-mate-open-restriction (1)
(blueprint: def-sfb-mate-open-restriction-maps). -/
def mateOpenExtension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (h : ∀ K : (localizingClosureProEtale Λ U).FullSubcategory,
      localizingClosureProEtale Λ X
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K.obj)) :
    (localizingClosureProEtale Λ U).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory :=
  (localizingClosureProEtale Λ X).lift
    ((localizingClosureProEtale Λ U).ι ⋙
      (openImmersionLowerShriek Λ j).mapDerivedCategory) h

/-- Canonical composition of open extensions: the left-adjoint comparison of the exact
open adjunctions and the coefficient-compatible inverse-image compositor.
Source: blueprint det-sf-mate-open-restriction (2), composite adjunction calculation
(blueprint: def-sfb-mate-open-restriction-maps). -/
def mateOpenExtensionComp {U X Z : Scheme.{u}} (j : U ⟶ X) (i : X ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] :
    (openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ i).mapDerivedCategory ≅
      (openImmersionLowerShriek Λ (j ≫ i)).mapDerivedCategory :=
  Adjunction.leftAdjointUniq
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i))
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (j ≫ i)).ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso (upperStarComp Λ j i) ≪≫
        Functor.mapDerivedCategoryCompIso (upperStar Λ i) (upperStar Λ j)))

/-- The lower-shriek compositor when the first morphism is open, computed in the
compactification with the same proper map. This fixes the source comparison's normalization.
Source: blueprint det-sf-mate-open-restriction (2)
(blueprint: def-sfb-mate-open-restriction-maps). -/
def mateOpenSourceLowerShriek {U X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification Λ c ≅
      rightDerivedLowerShriekOfCompactification Λ (c.precomp j) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mateOpenExtensionComp Λ j c.i)
      (lowerStar Λ c.g).rightDerivedFunctor

/-- The ordinary restriction mate for a commutative proper/open square. It is defined
using only the coefficient-compatible pullback compositor and the direct-image counit.
Source: blueprint det-sf-mate-open-restriction (2), canonical comparison in the open square
(blueprint: def-sfb-mate-open-restriction-maps). -/
def mateOpenProperRestriction {Z Z' Y V : Scheme.{u}}
    {a : Z' ⟶ Z} {q : Z' ⟶ V} {p : Z ⟶ Y} {v : V ⟶ Y}
    (sq : CommSq a q p v)
    (B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (upperStar Λ v).mapDerivedCategory.obj ((lowerStar Λ p).rightDerivedFunctor.obj B) ⟶
      (lowerStar Λ q).rightDerivedFunctor.obj ((upperStar Λ a).mapDerivedCategory.obj B) :=
  ((derivedUpperStarLowerStarAdjunction Λ q).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ q)).homEquiv _ _
      (((Functor.mapDerivedCategoryCompIso (upperStar Λ v) (upperStar Λ q)).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          ((upperStarComp Λ q v).symm ≪≫
            eqToIso (congrArg (upperStar Λ) sq.w.symm) ≪≫ upperStarComp Λ a p) ≪≫
        Functor.mapDerivedCategoryCompIso (upperStar Λ p) (upperStar Λ a)).hom.app
          ((lowerStar Λ p).rightDerivedFunctor.obj B) ≫
        (upperStar Λ a).mapDerivedCategory.map
          (((derivedUpperStarLowerStarAdjunction Λ p).ofNatIsoLeft
            (leftDerivedUpperStarIsoMapDerivedCategory Λ p)).counit.app B))

/-- The open square identifies the two composites of extensions by zero. Its components
are fixed by the units of the open adjunctions, including the coefficient actions.
Source: blueprint det-sf-mate-open-restriction (2)
(blueprint: def-sfb-mate-open-restriction-maps). -/
def mateOpenSquareExtension {U X V Y : Scheme.{u}}
    {a : U ⟶ X} {q : U ⟶ V} {f : X ⟶ Y} {v : V ⟶ Y}
    [IsOpenImmersion a] [IsOpenImmersion v]
    (sq : IsPullback a q f v) (c : Compactification f) :
    (openImmersionLowerShriek Λ a).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ c.i).mapDerivedCategory ≅
      (openImmersionLowerShriek Λ (c.ofIsPullback sq).i).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ (pullback.fst c.g v)).mapDerivedCategory :=
  mateOpenExtensionComp Λ a c.i ≪≫
    Functor.mapDerivedCategoryNatIso
      (eqToIso (by
        congr 1
        exact (c.ofIsPullback_i_fst sq).symm)) ≪≫
    (mateOpenExtensionComp Λ (c.ofIsPullback sq).i (pullback.fst c.g v)).symm

/-- The specified component `v* Rf! u! M → Rf_V! M`: first identify the composite open
extensions, then apply the proper/open restriction mate, and undo the open unit on the
base-changed compactification. Thus this is a real map before invertibility is asserted.
Source: blueprint det-sf-mate-open-restriction (2), Cartesian open square
(blueprint: def-sfb-mate-open-restriction-maps). -/
def mateOpenTargetLowerShriek {U X V Y : Scheme.{u}}
    {a : U ⟶ X} {q : U ⟶ V} {f : X ⟶ Y} {v : V ⟶ Y}
    [IsOpenImmersion a] [IsOpenImmersion v]
    (sq : IsPullback a q f v) (c : Compactification f)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))) :
    (upperStar Λ v).mapDerivedCategory.obj
        ((rightDerivedLowerShriekOfCompactification Λ c).obj
          ((openImmersionLowerShriek Λ a).mapDerivedCategory.obj M)) ⟶
      (rightDerivedLowerShriekOfCompactification Λ (c.ofIsPullback sq)).obj M :=
  (upperStar Λ v).mapDerivedCategory.map
      ((lowerStar Λ c.g).rightDerivedFunctor.map
        ((mateOpenSquareExtension Λ sq c).hom.app M)) ≫
    mateOpenProperRestriction Λ (IsPullback.of_hasPullback c.g v).toCommSq
      ((openImmersionLowerShriek Λ (pullback.fst c.g v)).mapDerivedCategory.obj
        ((openImmersionLowerShriek Λ (c.ofIsPullback sq).i).mapDerivedCategory.obj M)) ≫
    (lowerStar Λ (pullback.snd c.g v)).rightDerivedFunctor.map
      (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ
        (pullback.fst c.g v)).unit.app
          ((openImmersionLowerShriek Λ (c.ofIsPullback sq).i).mapDerivedCategory.obj M)))

/-- The canonical identification of compact-support image for the trivial open
compactification (j,id) with levelwise extension by zero. The identity direct-image
identification is the derived one normalized on ordinary module sheaves.
Source: blueprint det-sf-mate-open-restriction (1), trivial compactification
(blueprint: def-sfb-mate-open-restriction-maps). -/
def mateOpenTrivialLowerShriek {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    rightDerivedLowerShriekOfCompactification Λ (Compactification.ofIsOpenImmersion j) ≅
      (openImmersionLowerShriek Λ j).mapDerivedCategory :=
  Functor.isoWhiskerLeft (openImmersionLowerShriek Λ j).mapDerivedCategory
      (refinementDerivedLowerStarId Λ X) ≪≫
    Functor.rightUnitor _

end AlgebraicGeometry.ProEtale.CondensedRing
