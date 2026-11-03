/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero

/-!
# Extension by zero in finite intrinsic-compatible coordinates

Source: Stacks Tags 04J0 and 09AE; blueprint order 1583
(blueprint: lem-cbc-proetale-extension-zero-base-change).
The published construction is reproduced through its smaller finite-coefficient interface:
its legacy umbrella imports duplicate the recorded intrinsic coefficient declarations.

## Main definitions

- `sfFixedDerivedBaseChange`: the ordinary derived direct-image mate.
- `sfFixedOpenExtensionBaseChange`: its underived extension-by-zero conjugate.
- `sfFixedDerivedOpenExtensionBaseChangeIso`: the termwise derived isomorphism in
  the node's direction, using `sfFixedOpenExtensionBaseChange_isIso`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
open Scheme

/-- The specified inverse-image square, obtained by composing the recorded pullbacks.
Source: Stacks Tag 09A5 (blueprint: lem-cbc-proetale-extension-zero-base-change). -/
noncomputable def sfFixedPullbackSquareIso (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) :
    sfFixedDerivedPullback A g ⋙ sfFixedDerivedPullback A f' ≅
      sfFixedDerivedPullback A f ⋙ sfFixedDerivedPullback A g' :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (upperStarCompIso (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.w.symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The ordinary direct-image exchange is the mate of the inverse-image square.
Source: Stacks Tags 09A5 and 0B65
(blueprint: lem-cbc-proetale-extension-zero-base-change). -/
noncomputable def sfFixedDerivedBaseChange (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) :
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor ⋙
        sfFixedDerivedPullback A g ⟶
      sfFixedDerivedPullback A g' ⋙
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f').rightDerivedFunctor :=
  mateEquiv
    (upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f').mapDerivedCategoryRightDerivedAdjunction
    (sfFixedPullbackSquareIso A sq).hom

/-- Underived extension-by-zero exchange: the conjugate of the direct-image mate.
Source: Stacks Tags 04J0 and 0B65
(blueprint: lem-cbc-proetale-extension-zero-base-change). -/
noncomputable def sfFixedOpenExtensionBaseChange (A : Type u) [CommRing A]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : CommSq gU j' j g) :
    upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) gU ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j' ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g :=
  (conjugateEquiv
    ((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g))
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) gU).comp
      (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j'))).symm
    (mateEquiv
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) gU)
      (upperStarCompIso (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.w).hom)

/-- The canonical extension-by-zero exchange is invertible for a cartesian open square.
Source: blueprint lem-cbc-proetale-extension-zero-base-change; Stacks Tag 04J0
(blueprint: lem-cbc-proetale-extension-zero-base-change).
Proof: localize both small pro-etale sites at the open immersions. The pullback of their
localization functors is identified by the cartesian square, and its site comparison is an
isomorphism. Hence weakly-etale direct-image base change is an isomorphism. Conjugating
under the two displayed pairs of adjunctions gives this extension-by-zero exchange. -/
theorem sfFixedOpenExtensionBaseChange_isIso (A : Type u) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback gU j' j g) :
    IsIso (sfFixedOpenExtensionBaseChange A sq.toCommSq) := by
  sorry

/-- Termwise derived extension-by-zero exchange, in the node's direction.
Source: Stacks Tag 015F (blueprint: lem-cbc-proetale-extension-zero-base-change). -/
noncomputable def sfFixedDerivedOpenExtensionBaseChangeIso (A : Type u) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback gU j' j g) :
    (openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        sfFixedDerivedPullback A g ≅
      sfFixedDerivedPullback A gU ⋙
        (openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j').mapDerivedCategory :=
  letI := sfFixedOpenExtensionBaseChange_isIso A sq
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (asIso (sfFixedOpenExtensionBaseChange A sq.toCommSq)).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _

end AlgebraicGeometry.ProEtale
