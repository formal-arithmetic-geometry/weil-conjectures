/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteAdjunctionCoordinates
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Native.IntegralNativeOpenComparison
public import WeilConjectures.AlgebraicGeometry.StrictTower.MateEvaluationScalars.TowerMateEvaluationScalars

/-! # Coordinates for one native finite coefficient category

Source: Stacks 00YV, 03DI and 07A7; finite coefficient realization in
prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-finite-native-alpha-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralSystemRealization.FiniteCoordinates

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf presheafToSheaf Functor.leftAdjoint
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local implicit_reducible] StrictTower.modulePullback

variable (A : Type u) [CommRing A] [Finite A]

/-- Cancel the intrinsic coefficient presentation after the native inverse image.
Source: Stacks 00YV and 03DI; coefficient step of the finite alpha comparison.
(blueprint: lem-sf-finite-native-alpha-coordinates). -/
def finiteNativePullCoordinates {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (StrictTower.modulePullback (ULift.{u + 1} A) f).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence X A).inverse ≅
      (sfIntrinsicDerivedEquivalence Y A).inverse ⋙ ProperOpenPull (ULift.{u + 1} A) f :=
  Functor.mapDerivedCategorySquareIso
    (Functor.isoWhiskerRight (openSquarePullbackModel A f)
        (sfIntrinsicModuleEquivalence X A).inverse ≪≫
      Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence Y A).inverse
        (Functor.isoWhiskerLeft (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
          (sfIntrinsicModuleEquivalence X A).unitIso.symm) ≪≫
      Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence Y A).inverse
        (Functor.rightUnitor _)) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicDerivedEquivalence Y A).inverse
      (leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).symm

/-- Cancel the intrinsic coefficient presentation after native extension by zero.
Source: Stacks 00YV and 03DI; coefficient step of the finite alpha comparison.
(blueprint: lem-sf-finite-native-alpha-coordinates). -/
def finiteNativeShriekCoordinates {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (StrictTower.moduleJ (ULift.{u + 1} A) j).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Y A).inverse ≅
      (sfIntrinsicDerivedEquivalence X A).inverse ⋙ ProperOpenShriek (ULift.{u + 1} A) j :=
  Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso (compactSupportOpenModel j A))
      (sfIntrinsicDerivedEquivalence Y A).inverse ≪≫
    (let R := sfIntrinsicDerivedEquivalence X A
     let S := sfIntrinsicDerivedEquivalence Y A
     let F := ProperOpenShriek (ULift.{u + 1} A) j
     let G := (sfIntrinsicExtensionByZero j A).mapDerivedCategory
     let q := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
       Functor.mapDerivedCategoryNatIso (sfIntrinsicOpenExtensionComparison A j) ≪≫
         Functor.mapDerivedCategoryCompIso _ _
     (Functor.leftUnitor _).symm ≪≫
       Functor.isoWhiskerRight R.counitIso.symm (G ⋙ S.inverse) ≪≫
       Functor.associator _ _ _ ≪≫
       Functor.isoWhiskerLeft R.inverse (Functor.associator _ _ _).symm ≪≫
       Functor.isoWhiskerLeft R.inverse (Functor.isoWhiskerRight q S.inverse) ≪≫
       Functor.isoWhiskerLeft R.inverse (Functor.associator _ _ _) ≪≫
       Functor.isoWhiskerLeft R.inverse (Functor.isoWhiskerLeft F S.unitIso.symm) ≪≫
       Functor.isoWhiskerLeft R.inverse (Functor.rightUnitor F))

/-- The single-coefficient clopen alpha in its fixed sheaf presentation.

Source: Stacks 00YV, 03DI and 0F7B; the coefficient-equivalence step of
lem-sf-system-finite-alpha-coordinates.
Proof: before localization, both pull comparisons are inverse mates of the
section-preserving direct comparisons. Both open comparisons are their inverse
open mates. The cartesian beta therefore has the same open transpose in the two
presentations. The coefficient equivalence preserves the identity on the clopen
component and zero on its complement, so preserves the projector. Its unit and
counit identify the pull and open compositors. Paste these identities in the
ordinary alpha word. Apply the exact cochain functors and localization, inserting
the standard composition isomorphisms. The total-to-exact pull comparisons give
properOpenAlpha by ordinary_alpha_localized. Naturality and the equivalence
triangle identities give exactly the displayed inverse-coordinate formula.
Empty components and the zero ring use the same identity/zero calculation.
(blueprint: lem-sf-finite-native-alpha-coordinates). -/
theorem finiteNativeAlphaCoordinates
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : DerivedCategory (StrictTower.Modules (ULift.{u + 1} A) W)) :
    (sfIntrinsicDerivedEquivalence V A).inverse.map
        ((StrictTower.MateEvaluationScalars.singleDerivedAlpha
          (ULift.{u + 1} A) k r p i h).app M) ≫
      (finiteNativeShriekCoordinates A k).hom.app
        ((StrictTower.modulePullback (ULift.{u + 1} A) r).mapDerivedCategory.obj M) ≫
      (ProperOpenShriek (ULift.{u + 1} A) k).map
        ((finiteNativePullCoordinates A r).hom.app M) =
    (finiteNativePullCoordinates A p).hom.app
        ((StrictTower.moduleJ (ULift.{u + 1} A) i).mapDerivedCategory.obj M) ≫
      (ProperOpenPull (ULift.{u + 1} A) p).map
        ((finiteNativeShriekCoordinates A i).hom.app M) ≫
      (properOpenAlpha (ULift.{u + 1} A) k r p i h).app
        ((sfIntrinsicDerivedEquivalence W A).inverse.obj M) := by
  sorry

end WeilConjectures.IntegralSystemRealization.FiniteCoordinates
