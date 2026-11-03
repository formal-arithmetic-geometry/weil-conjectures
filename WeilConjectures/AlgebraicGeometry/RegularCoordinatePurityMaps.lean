/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalTateCoprojectionCoherence
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import Mathlib.FieldTheory.Perfect
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothTwoLevelReduction
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCompactQuotientCocycle
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothOrdinaryTwistCocycle
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.EtaleScalarTensorComposition
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothProQuotientTransport
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothSiteRealizations
import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ExtendScalars
public import WeilConjectures.EtaleCohomology.TateTwist.Basic
public import WeilConjectures.EtaleCohomology.TateTwist.KummerLevelIndependence
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation

/-! # Canonical maps for coordinate orientation cancellation

The five original maps are moved verbatim from the coordinate-contraction module.
The additional maps extend the same tensor/counit purity and identity unitor to
arbitrary coefficients, and expose the inverse Tate evaluation and reassociation.
All data are actual composites of the published canonical maps.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/
sk-thm-regular.proof.md, Steps 1--2 and 4(iii)
(blueprint: def-pur-regular-coordinate-purity-maps).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The actual finite-root line, compared with the concrete Tate datum by the
scalar-extension adjunction and the canonical root-power map. No basis is chosen.
Source: finite coefficient twists, used in Step 1
(blueprint: lem-pur-regular-coordinate-comparison-contraction). -/
def regularRootTateIso
    (A : Type (u + 1)) [CommRing A] [NeZero (ringChar A)]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u})
    [HasInvertibleExponent A T] (hT : IsUnit (N : Γ(T, ⊤))) :
    (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧ ≅ shiftedTateObject A T 1 :=
  (shiftFunctor _ (2 : ℤ)).mapIso
    ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
      (finiteEtaleLineAbIso T N A hA ≪≫
        extendScalarsRootsOfUnityIsoTateTwistSheaf A N hA hT) ≪≫
      (tateTwistObjectIsoSingleFunctor A T 1).symm)

/-- Ordered positive finite-root powers with their canonical Tate-addition constraints.
Source: finite coefficient twists and Step 1
(blueprint: lem-pur-regular-coordinate-comparison-contraction). -/
def regularLineTateIso
    (A : Type (u + 1)) [CommRing A] [NeZero (ringChar A)]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u})
    [HasInvertibleExponent A T] (hT : IsUnit (N : Γ(T, ⊤))) :
    (d : ℕ) → FiniteSmoothPurity.line A N hA T d ≅ shiftedTateObject A T (d : ℤ)
  | 0 => singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T ≪≫
      (shiftedTateZeroIso A T).symm
  | d + 1 =>
      ((derivedTensor (ModuleCat.{u + 1} A) T).mapIso
        (regularLineTateIso A N hA T hT d)).app _ ≪≫
      ((derivedTensor (ModuleCat.{u + 1} A) T).obj
        (shiftedTateObject A T (d : ℤ))).mapIso (regularRootTateIso A N hA T hT) ≪≫
      shiftTateObjectAddIso A T (d : ℤ) 1 ≪≫
      eqToIso (by simp only [Nat.cast_add, Nat.cast_one]; rfl)

/-- The specified tensor construction of smooth purity at the coefficient unit.
The source is identified by the canonical pullback-unit and tensor-unit maps.
Invertibility of the tensor mate is a conclusion of smooth tensor duality, rather
than an additional hypothesis. Source: def-pur-smooth-purity-map, Step 1
(blueprint: lem-pur-regular-coordinate-comparison-contraction). -/
def regularSmoothUnitPurityIso
    (A : Type (u + 1)) [CommRing A] [Finite A] [NeZero (ringChar A)]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    [HasInvertibleExponent A X] (hY : IsUnit (N : Γ(Y, ⊤))) :
    shiftedTateObject A X (d : ℤ) ≅
      (rightDerivedUpperShriek A f).obj (constantComplex A Y) := by
  have hX : IsUnit (N : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hY.map f.appTop.hom
  let α := regularDiagonalOrientation A N hN hA f d hX
  let K := constantComplex A Y
  haveI : IsIso (smoothTensorDualityMap A f (isIso_projectionMap_of_finite A f) K) :=
    (smooth_tensor_duality A N hN hA
      (fun y ↦ by
        simpa only [map_natCast] using hY.map (Y.presheaf.germ ⊤ y trivial).hom) f d).2 K
  let γ := FiniteSmoothPurity.gamma A f (shiftedTateObject A X (d : ℤ)) α K
  haveI : IsIso γ := by
    dsimp only [γ, FiniteSmoothPurity.gamma]
    infer_instance
  exact (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X _).symm ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      (leftDerivedUpperStarConstantComplexIso A f).symm).app _ ≪≫
    asIso γ

/-- Equality transport followed by the canonical exceptional identity unitor, with
no comparison-site counit assumption. Source: Step 3 and the identity clause of Step 6
(blueprint: lem-pur-regular-coordinate-comparison-contraction). -/
def regularExceptionalIdentityUnitor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (B : Scheme.{u}) (f : B ⟶ B) [HasCompactification f] (hf : f = 𝟙 B) :
    (rightDerivedUpperShriek A f).obj (constantComplex A B) ≅ constantComplex A B := by
  subst f
  exact (rightDerivedUpperShriekIdIso A B).app (constantComplex A B)

/-- The tensor/counit purity isomorphism at an arbitrary coefficient complex.
Source: sk-thm-smooth-purity, tensor construction used in Step 4(iii)
(blueprint: def-pur-regular-coordinate-purity-maps). -/
def regularSmoothTensorPurityIso
    (A : Type (u + 1)) [CommRing A] [Finite A] [NeZero (ringChar A)]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    [HasInvertibleExponent A X] (hY : IsUnit (N : Γ(Y, ⊤)))
    (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((ordinaryFinitePullback A f).obj K)).obj
        (shiftedTateObject A X (d : ℤ)) ≅ (rightDerivedUpperShriek A f).obj K := by
  have hX : IsUnit (N : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hY.map f.appTop.hom
  haveI : IsIso (smoothTensorDualityMap A f (isIso_projectionMap_of_finite A f) K) :=
    (smooth_tensor_duality A N hN hA
      (fun y ↦ by
        simpa only [map_natCast] using hY.map (Y.presheaf.germ ⊤ y trivial).hom) f d).2 K
  let γ := FiniteSmoothPurity.gamma A f (shiftedTateObject A X (d : ℤ))
    (regularDiagonalOrientation A N hN hA f d hX) K
  haveI : IsIso γ := by
    dsimp only [γ, FiniteSmoothPurity.gamma]
    infer_instance
  exact asIso γ

/-- Naturality of the constructed purity map in its coefficient complex.
This is the tensor/counit naturality used before cancelling the base orientation.
Source: sk-thm-regular, Step 4(iii), smooth-purity composition and naturality
(blueprint: def-pur-regular-coordinate-purity-maps). -/
theorem regularSmoothTensorPurityIso_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A] [NeZero (ringChar A)]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    [HasInvertibleExponent A X] (hY : IsUnit (N : Γ(Y, ⊤)))
    {K K' : DerivedCategoryModule A Y} (a : K ⟶ K') :
    ((derivedTensor (ModuleCat.{u + 1} A) X).map
      ((ordinaryFinitePullback A f).map a)).app (shiftedTateObject A X (d : ℤ)) ≫
        (regularSmoothTensorPurityIso A N hN hA f d hY K').hom =
      (regularSmoothTensorPurityIso A N hN hA f d hY K).hom ≫
        (rightDerivedUpperShriek A f).map a := by
  have hX : IsUnit (N : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hY.map f.appTop.hom
  exact FiniteSmoothPurity.ordinaryGammaNaturality A f _
    (regularDiagonalOrientation A N hN hA f d hX) a

/-- Split the source Tate line, then apply the actual tensor/counit purity map.
This is purity at the base orientation line, before cancelling that line.
Source: sk-thm-regular, Step 4(iii)
(blueprint: def-pur-regular-coordinate-purity-maps). -/
def regularPurityAtTateIso
    (A : Type (u + 1)) [CommRing A] [Finite A] [NeZero (ringChar A)]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    [HasInvertibleExponent A X] [HasInvertibleExponent A Y]
    (hY : IsUnit (N : Γ(Y, ⊤))) (m : ℕ) :
    shiftedTateObject A X ((m + d : ℕ) : ℤ) ≅
      (rightDerivedUpperShriek A f).obj (shiftedTateObject A Y m) :=
  eqToIso (by simp only [Nat.cast_add]; rfl) ≪≫
    (shiftTateObjectAddIso A X (m : ℤ) (d : ℤ)).symm ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      (leftDerivedUpperStarTateShiftIso A f (m : ℤ)).symm).app _ ≪≫
    regularSmoothTensorPurityIso A N hN hA f d hY (shiftedTateObject A Y m)

/-- The identity exceptional unitor on all coefficients, using equality elimination.
Its component at the coefficient unit is `regularExceptionalIdentityUnitor`.
Source: Step 3 of the contraction argument
(blueprint: def-pur-regular-coordinate-purity-maps). -/
def regularExceptionalIdentityNatIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (B : Scheme.{u}) (f : B ⟶ B) [HasCompactification f] (hf : f = 𝟙 B) :
    rightDerivedUpperShriek A f ≅ 𝟭 (DerivedCategoryModule A B) := by
  subst f
  exact rightDerivedUpperShriekIdIso A B

/-- The natural identity unitor has the original specified unit component.
Source: equality elimination in the definition
(blueprint: def-pur-regular-coordinate-purity-maps). -/
theorem regularExceptionalIdentityNatIso_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (B : Scheme.{u}) (f : B ⟶ B) [HasCompactification f] (hf : f = 𝟙 B) :
    (regularExceptionalIdentityNatIso A B f hf).app (constantComplex A B) =
      regularExceptionalIdentityUnitor A B f hf := by
  subst f
  rfl

/-- The exceptional section unitor as a natural isomorphism on all coefficients.
It is the inverse of the canonical compositor followed by equality transport and
by the exceptional identity unitor. Source: Step 3 of the contraction argument
(blueprint: def-pur-regular-coordinate-purity-maps). -/
def regularExceptionalSectionUnitor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X B : Scheme.{u}} (p : X ⟶ B) (z : B ⟶ X)
    [HasCompactification p] [HasCompactification z] [HasCompactification (z ≫ p)]
    [QuasiCompact z] [QuasiCompact (z ≫ p)] (hz : z ≫ p = 𝟙 B) :
    rightDerivedUpperShriek A p ⋙ rightDerivedUpperShriek A z ≅
      𝟭 (DerivedCategoryModule A B) :=
  (WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition A z p).symm ≪≫
    regularExceptionalIdentityNatIso A B (z ≫ p) hz

/-- The specified inverse Tate evaluation, directed out of the tensor unit.
Source: Step 2 of the regular dualizing cancellation construction
(blueprint: def-pur-regular-coordinate-purity-maps). -/
def regularInverseTateEvaluation
    (A : Type (u + 1)) [CommRing A] [Finite A] [HasTateTwist A]
    (B : Scheme.{u}) [HasInvertibleExponent A B] (m : ℤ) :
    constantComplex A B ≅ ((derivedTensor (ModuleCat.{u + 1} A) B).obj
      (shiftedTateObject A B m)).obj (shiftedTateObject A B (-m)) :=
  (shiftedTateZeroIso A B).symm ≪≫
    eqToIso (by simp [shiftedTateObject]) ≪≫
    (shiftTateObjectAddIso A B m (-m)).symm

/-- Reassociate and add the two Tate factors after tensoring by the inverse base twist.
Source: Step 2 of the regular dualizing cancellation construction
(blueprint: def-pur-regular-coordinate-purity-maps). -/
def regularCancelBaseTateIso
    (A : Type (u + 1)) [CommRing A] [Finite A] [HasTateTwist A]
    (B : Scheme.{u}) [HasInvertibleExponent A B]
    (L : DerivedCategoryModule A B) (m c : ℕ) :
    ((derivedTensor (ModuleCat.{u + 1} A) B).obj
      (((derivedTensor (ModuleCat.{u + 1} A) B).obj L).obj
        (shiftedTateObject A B ((m + c : ℕ) : ℤ)))).obj
          (shiftedTateObject A B (-(m : ℤ))) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) B).obj L).obj
        (shiftedTateObject A B (c : ℤ)) :=
  derivedTensorAssociator (ModuleCat.{u + 1} A) B L
      (shiftedTateObject A B ((m + c : ℕ) : ℤ)) (shiftedTateObject A B (-(m : ℤ))) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) B).obj L).mapIso
      (shiftTateObjectAddIso A B ((m + c : ℕ) : ℤ) (-(m : ℤ))) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) B).obj L).mapIso
      (eqToIso (by simp [Nat.cast_add, shiftedTateObject]))

end AlgebraicGeometry.Etale
