/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Paper.OrientationEtaleCoefficientTwists
public import Sheaf.Paper.PurityFiniteExceptionalComposition
public import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
public import Sheaf.AlgebraicGeometry.AffineTraceConstruction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-!
# Coherent six-functor orientations

Source: main-20261015, sec-six-functors/sk-def-sf-orientation/def-sf-orientation.md
(blueprint: def-sf-orientation-etale-family).

The two comparison arrows below are counit transposes. In particular, an
orientation never supplies an arbitrary replacement for either arrow.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

/-- The canonical affine-line integration: comparison with the standard
projective compactification, Rq_* of the open counit, then the normalized P1 trace.
It applies to a Noetherian base without a separatedness hypothesis.
Source: clause 4 (blueprint: def-sf-orientation-etale-family). -/
def sfOrientationAffineTrace (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤)))
    [HasCompactification (AffineSpace PUnit.{u + 1} Y ↘ Y)] :=
  (Etale.rightDerivedLowerShriekOfCompactificationIso A
    (HasCompactification.compactification (AffineSpace PUnit.{u + 1} Y ↘ Y))
    (affineTraceLineCompactification Y)).hom.app _ ≫
    (Etale.ordinaryFinitePushforward A (ProjectiveLine Y ↘ Y)).map
      ((Etale.affineTraceOpenLeft A Y).map
        (Etale.ordinaryFiniteShiftedLinePullback A N hA
          (Etale.projectiveLineTraceTransport N hN A hA) (ProjectiveLine.affineChart Y)
          (affineTraceProjectiveInvertible N Y hY)).inv ≫
        (Etale.affineTraceOpenAdjunction A Y).counit.app
          ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine Y))⟦(2 : ℤ)⟧)) ≫
    Etale.projectiveLineTrace N hN A hA Y hY ≫
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom

/-- Finite ordinary-etale components and their geometric equations. The tensor
and base-change arrows are the specified projection/counit transposes, and the
compositor is the adjunction conjugate of compact-support composition.
Source: finite-etale family and clauses 1--2 (blueprint: def-sf-orientation-etale-family). -/
structure SfFiniteEtaleOrientation (D : FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hunit : ∀ X : SixFunctorSpace D, IsUnit (N : Γ(X.obj.left, ⊤))) where
  component : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    [HasCompactification f.hom.left],
    sfOrientationEtaleLine A N hA X.obj.left d ≅
      Etale.dualizingComplex (ModuleCat.{u + 1} A) f.hom.left
  baseChange : ∀ (Q : SixFunctorCompactifiedSquare D)
    [IsSeparated Q.g.hom.left] [IsSeparated Q.f.hom.left]
    [IsSeparated Q.f'.hom.left] [QuasiCompact Q.f'.hom.left]
    [HasCompactification Q.f.hom.left] [HasCompactification Q.f'.hom.left]
    (d : ℕ) [SmoothOfRelativeDimension d Q.f.hom.left]
    [SmoothOfRelativeDimension d Q.f'.hom.left],
    (component Q.f' d).hom =
      (sfOrientationEtaleLinePullback A N hN hA Q.g'.hom.left
        (hunit Q.X') (hunit Q.X) d).inv ≫
      ((Etale.upperStar (ModuleCat.{u + 1} A) Q.g'.hom.left).leftDerivedFunctor).map
        (component Q.f d).hom ≫ Etale.dualizingComplexBaseChangeMap A Q.square
  composition : ∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [IsSeparated g.hom.left]
    [IsSeparated (f ≫ g).hom.left]
    [QuasiCompact f.hom.left] [QuasiCompact (f ≫ g).hom.left]
    [QuasiCompact (f.hom.left ≫ g.hom.left)]
    [HasCompactification f.hom.left] [HasCompactification g.hom.left]
    [HasCompactification (f ≫ g).hom.left]
    [HasCompactification (f.hom.left ≫ g.hom.left)] (d e : ℕ)
    [SmoothOfRelativeDimension d f.hom.left] [SmoothOfRelativeDimension e g.hom.left]
    [SmoothOfRelativeDimension (d + e) (f ≫ g).hom.left],
    (component (f ≫ g) (d + e)).hom =
      (sfOrientationEtaleProduct A N hN hA X.obj.left (hunit X) d e).inv ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X.obj.left).obj
        (sfOrientationEtaleLine A N hA X.obj.left d)).map
          (sfOrientationEtaleLinePullback A N hN hA f.hom.left
            (hunit X) (hunit Y) e).inv ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X.obj.left).map
        (component f d).hom).app
          (((Etale.upperStar (ModuleCat.{u + 1} A) f.hom.left).leftDerivedFunctor).obj
            (sfOrientationEtaleLine A N hA Y.obj.left e)) ≫
      Etale.dualizingComplexTensorMap A f.hom.left
        (sfOrientationEtaleLine A N hA Y.obj.left e) ≫
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) f.hom.left).map
        (component g e).hom ≫
      (PurityFiniteSetting.finiteExceptionalComposition A f.hom.left g.hom.left).inv.app
        (𝟙_ (Etale.DerivedCategoryModule A Z.obj.left))


  affineLine : ∀ (X Y : SixFunctorSpace D) (f : X ⟶ Y)
    [IsSeparated f.hom.left] [SmoothOfRelativeDimension 1 f.hom.left]
    [HasCompactification f.hom.left] [IsNoetherian Y.obj.left]
    [HasCompactification (AffineSpace PUnit.{u + 1} Y.obj.left ↘ Y.obj.left)],
    X.obj.left = AffineSpace PUnit.{u + 1} Y.obj.left →
    HEq f.hom.left (AffineSpace PUnit.{u + 1} Y.obj.left ↘ Y.obj.left) →
    HEq ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f.hom.left).map
      (component f 1).hom ≫
        (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f.hom.left).counit.app
          (𝟙_ (Etale.DerivedCategoryModule A Y.obj.left)))
      (sfOrientationAffineTrace A N hN hA Y.obj.left (hunit Y))

end WeilConjectures
