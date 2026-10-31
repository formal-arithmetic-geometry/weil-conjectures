/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization.OrdinaryAffineCounitTensorMaps
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection

/-! # Specified tensor actions on the ordered affine tower -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale
namespace OrdinaryAffineTensorActions

variable (A : Type (u + 1)) [CommRing A]

/-- The untwisted pullback along one compactified coordinate, before composing its
inverse-image comparison. Source: affine trace proof, ordered compactification
(blueprint: def-pur-ordinary-affine-tensor-actions). -/
abbrev linePull (S : Scheme.{u}) :=
  ordinaryFinitePullback A (ProjectiveLine S ↘ S) ⋙
    ordinaryFinitePullback A (ProjectiveLine.affineChart S)

/-- Pull the coefficient through the coordinate tower in the same order as its right
adjoint. Source: affine trace proof, coordinate order
(blueprint: def-pur-ordinary-affine-tensor-actions). -/
abbrev pull (S : Scheme.{u}) (d : ℕ) :=
  affineTraceRightTower (fun e ↦ linePull A (affineTraceTower S e)) d

/-- The symmetry conjugate of the inverse projection of the standard open chart.
Source: Stacks Tag 0GL1, with the specified signed symmetry
(blueprint: def-pur-ordinary-affine-tensor-actions). -/
def openAction (S : Scheme.{u}) (H : DerivedCategoryModule A (ProjectiveLine S))
    (M : DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S)) :
    ((ordinaryFiniteTensor A (ProjectiveLine S)).obj H).obj
        ((affineTraceOpenLeft A S).obj M) ⟶
      (affineTraceOpenLeft A S).obj
        (((ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} S)).obj
          ((ordinaryFinitePullback A (ProjectiveLine.affineChart S)).obj H)).obj M) :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) (ProjectiveLine S)).hom.app H).app _ ≫
    ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} A)
      (ProjectiveLine.affineChart S)).inv.app M).app H ≫
    (affineTraceOpenLeft A S).map
      (((derivedTensorSymmetry (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} S)).hom.app M).app _)

/-- Open tensor action as a natural transformation in the source complex.
Source: naturality of the open projection and signed symmetry
(blueprint: def-pur-ordinary-affine-tensor-actions). -/
def openActionNat (S : Scheme.{u}) (H : DerivedCategoryModule A (ProjectiveLine S)) :
    affineTraceOpenLeft A S ⋙ (ordinaryFiniteTensor A (ProjectiveLine S)).obj H ⟶
      (ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} S)).obj
        ((ordinaryFinitePullback A (ProjectiveLine.affineChart S)).obj H) ⋙
          affineTraceOpenLeft A S where
  app := openAction A S H
  naturality M M' f := by
    dsimp only [Functor.comp_map, ordinaryFiniteTensor]
    unfold openAction
    have hs := ((derivedTensorSymmetry (ModuleCat.{u + 1} A)
      (ProjectiveLine S)).hom.app H).naturality ((affineTraceOpenLeft A S).map f)
    have hp := NatTrans.naturality_app
      (derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} A)
        (ProjectiveLine.affineChart S)).inv H f
    have ht := NatTrans.naturality_app
      (derivedTensorSymmetry (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} S)).hom
      ((ordinaryFinitePullback A (ProjectiveLine.affineChart S)).obj H) f
    erw [reassoc_of% hs, reassoc_of% hp]
    erw [← (affineTraceOpenLeft A S).map_comp, ht,
      (affineTraceOpenLeft A S).map_comp]
    simp only [Category.assoc]
    rfl

/-- The proper ordered projection as a natural transformation in its source input.
Source: Stacks Tag 0B56, naturality of the specified adjoint-of-counit map
(blueprint: def-pur-ordinary-affine-tensor-actions). -/
def properActionNat (S : Scheme.{u}) (H : DerivedCategoryModule A S) :
    ordinaryFinitePushforward A (ProjectiveLine S ↘ S) ⋙
      (ordinaryFiniteTensor A S).obj H ⟶
    (ordinaryFiniteTensor A (ProjectiveLine S)).obj
      ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj H) ⋙
        ordinaryFinitePushforward A (ProjectiveLine S ↘ S) where
  app M := ordinaryFiniteProjection A _ M H
  naturality M M' f := by
    dsimp only [Functor.comp_map, ordinaryFiniteTensor]
    unfold ordinaryFiniteProjection
    have hs := ((derivedTensorSymmetry (ModuleCat.{u + 1} A) S).hom.app H).naturality
      ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map f)
    have hp := NatTrans.naturality_app
      (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A)
        (ProjectiveLine S ↘ S)) H f
    have ht := NatTrans.naturality_app
      (derivedTensorSymmetry (ModuleCat.{u + 1} A) (ProjectiveLine S)).hom
      ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj H) f
    erw [reassoc_of% hs, reassoc_of% hp]
    erw [← (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map_comp, ht,
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map_comp]
    simp only [Category.assoc]
    rfl

/-- The actual proper/open tensor action of one affine coordinate.
Source: affine trace proof, pasting the proper and open projection maps
(blueprint: def-pur-ordinary-affine-tensor-actions). -/
def lineActionNat (S : Scheme.{u}) (H : DerivedCategoryModule A S) :
    affineTraceLineLeft A S ⋙ (ordinaryFiniteTensor A S).obj H ⟶
      (ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} S)).obj
        ((linePull A S).obj H) ⋙ affineTraceLineLeft A S :=
  Functor.whiskerLeft (affineTraceOpenLeft A S) (properActionNat A S H) ≫
    Functor.whiskerRight
      (openActionNat A S ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj H))
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S))

/-- The coefficient tensor endofunctors along the ordered tower.
Source: affine trace proof, coefficient induction
(blueprint: def-pur-ordinary-affine-tensor-actions). -/
abbrev coefficient (S : Scheme.{u}) (H : DerivedCategoryModule A S) (d : ℕ) :=
  (ordinaryFiniteTensor A (affineTraceTower S d)).obj ((pull A S d).obj H)

/-- The pasted forward projection action on the ordered left functor.
Source: affine trace proof, successor composition of projection maps
(blueprint: def-pur-ordinary-affine-tensor-actions). -/
def action (S : Scheme.{u}) (H : DerivedCategoryModule A S) (d : ℕ) :
    affineTraceLeft A S d ⋙ coefficient A S H 0 ⟶
      coefficient A S H d ⋙ affineTraceLeft A S d :=
  affineTraceExchangeTower
    (fun e ↦ affineTraceLineLeft A (affineTraceTower S e))
    (fun e ↦ affineTraceLineLeft A (affineTraceTower S e))
    (coefficient A S H)
    (fun e ↦ lineActionNat A (affineTraceTower S e) ((pull A S e).obj H)) d

/-- The tensor strength of the projective-line right functor.
Source: strong inverse-image tensor comparison and associativity
(blueprint: def-pur-ordinary-affine-tensor-actions). -/
def properStrength (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u})
    (H K : DerivedCategoryModule A S) :
    ((ordinaryFiniteTensor A (ProjectiveLine S)).obj
      ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj H)).obj
        ((ordinaryFiniteP1Right A N hA S).obj K) ≅
      (ordinaryFiniteP1Right A N hA S).obj (((ordinaryFiniteTensor A S).obj H).obj K) :=
  (derivedTensorAssociator (ModuleCat.{u + 1} A) (ProjectiveLine S) _ _ _).symm ≪≫
    ordinaryFiniteTensorRightMapIso A (ProjectiveLine S)
      (ordinaryFiniteTensorPullback A (ProjectiveLine S ↘ S) H K).symm (Iso.refl _)

/-- The tensor strength of the open/projective right functor of one coordinate.
Source: affine trace proof, right-functor reassociation
(blueprint: def-pur-ordinary-affine-tensor-actions). -/
def lineStrength (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u})
    (H K : DerivedCategoryModule A S) :
    ((ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} S)).obj
      ((linePull A S).obj H)).obj ((affineTraceLineRight A N hA S).obj K) ≅
      (affineTraceLineRight A N hA S).obj (((ordinaryFiniteTensor A S).obj H).obj K) :=
  (ordinaryFiniteTensorPullback A (ProjectiveLine.affineChart S)
      ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj H)
      ((ordinaryFiniteP1Right A N hA S).obj K)).symm ≪≫
    (ordinaryFinitePullback A (ProjectiveLine.affineChart S)).mapIso
      (properStrength A N hA S H K)

/-- Paste the specified line strengths, retaining their coordinate order.
Source: affine trace proof, iterated right-functor tensor comparison
(blueprint: def-pur-ordinary-affine-tensor-actions). -/
def strength (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u})
    (H : DerivedCategoryModule A S) (d : ℕ) (K : DerivedCategoryModule A S) :
    (coefficient A S H d).obj ((affineTraceRight A N hA S d).obj K) ≅
      (affineTraceRight A N hA S d).obj ((coefficient A S H 0).obj K) :=
  affineTraceRightExchangeTower
    (fun e ↦ affineTraceLineRight A N hA (affineTraceTower S e))
    (fun e ↦ affineTraceLineRight A N hA (affineTraceTower S e))
    (coefficient A S H)
    (fun e M ↦ lineStrength A N hA (affineTraceTower S e) ((pull A S e).obj H) M) d K

end OrdinaryAffineTensorActions
end AlgebraicGeometry.Etale
