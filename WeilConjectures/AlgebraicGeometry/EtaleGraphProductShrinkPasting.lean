/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphProductAmbientPasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkLift
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkSquare

/-! # Shrinking the three supports in the product interchange grid

Source: Stacks Project, Tag 0F7J.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

/-- Shrinking the three supporting neighborhoods commutes with the fixed product boundary.
The source and target are the already enlarged proper ambient products: this assertion
contains neither the original supplied square exchange nor a proper-ambient lambda
(Stacks, Tags 0F7C, 0F7D and 0F7J). -/
theorem etaleGraphProductShrinkPasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d₁ d₂ : EtaleGraphInterchangeDiagram f g) (second : Bool) :
    (match second with
    | false =>
      let sf := EtaleGraphPresentation.ProductRow.shrinkLambda
        d₁.sourcePresentation d₂.sourcePresentation false A
      let sg := EtaleGraphPresentation.ProductRow.shrinkLambda
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) false A
      let sh := EtaleGraphPresentation.ProductRow.shrinkLambda
        d₁.compositePresentation d₂.compositePresentation false A
      (EtaleGraphInterchangeDiagram.ProductRow.First.interchange d₁ d₂ A).hom ≫ sh.hom =
        Functor.whiskerRight sf.hom
            ((EtaleGraphInterchangeDiagram.ProductRow.First.G d₁ d₂).functor A) ≫
          Functor.whiskerLeft ((d₁.productF d₂).functor A) sg.hom ≫
          (d₁.productInterchange d₂ A).hom
    | true =>
      let sf := EtaleGraphPresentation.ProductRow.shrinkLambda
        d₁.sourcePresentation d₂.sourcePresentation true A
      let sg := EtaleGraphPresentation.ProductRow.shrinkLambda
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) true A
      let sh := EtaleGraphPresentation.ProductRow.shrinkLambda
        d₁.compositePresentation d₂.compositePresentation true A
      (EtaleGraphInterchangeDiagram.ProductRow.Second.interchange d₁ d₂ A).hom ≫ sh.hom =
        Functor.whiskerRight sf.hom
            ((EtaleGraphInterchangeDiagram.ProductRow.Second.G d₁ d₂).functor A) ≫
          Functor.whiskerLeft ((d₁.productF d₂).functor A) sg.hom ≫
          (d₁.productInterchange d₂ A).hom
    ) := by
  have h (b : Bool) :
      (EtaleGraphInterchangeDiagram.ProductShrink.liftBoundary d₁ d₂ b A).hom ≫
          (EtaleGraphInterchangeDiagram.ProductShrink.squareInterchange d₁ d₂ b A).hom ≫
          (EtaleGraphInterchangeDiagram.ProductShrink.compositeShrink d₁ d₂ b A).hom =
        (EtaleGraphInterchangeDiagram.ProductShrink.inputBoundary d₁ d₂ b A).hom ≫
          (EtaleGraphInterchangeDiagram.ProductShrink.productLiftBoundary d₁ d₂ A).hom ≫
          (d₁.productSquareInterchange d₂ A).hom := by
    rw [etaleGraphProductShrinkSquare A d₁ d₂ b, ← Category.assoc,
      etaleGraphProductShrinkLift A d₁ d₂ b, Category.assoc]
  cases second
  · simpa only [EtaleGraphInterchangeDiagram.ProductShrink.liftBoundary,
      EtaleGraphInterchangeDiagram.ProductShrink.liftInterchange,
      EtaleGraphInterchangeDiagram.ProductShrink.squareInterchange,
      EtaleGraphInterchangeDiagram.ProductShrink.inputBoundary,
      EtaleGraphInterchangeDiagram.ProductShrink.productLiftBoundary,
      EtaleGraphInterchangeDiagram.ProductShrink.sourceShrink,
      EtaleGraphInterchangeDiagram.ProductShrink.middleShrink,
      EtaleGraphInterchangeDiagram.ProductShrink.compositeShrink,
      EtaleGraphInterchangeDiagram.ProductShrink.F,
      EtaleGraphInterchangeDiagram.ProductShrink.G,
      EtaleGraphInterchangeDiagram.ProductShrink.H,
      EtaleGraphInterchangeDiagram.ProductRow.First.F,
      EtaleGraphInterchangeDiagram.ProductRow.First.G,
      EtaleGraphInterchangeDiagram.ProductRow.First.H,
      EtaleGraphInterchangeDiagram.ProductRow.Second.F,
      EtaleGraphInterchangeDiagram.ProductRow.Second.G,
      EtaleGraphInterchangeDiagram.ProductRow.Second.H,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      EtaleGraphInterchangeDiagram.ProductRow.First.interchange,
      EtaleGraphInterchangeDiagram.productInterchange, Iso.trans_hom, Category.assoc]
      using h false
  · simpa only [EtaleGraphInterchangeDiagram.ProductShrink.liftBoundary,
      EtaleGraphInterchangeDiagram.ProductShrink.liftInterchange,
      EtaleGraphInterchangeDiagram.ProductShrink.squareInterchange,
      EtaleGraphInterchangeDiagram.ProductShrink.inputBoundary,
      EtaleGraphInterchangeDiagram.ProductShrink.productLiftBoundary,
      EtaleGraphInterchangeDiagram.ProductShrink.sourceShrink,
      EtaleGraphInterchangeDiagram.ProductShrink.middleShrink,
      EtaleGraphInterchangeDiagram.ProductShrink.compositeShrink,
      EtaleGraphInterchangeDiagram.ProductShrink.F,
      EtaleGraphInterchangeDiagram.ProductShrink.G,
      EtaleGraphInterchangeDiagram.ProductShrink.H,
      EtaleGraphInterchangeDiagram.ProductRow.First.F,
      EtaleGraphInterchangeDiagram.ProductRow.First.G,
      EtaleGraphInterchangeDiagram.ProductRow.First.H,
      EtaleGraphInterchangeDiagram.ProductRow.Second.F,
      EtaleGraphInterchangeDiagram.ProductRow.Second.G,
      EtaleGraphInterchangeDiagram.ProductRow.Second.H,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      EtaleGraphInterchangeDiagram.ProductRow.Second.interchange,
      EtaleGraphInterchangeDiagram.productInterchange, Iso.trans_hom, Category.assoc]
      using h true

end AlgebraicGeometry.Etale
