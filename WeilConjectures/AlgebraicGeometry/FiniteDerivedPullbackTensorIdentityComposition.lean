/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackTensorComposition

/-! Identity specialization of the fixed-coefficient pullback/tensor composition law.
(blueprint: lem-sf-finite-partial-tensor-identity-component)

This is the fixed-coefficient calculation used when the finite realization is
expanded.  It is independent of the six-functor realization and therefore is a
strictly lower step than the partial-tensor component equation.
-/

@[expose] public section
set_option autoImplicit false

universe u v

open CategoryTheory Abelian Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
open _root_.DerivedCategory
open scoped MonoidalCategory CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  [ProEtale.UpperStarPreservesFlat A]

/-- The canonical fixed-coefficient tensor comparison satisfies the composition
square for two identity pullbacks.  This is the identity instance of the
pro-étale composition coherence theorem, before transporting through the finite
constructible realization.

Source: Stacks Project, Tag 07A4, and
`Sheaf.SixFunctors.ProEtaleDerivedPullbackTensorComposition`.
(blueprint: lem-sf-finite-partial-tensor-identity-component). -/
theorem leftDerivedUpperStarTensorComparison_identityComposition
    {X : Scheme.{u}}
    [NatTrans.IsMonoidal (upperStarComp A (𝟙 X) (𝟙 X)).inv]
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (leftDerivedUpperStarComp A (𝟙 X) (𝟙 X)).hom.app
        (((derivedTensor A X).obj M).obj N) ≫
      (ProEtale.upperStar A (𝟙 X)).leftDerivedFunctor.map
        (leftDerivedUpperStarTensorIso A (𝟙 X) M N).hom ≫
      (leftDerivedUpperStarTensorIso A (𝟙 X)
          ((ProEtale.upperStar A (𝟙 X)).leftDerivedFunctor.obj M)
          ((ProEtale.upperStar A (𝟙 X)).leftDerivedFunctor.obj N)).hom =
    (leftDerivedUpperStarTensorIso A ((𝟙 X) ≫ (𝟙 X)) M N).hom ≫
      ((derivedTensor A X).map
        ((leftDerivedUpperStarComp A (𝟙 X) (𝟙 X)).hom.app M)).app
          ((ProEtale.upperStar A ((𝟙 X) ≫ (𝟙 X))).leftDerivedFunctor.obj N) ≫
      ((derivedTensor A X).obj
        ((ProEtale.upperStar A (𝟙 X)).leftDerivedFunctor.obj
          ((ProEtale.upperStar A (𝟙 X)).leftDerivedFunctor.obj M))).map
        ((leftDerivedUpperStarComp A (𝟙 X) (𝟙 X)).hom.app N) := by
  simpa using
    (leftDerivedUpperStarTensorComparison_comp A (𝟙 X) (𝟙 X) M N)

end AlgebraicGeometry.ProEtale
