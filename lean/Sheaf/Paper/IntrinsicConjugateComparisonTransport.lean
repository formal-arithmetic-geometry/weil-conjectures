/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntrinsicDirectComparisonTransport
public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange

/-! The intrinsic conjugate before the final direct-image comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

/-
The final comparison isomorphism is cancellable, so this statement is one composition
shorter than the intrinsic-coordinate target.  Its proof is the left-derived/exact-derived
adjunction identification and the transported mate equation.
(blueprint: lem-sf-intrinsic-conjugate-comparison-transport).
-/
theorem sfIntrinsicConjugateComparisonTransport
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ) [I.IsKInjective] :
    (conjugateIsoEquiv
        ((sfIntrinsicConstantModuleAdjunction g A).mapDerivedCategoryRightDerivedAdjunction.comp
          (sfIntrinsicConstantModuleAdjunction f A).mapDerivedCategoryRightDerivedAdjunction)
        (sfIntrinsicConstantModuleAdjunction (f ≫ g) A).mapDerivedCategoryRightDerivedAdjunction
        (sfIntrinsicDerivedPullbackComp A f g)).hom.app
          ((sfIntrinsicDerivedEquivalence X A).functor.obj (DerivedCategory.Q.obj I)) =
      sfIntrinsicAmbientCoordinate A f g I
          (leftDerivedUpperStarComp
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g) ≫
      (sfIntrinsicDerivedDirectImageComparison (f ≫ g) A).inv.app
        (DerivedCategory.Q.obj I) := by
  sorry

end AlgebraicGeometry.Scheme
