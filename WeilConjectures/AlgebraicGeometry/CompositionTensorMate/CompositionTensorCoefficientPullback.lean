/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompositionTensorMate.CondensedBridge.CompositionTensorMateData2

/-! # Pullback composition in normalized finite coefficient coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CompositionTensorMate
open FiniteDiscreteOrdinary CondensedBridge
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [Finite A] [DiscreteTopology A]

/-- Encoding the specified pullback compositor agrees with the compositor of the
encoded pullbacks, for every unbounded input.
Source: section-action pullback comparison in composition proof Step 2
(blueprint: lem-pur-composition-tensor-coefficient-pullback).

Proof: the underived pushforward comparison is identity on the common additive
sections. The native and ordinary pushforward compositors are induced by the same
base-change identification of those sections, so their encoding square commutes.
The specified nativeencodingPullbackIso is the left-adjoint-uniqueness mate of this
comparison. Mate pasting and conjugation identify the square for the native and
ordinary underived pullback compositors. Both pullbacks are exact. Apply the total
left-derived functor to this square and use naturality and associativity of its
composition comparison. The exact/left-derived identifications at the encoding
functors cancel by their localization factorization equations. These are precisely
the three components defining encodingDerivedPull and the components defining the
two canonical derived pullback compositors. Evaluation at K gives the equation.
No boundedness, nonzero coefficient or nonempty site is required. -/
theorem compositionTensorCoefficientPullback (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (K : Native A Z) :
    (N A E X).map
        ((CondensedRing.condensedCanonicalPullbackComposition
          (coefficient A) f g).hom.app K) ≫
      (FiniteNativeTensor.encodingDerivedPull A E f).inv.app ((nativePull A g).obj K) ≫
      (S (ULift.{u + 1} A) f).map
        ((FiniteNativeTensor.encodingDerivedPull A E g).inv.app K) =
    (FiniteNativeTensor.encodingDerivedPull A E (f ≫ g)).inv.app K ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g).hom.app
        ((N A E Z).obj K) := by
  sorry

end AlgebraicGeometry.ProEtale.CompositionTensorMate
