/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.Paper.SupportedClassGeometry
public import Sheaf.Paper.SupportedExteriorShift
public import Sheaf.Paper.SupportedTwistPullback
public import Sheaf.Paper.SupportedTwistMultiplication
public import Sheaf.Paper.SupportedClassSiteComparison

/-! # Supported exterior classes and signed twists

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-supported-exterior-class-arrows).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v c d e w v₁ v₂ v₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

open AlgebraicGeometry AlgebraicGeometry.Etale

/-- Tensor the supported representatives and apply the exterior shift comparison,
with the coefficient ring and targets kept variable.
Source: blueprint Step 1, supported exterior class
(blueprint: def-pur-supported-exterior-class-arrows). -/
def compactProductExteriorClassCore (A : Type (u + 1)) [CommRing A]
    {B X Y Z W : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (M N : DerivedCategory (ModuleCat.{u + 1} A))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (a b : ℤ) (α : (supportedCoefficients A i).mapDerivedCategory.obj M ⟶ K⟦a⟧)
    (β : (supportedCoefficients A j).mapDerivedCategory.obj N ⟶ L⟦b⟧) :
    (supportedCoefficients A (supportedProductImmersion f g i j)).mapDerivedCategory.obj
        (M ⊗ N) ⟶ (externalProduct (ModuleCat.{u + 1} A) f g K L)⟦a + b⟧ :=
  supportedCoefficientTensorDerived A f g i j M N ≫
    supportedDerivedTensorMap A (pullback f g)
      (compactProductClassPullbackGeneric A i (pullback.fst f g) M (K⟦a⟧) α)
      (compactProductClassPullbackGeneric A j (pullback.snd f g) N (L⟦b⟧) β) ≫
    compactProductShiftGeneric (ModuleCat.{u + 1} A) f g K L a b

/-- The supported exterior class, explicitly the tensor of the two supported morphisms
through the same derived coefficient comparison whose adjunct defines kappa^{Z,W}.
The source is written as C_h(A[0] tensor A[0]), retaining its coefficient multiplication
instead of silently identifying coefficient units.
Source: blueprint Step 1, supported exterior class
(blueprint: def-pur-supported-exterior-class-arrows). -/
def compactProductExteriorClass (P : PurityFiniteSetting.{u})
    {X Y Z W : Scheme.{u}} (f : X ⟶ Spec (.of P.field.k))
    (g : Y ⟶ Spec (.of P.field.k)) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (a b r s : ℤ)
    (α : P.FunctorialCupH false i a r) (β : P.FunctorialCupH false j b s) :
    (supportedCoefficients P.Coefficient (supportedProductImmersion f g i j)).mapDerivedCategory.obj
        (P.compactProductUnit ⊗ P.compactProductUnit) ⟶
      ((P.functorialCupSingle false (pullback f g)).obj
        (P.functorialCupTwist false (pullback f g) (r + s)))⟦a + b⟧ :=
  compactProductExteriorClassCore P.Coefficient f g i j
      P.compactProductUnit P.compactProductUnit
      ((P.functorialCupSingle false X).obj (P.functorialCupTwist false X r))
      ((P.functorialCupSingle false Y).obj (P.functorialCupTwist false Y s)) a b
      (P.compactProductClass i a r α) (P.compactProductClass j b s β) ≫
    (P.compactProductTwistMultiplication f g r s)⟦a + b⟧'

end WeilConjectures.PurityFiniteSetting
