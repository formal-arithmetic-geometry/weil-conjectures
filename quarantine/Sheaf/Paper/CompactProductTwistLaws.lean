/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.Paper.SupportedExteriorClassArrows

public import Sheaf.Paper.SupportedClassGeometry
public import Sheaf.Paper.SupportedClassSiteComparison
public import Sheaf.Paper.SupportedExteriorShift
public import Sheaf.Paper.SupportedTwistMultiplication
public import Sheaf.Paper.SupportedTwistPullback
/-! # Supported exterior-class identities for signed finite twists

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-twist-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry AlgebraicGeometry.Etale

/-- Finiteness of the actual positive-level quotient, including its size lift.
Source: blueprint Step 1, finite coefficient datum
(blueprint: def-pur-compact-product-twist-laws). -/
instance compactProductCoefficientFinite (P : PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))


/-- The support identification clause, with the same quantified inputs and canonical maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-twist-laws). -/
def compactProductTwistSupportIdentificationLaw (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y Z W : Scheme.{u}}
    (f : X ⟶ Spec (.of P.field.k)) (g : Y ⟶ Spec (.of P.field.k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j],
    IsIso (compactProductIntersectionMap f g i j)

/-- The etale clause, with the same quantified inputs and canonical maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-twist-laws). -/
def compactProductTwistEtaleLaw (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y Z W : Scheme.{u}} (f : X ⟶ Spec (.of P.field.k))
    (g : Y ⟶ Spec (.of P.field.k)),
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
    IsSeparated g → LocallyOfFiniteType g → QuasiCompact g →
    ∀ (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
      (a b r s : ℤ), Even a → Even b →
      ∀ (α : P.FunctorialCupH false i a r) (β : P.FunctorialCupH false j b s),
      P.compactProductExteriorClass f g i j a b r s α β =
        P.compactProductClassSource (supportedProductImmersion f g i j) ≫
          P.compactProductPulledCup false f g i j a b r s α β

/-- The proetale clause, with the same quantified inputs and canonical maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-twist-laws). -/
def compactProductTwistProetaleLaw (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y Z W : Scheme.{u}} (f : X ⟶ Spec (.of P.field.k))
    (g : Y ⟶ Spec (.of P.field.k)),
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
    IsSeparated g → LocallyOfFiniteType g → QuasiCompact g →
    ∀ (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
      (a b r s : ℤ), Even a → Even b →
      ∀ (α : P.FunctorialCupH false i a r) (β : P.FunctorialCupH false j b s),
      P.compactProductCompareClass (pullback f g) (a + b) (r + s)
          (P.compactProductExteriorClass f g i j a b r s α β) =
        P.compactProductCompareSource (supportedProductImmersion f g i j) ≫
          P.compactProductPulledCup true f g i j a b r s
            (P.functorialCupCompare i a r α) (P.functorialCupCompare j b s β)

/-- The complete conjunction of the named universally quantified clauses above.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-twist-laws). -/
structure CompactProductTwistLaws (P : PurityFiniteSetting.{u}) : Prop where
  support_identification : P.compactProductTwistSupportIdentificationLaw
  etale : P.compactProductTwistEtaleLaw
  proetale : P.compactProductTwistProetaleLaw

end WeilConjectures.PurityFiniteSetting
