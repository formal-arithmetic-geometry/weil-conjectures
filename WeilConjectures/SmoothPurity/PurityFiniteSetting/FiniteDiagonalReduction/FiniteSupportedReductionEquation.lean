/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteOrientationScalarPresentation
public import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedCoefficientReduction
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionAffineOrientation

/-! # The scalar-unit reduction equation at a single affine zero divisor

Source: blueprint/latest, sec-smooth-purity/sk-lem-sp-reduction,
thm-pur-finite-reduction-of-purity.proof.md, Steps 3--4
(blueprint: def-pur-finite-supported-reduction-equation).

The fixed-scalar pro-etale presentation is canonically equivalent to the intrinsic
one. All maps below are the published root-generator, scalar-unit and counit mates.
Positive affine coefficient levels are indexed by their predecessors, as in the
published supported-product API; no divisibility by a ramification index is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension Etale.derivedTensor Etale.upperStar Etale.lowerStar

namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

/-- The scalar-unit and generator-normalized reduction equation at one zero divisor.
This is the single-divisor instance of CartierKummerReduction, retaining both units.
Source: node proof Step 1; Stacks 07A6
(blueprint: def-pur-finite-supported-reduction-equation). -/
@[irreducible]
def supportedKummerReductionAt (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Etale.CartierKummerFamily l E) (a b : ℕ) (hab : a ≤ b)
    (S : Scheme.{u})
    (hT : IsUnit (l : Γ(AffineSpace (ULift.{u} (Fin 1)) S, ⊤))) : Prop :=
    ∃ (η : Etale.cartierSupported l E b
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S) ⟶
        (Sheaf.restrictScalars (Scheme.ProEt.topology (AffineSpace (ULift.{u} (Fin 1)) S))
          (Etale.cartierCoefficientReduction l E a b hab)).obj
            (Etale.cartierSupported l E a
              (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)))
      (θ : Scheme.finiteTateProSheaf l E b
          (AffineSpace (ULift.{u} (Fin 1)) S) 1 ⟶
        (Sheaf.restrictScalars (Scheme.ProEt.topology (AffineSpace (ULift.{u} (Fin 1)) S))
          (Etale.cartierCoefficientReduction l E a b hab)).obj
            (Scheme.finiteTateProSheaf l E a
              (AffineSpace (ULift.{u} (Fin 1)) S) 1)),
      (∀ (U : (AffineSpace (ULift.{u} (Fin 1)) S).ProEtᵒᵖ)
          (z : Scheme.finiteTateCoefficient l E b),
        η.hom.app U (Etale.cartierSupportedGenerator l E b
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S) U z) =
        Etale.cartierSupportedGenerator l E a
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S) U
            (Etale.cartierCoefficientReduction l E a b hab z)) ∧
      (∀ (U : (AffineSpace (ULift.{u} (Fin 1)) S).ProEtᵒᵖ)
          (z : Scheme.finiteTateCoefficient l E b)
          (x : (Scheme.purTwistZlOne (AffineSpace (ULift.{u} (Fin 1)) S)
            l).obj.obj U),
        θ.hom.app U (Scheme.finiteTateProGenerator l E b
          (AffineSpace (ULift.{u} (Fin 1)) S) U z x) =
        Scheme.finiteTateProGenerator l E a
          (AffineSpace (ULift.{u} (Fin 1)) S) U
            (Etale.cartierCoefficientReduction l E a b hab z) x) ∧
      Etale.IsCartierDerivedScalarUnit
        (Etale.cartierCoefficientReduction l E a b hab) _ _ _ η ∧
      Etale.IsCartierDerivedScalarUnit
        (Etale.cartierCoefficientReduction l E a b hab) _ _ _ θ ∧
      (Abelian.Ext.mk₀ η).comp
        ((c
          a (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
          (finiteReductionZeroCartier S) hT).mapExactFunctor
            (Sheaf.restrictScalars
              (Scheme.ProEt.topology (AffineSpace (ULift.{u} (Fin 1)) S))
              (Etale.cartierCoefficientReduction l E a b hab)))
        (zero_add 2) =
      (c
        b (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
        (finiteReductionZeroCartier S) hT).comp (Abelian.Ext.mk₀ θ) (add_zero 2)


end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
