/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P9
-/
module

public import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
public import Sheaf.AlgebraicGeometry.OrdinaryKunnethMap

/-! # Forgetting supports in the exterior product

Source: blueprint `def-pur-supported-exterior-product`, final paragraph.
(blueprint: lem-pur-supported-product-forget-supports).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] HomologicalComplex₂.total
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale

/-- Forgetting supports commutes with the actual exterior product.
Source: blueprint `def-pur-supported-exterior-product`, final paragraph;
Stacks Tag 0F1E, construction of the exterior product.
(blueprint: lem-pur-supported-product-forget-supports).

Proof: the quotient-normalized supported adjunction identifies the composite of its
inverse Hom bijection with the constant-to-support quotient with the ordinary constant
adjunction applied after the kernel inclusion. The defining quotient equation of the
coefficient tensor comparison therefore identifies the two ordinary section pairings.
On complexes the equation holds after each bidegree inclusion; the totalization signs
are the same on both sides. Apply the localization comparisons to this equation.
The derived comparisons are uniquely normalized on cochain models and natural in
both arguments, so their quotient square is the derived ordinary square. The derived
adjunctions inherit the same counit normalization by the derived universal property.
Transpose the square of coefficient maps and the two evaluation counits under the
constant/global-sections adjunction. Its two sides are the displayed composites.
This construction uses arbitrary K-flat and K-injective models, so the equation holds
for unbounded complexes and arbitrary coefficients. Empty supports make both composites
zero; full supports specialize to the ordinary product under kernel inclusions.
-/
theorem supportedExteriorProduct_forget
    (A : Type (u + 1)) [CommRing A] {S X Y Z W : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    supportedExteriorProduct A f g i j K L ≫
        (Functor.rightDerivedFunctorNatTrans
          (supportedEtaleSectionsι A (pullback f g)
            (supportedProductImmersion f g i j).openComplement)).app
              (externalProduct (ModuleCat.{u + 1} A) f g K L) =
      tensorHom
          ((Functor.rightDerivedFunctorNatTrans
            (supportedEtaleSectionsι A X i.openComplement)).app K)
          ((Functor.rightDerivedFunctorNatTrans
            (supportedEtaleSectionsι A Y j.openComplement)).app L) ≫
        ordinaryGlobalKunnethMap (ModuleCat.{u + 1} A)
          (pullback.fst f g) (pullback.snd f g) K L := by sorry

end AlgebraicGeometry.Etale
