module

public import Sheaf.Paper.PurityFrameKummer
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary

/-! # Supported Kummer realization of a framed line bundle

Source: Stacks Tags 03AJ, 03PL and 0A45; blueprint main-20261015,
lem-pur-divisor-class, first sentence and final paragraph
(blueprint: def-pur-framed-scalar-maps).

The integral torsor extension remembers the frame on the complementary open.
Scalar extension is performed on roots of unity, never on Gm as a Z/m-module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting
/-- Yoneda composition with fixed degree. Source: Stacks 03PL
(blueprint: def-pur-framed-scalar-maps). -/
@[irreducible] def divisorSplice {C : Type v} [Category.{w} C] [Abelian C]
    [HasExt.{w} C] {S G M B : C} (β : Ext.{w} S G 1) (k : Ext.{w} G M 1)
    (f : M ⟶ B) : Ext.{w} S B 2 :=
  (β.comp k (rfl : 1 + 1 = 2)).comp (Ext.mk₀ f) (add_zero 2)

/-- The scalar roots image of the Yoneda splice k_m[1] beta.
Source: Stacks 03PL and the integral normalization of the framed-line refinement
(blueprint: def-pur-framed-scalar-maps). -/
@[irreducible] def divisorIntegralSplice (P : PurityFiniteSetting.{u}) {Z T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (i : Z ⟶ T)
    (β : Ext.{u + 1} ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
      (Etale.supportedIntegralConstant Z)) T.gmSheaf 1) :=
  divisorSplice β (T.kummerSequence_shortExact P.diagonalExponent
    (P.diagonalExponent_isUnit a)).extClass
      (Etale.ordinaryFiniteRootMap P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T)



end WeilConjectures.PurityFiniteSetting
