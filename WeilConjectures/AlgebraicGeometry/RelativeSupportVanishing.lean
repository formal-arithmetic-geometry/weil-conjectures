/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.KrullDimension.Basic

public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp

/-! # Lower vanishing for the supported complex of a smooth pair

## References

* [Stacks Project, Tag 0FUE](https://stacks.math.columbia.edu/tag/0FUE)
* [Stacks Project, Tag 09XP](https://stacks.math.columbia.edu/tag/09XP)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

-- STATEMENT-DISPUTED: the former codimension convention allowed infinite ambient
-- stalk dimensions. The returned E2 repair adds hfinite before using that convention.
/-- The derived sheaf of closed-supported sections of a signed finite Tate coefficient
vanishes below twice the codimension of a smooth pair with finite-dimensional ambient
stalks. The finite-dimensional stalk hypothesis explicitly rules out using the
codimension equation at infinity, where addition cannot determine the codimension.
No frame or orientation is needed for this vanishing assertion.
-/
theorem relative_support_vanishing
    (P : WeilConjectures.PurityFiniteSetting.{u}) (c d : ℕ)
    {B V Z U : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    [SmoothOfRelativeDimension d v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)]
    (hcodim : ∀ z : Z,
      ringKrullDim (V.presheaf.stalk (i.base z)) =
        ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞))
    (hfinite : ∀ z : Z,
      ringKrullDim (V.presheaf.stalk (i.base z)) ≠ ⊤)
    (e : U ⟶ V) [Etale e] (r : ℤ) :
    ∀ q : ℤ, q < 2 * (c : ℤ) →
      IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((sectionsWithSupport AddCommGrpCat.{u + 1}
            (pullback.snd i e).openComplement.ι).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((P.forgetEtale U).obj
                (Scheme.finiteEtaleTateSheaf P.Coefficient (ringChar P.Coefficient) U
                  (CharP.cast_eq_zero P.Coefficient (ringChar P.Coefficient)) r))))) := by
  sorry

end AlgebraicGeometry.Etale
