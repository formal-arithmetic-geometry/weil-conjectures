/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import WeilConjectures.AlgebraicGeometry.RelativeKunnethProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-! # Base change for the outside projection and symmetry factors -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance high] SymmetricCategory.toBraidedCategory
variable (A : Type (u + 1)) [CommRing A] [Finite A]

omit [Finite A] in
private theorem kunneth_pull_braiding {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategoryModule A Y) :
    (L((f)^*[ModuleCat.{u + 1} A])).map
        (derivedTensorBraidingIso (ModuleCat.{u + 1} A) Y M N).hom ≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f N M).hom =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f M N).hom ≫
      (derivedTensorBraidingIso (ModuleCat.{u + 1} A) X
        ((L((f)^*[ModuleCat.{u + 1} A])).obj M)
        ((L((f)^*[ModuleCat.{u + 1} A])).obj N)).hom := by
  simpa only [leftDerivedUpperStar_δ_eq, leftDerivedUpperStarTensorIso_hom,
    derivedTensorBraidingIso, derivedTensorBraiding, BraidedCategory.curriedBraidingNatIso,
    Iso.app_hom, NatIso.ofComponents_hom_app] using
      leftDerivedUpperStar_map_braiding_hom_δ (ModuleCat.{u + 1} A) f M N

/-- Base change for the final inverse projection and symmetry in the relative product.
Source: thm-sf-kunneth-relative, base-change clause, outside factors.
(blueprint: lem-sf-relative-kunneth-outer-base-change).

Proof: move the pullback tensor comparison through the symmetry by braided pullback.
Naturality of symmetry moves the compact-support exchange to the first tensor factor.
The inverse projection/exchange square then identifies the remaining factors. -/
theorem relativeKunneth_outer_baseChange
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {b : Y' ⟶ Y}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback a f' f b)
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (L((b)^*[ModuleCat.{u + 1} A])).map
        ((projectionIsoApp A f K L).inv ≫
          (derivedTensorBraidingIso (ModuleCat.{u + 1} A) Y
            ((R(f)_![ModuleCat.{u + 1} A]).obj K) L).hom) ≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) b L
        ((R(f)_![ModuleCat.{u + 1} A]).obj K)).hom ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y').obj
        ((L((b)^*[ModuleCat.{u + 1} A])).obj L)).map
          ((rightDerivedLowerShriekBaseChangeMap A sq).app K) =
    (rightDerivedLowerShriekBaseChangeMap A sq).app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj
          ((L((f)^*[ModuleCat.{u + 1} A])).obj L)) ≫
      (R(f')_![ModuleCat.{u + 1} A]).map
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) a K
          ((L((f)^*[ModuleCat.{u + 1} A])).obj L)).hom ≫
      (R(f')_![ModuleCat.{u + 1} A]).map
        (((derivedTensor (ModuleCat.{u + 1} A) X').obj
          ((L((a)^*[ModuleCat.{u + 1} A])).obj K)).map
            (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A) sq.toCommSq L)) ≫
      (projectionIsoApp A f' ((L((a)^*[ModuleCat.{u + 1} A])).obj K)
        ((L((b)^*[ModuleCat.{u + 1} A])).obj L)).inv ≫
      (derivedTensorBraidingIso (ModuleCat.{u + 1} A) Y'
        ((R(f')_![ModuleCat.{u + 1} A]).obj
          ((L((a)^*[ModuleCat.{u + 1} A])).obj K))
        ((L((b)^*[ModuleCat.{u + 1} A])).obj L)).hom := by
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (kunneth_pull_braiding A b _ _)]
  rw [← derivedTensorBraidingIso_hom_naturality_left]
  rw [reassoc_of% (relativeKunneth_projection_inv_baseChange A sq K L)]
  rfl

end AlgebraicGeometry.Etale
