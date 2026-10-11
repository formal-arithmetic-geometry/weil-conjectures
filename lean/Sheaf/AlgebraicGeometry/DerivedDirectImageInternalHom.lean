/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure

/-!
# Internal-Hom comparison for derived direct image

Source: Stacks Project, cohomology.tex, Remark remark-projection-formula-for-internal-hom
(blueprint: lem-pc-sheaf-rhom-projection-formula).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The natural internal-Hom comparison for `Rf_*`, specified as the mate of evaluation.
The witnesses `a`, `bX`, `bY` and `t` exhibit the pullback/direct-image adjunction,
tensor/internal-Hom adjunctions and pullback/tensor comparison. The last equation
specifies the comparison, rather than merely asserting the existence of some arrow.

Source: Stacks Project, cohomology.tex, Remark remark-projection-formula-for-internal-hom
(blueprint: lem-pc-sheaf-rhom-projection-formula).

Proof:
1. Use lem-pc-ringed-spaces-derived-adjoint-general for the adjunction `a` and
   lem-sc-derived-internal-hom-adjunction for `bX` and `bY`. Evaluation is the counit
   of the latter adjunctions, equivalently the transpose of the identity of RHom.
2. For a test object `A` and `α : A ⟶ Rf_* RHom(L,M)`, transpose `α` by `a`, then
   by `bX`. Use lem-pc-derived-pullback-tensor-product to identify the pullback of
   `A ⊗ Rf_*L` with `Lf^*A ⊗ Lf^*Rf_*L`. Precompose with identity tensor the
   counit `Lf^*Rf_*L ⟶ L`. Transpose back by `a` and `bY`. Yoneda constructs the
   asserted comparison. This is the relative cup product followed by `Rf_*` of
   evaluation, exactly the construction in the source remark.
3. All operations are natural; hence the comparison is natural in both `L` and
   `M`. The displayed equation records its mate construction on every test map.
   No invertibility of the resulting comparison is asserted. -/
theorem exists_derivedDirectImage_internalHom_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∃ (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
      (bX : ∀ L : schemeDerivedCategory X, tensorRight L ⊣
        (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf)).obj
            (op L))
      (bY : ∀ L : schemeDerivedCategory Y, tensorRight L ⊣
        (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
            (op L))
      (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
        (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
      (c : derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf ⋙
          schemeDerivedDirectImage f ⟶
        (schemeDerivedDirectImage f).op.prod (schemeDerivedDirectImage f) ⋙
          derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf),
      ∀ (L M : schemeDerivedCategory X) (A : schemeDerivedCategory Y)
        (α : A ⟶ (schemeDerivedDirectImage f).obj
          ((derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf).obj
            (op L, M))),
        ((bY ((schemeDerivedDirectImage f).obj L)).homEquiv A
          ((schemeDerivedDirectImage f).obj M)).symm (α ≫ c.app (op L, M)) =
        a.homEquiv (A ⊗ (schemeDerivedDirectImage f).obj L) M
          (t.hom.app (A, (schemeDerivedDirectImage f).obj L) ≫
            (𝟙 ((derivedPullback f).obj A) ⊗ₘ a.counit.app L) ≫
            ((bX L).homEquiv ((derivedPullback f).obj A) M).symm
              ((a.homEquiv A
                ((derivedInternalHom (Opens.grothendieckTopology X)
                  X.toRingedSpace.sheaf).obj (op L, M))).symm α)) := by
  sorry

end AlgebraicGeometry
