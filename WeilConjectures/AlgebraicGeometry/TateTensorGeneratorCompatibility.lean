/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedTateIntegralTowerData

/-! Generator compatibility for the integral Tate tensor.

Source: smooth-purity transport, normalized Tate tower, Step 1.
(blueprint: def-pur-tate-tensor-generator-compatibility)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

/-- The prescribed action of a morphism on compatible root generators.
Source: smooth-purity transport, ordinary Tate quotient comparison. -/
def GeneratorCompatible
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (n d : ℕ) (f : (realization T ell n).obj (finiteSheaf T ell n d) ⟶
      quotientLine T ell n d) : Prop :=
      ∀ (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
        (v : W.unop ⟶ (toProEt T).obj U.unop)
        (a : coefficient ell (n + 1))
        (z : Fin d → (T.rootsOfUnitySheaf (ell ^ (n + 1))).obj.obj U)
        (x : Fin d → (purTwistZlOne T ell).obj.obj W),
        (∀ i : Fin d, finiteTateLimitRootValue ell T n W (x i) =
          Units.map v.left.appTop.hom.toMonoidHom
            (finiteTateEtaleRootValue T (ell ^ (n + 1)) U (z i))) →
        f.val.app W
            (1 • (@id (((realization T ell n).obj (finiteSheaf T ell n d)).val.obj W)
              ((toSheafify (ProEt.topology T)
              ((finiteSheaf T ell n d).obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W
              ((finiteSheaf T ell n d).obj.map v.op
                (((ProEtale.comparisonAdjunction
                  (ModuleCat.{u + 1} (coefficient ell (n + 1))) T).unit.app
                    (finiteEtaleTateTwist T (ell ^ (n + 1))
                      (coefficient ell (n + 1)) (CharP.cast_eq_zero _ _) d)).hom.app U
                  (finiteTateEtalePowerGenerator T _ (ell ^ (n + 1))
                    (CharP.cast_eq_zero _ _) U a d z)))))) =
          pbcTensorSection (pbcAdicProjection T (datum.{u} ell) n)
            (integralLine T ell d) W (((scalars T ell n).app W).hom a)
              (integralGenerator T ell W d x)

end AlgebraicGeometry.Scheme.PurityIntegralTower
