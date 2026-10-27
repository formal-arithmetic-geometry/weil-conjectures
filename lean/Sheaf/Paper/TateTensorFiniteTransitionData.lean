/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CondensedTateIntegralTowerData

/-! The generator formula for finite Tate transitions.

Source: smooth-purity transport, normalized Tate tower, Step 4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

/-- The root-power formula for a completed-coefficient linear map between the ordinary
finite models. The scalar section at the larger quotient is reduced to the smaller one.
Source: smooth-purity transport, normalized Tate tower, Step 4.
(blueprint: def-pur-tate-tensor-finite-transition) -/
def FiniteRootTransition
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (d b a : ℕ) (hab : a ≤ b)
    (r : CoefficientLineComparison
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
      (ell ^ (b + 1)) (ell ^ (a + 1))
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (f : (pbcRestrict (pbcAdicProjection T (datum.{u} ell) b)).obj
        ((realization T ell b).obj (finiteSheaf T ell b d)) ⟶
      (pbcRestrict (pbcAdicProjection T (datum.{u} ell) a)).obj
        ((realization T ell a).obj (finiteSheaf T ell a d))) : Prop :=
  ∀ (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ) (v : W.unop ⟶ (toProEt T).obj U.unop)
    (s : coefficient ell (b + 1))
    (t : ((pbcAdicRings T (datum.{u} ell)).obj (op b)).obj.obj W)
    (z : Fin d → (T.rootsOfUnitySheaf (ell ^ (b + 1))).obj.obj U),
    f.val.app W
        (t • (@id (((realization T ell b).obj (finiteSheaf T ell b d)).val.obj W)
          ((toSheafify (ProEt.topology T)
            ((finiteSheaf T ell b d).obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W
            ((finiteSheaf T ell b d).obj.map v.op
              (((ProEtale.comparisonAdjunction
                (ModuleCat.{u + 1} (coefficient ell (b + 1))) T).unit.app
                  (finiteEtaleTateTwist T (ell ^ (b + 1))
                    (coefficient ell (b + 1)) (CharP.cast_eq_zero _ _) d)).hom.app U
                (finiteTateEtalePowerGenerator T _ (ell ^ (b + 1))
                  (CharP.cast_eq_zero _ _) U s d z)))))) =
      (pbcAdicQuotient T (datum.{u} ell) b a hab).hom.app W t •
        (@id (((realization T ell a).obj (finiteSheaf T ell a d)).val.obj W)
          ((toSheafify (ProEt.topology T)
            ((finiteSheaf T ell a d).obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W
            ((finiteSheaf T ell a d).obj.map v.op
              (((ProEtale.comparisonAdjunction
                (ModuleCat.{u + 1} (coefficient ell (a + 1))) T).unit.app
                  (finiteEtaleTateTwist T (ell ^ (a + 1))
                    (coefficient ell (a + 1)) (CharP.cast_eq_zero _ _) d)).hom.app U
                (finiteTateEtalePowerGenerator T _ (ell ^ (a + 1))
                  (CharP.cast_eq_zero _ _) U
                  (FiniteReduction.quotient ell (Nat.add_le_add_right hab 1) s) d
                  (fun i ↦ r.roots.hom.app U (z i)))))))

end AlgebraicGeometry.Scheme.PurityIntegralTower
