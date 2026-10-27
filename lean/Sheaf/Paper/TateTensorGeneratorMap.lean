/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CondensedTateIntegralTowerData

/-! Fixed-level root-generator comparison for the integral Tate tensor.

Source: smooth-purity transport, normalized Tate tower, Step 1.
(blueprint: lem-pur-tate-tensor-generator-map)
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

/-- A morphism inducing the quotient projection on all compatible root generators.
No invertibility is asserted here.

Source: current blueprint, sec-smooth-purity/sk-thm-purity-transport, Step 2,
ordinary quotient comparison of the integral root tensor.
(blueprint: lem-pur-tate-tensor-generator-map)

Proof: on the compatible primitive-root covering, identify the inverse-limit root
module with the completed coefficient unit by compatible scalar coordinates.
Project these coordinates to the finite coefficient ring and tensor the root
projections in the prescribed order. For degree zero use coefficient multiplication.
The projection formula is balanced in every coefficient, hence defines a morphism
on the sheafified tensor. Changing a primitive root changes both coordinates by
the same unit, so these local morphisms agree on overlaps and glue. Restriction
commutes with the root projections, giving the displayed formula for every lift.
On the empty scheme the unique morphism has the same formula. -/
theorem tateTensorQuotient_generator_map
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n d : ℕ) :
    ∃ f : (realization T ell n).obj (finiteSheaf T ell n d) ⟶ quotientLine T ell n d,
      GeneratorCompatible T ell n d f := by sorry

end AlgebraicGeometry.Scheme.PurityIntegralTower
