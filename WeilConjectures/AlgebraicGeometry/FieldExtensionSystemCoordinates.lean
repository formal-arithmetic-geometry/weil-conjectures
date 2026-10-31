/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExtensionIntegralCoordinates
public import WeilConjectures.AlgebraicGeometry.FieldScalarNormalizedSystems

/-! # FieldExtensionSystemCoordinates

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.md, clauses (1)--(3)
(blueprint: def-sp-field-extension-system-coordinates).

## Main definitions and statements

The declarations below package the named functors, comparisons and equations of
the indicated clauses, using the published coefficient and geometric models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard

universe u a b v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExtensionTowers
variable (P : PurityFiniteSetting.{u})
variable (D : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [CompactSpace X] [QuasiSeparatedSpace Y]

set_option maxHeartbeats 600000 in
-- The counit equation compares two nested exact-localization coordinate transports.
/-- Canonical whole-system scalar coordinates, fixed on every tensor section and
by the universal derived counit. Source: clause (1)
(blueprint: def-sp-field-extension-system-coordinates). -/
structure SystemCoordinates (E F : FieldShriekSystem.Index P) (h : E ≤ F) (T : Scheme.{u})
    (RA : SpReductionTower P.coefficients.l E.val T ((D.coordinates E).abelian T))
    (RB : SpReductionTower P.coefficients.l F.val T ((D.coordinates F).abelian T))
    (A : IntegralCoordinates P D E F h T RA RB) where
  systemOrdinary : A.data.extension.ordinary ⋙ ((D.base F).realization T).functor ≅
    ((D.base E).realization T).functor ⋙ (D.scalars E F h T).model.E
  systemOrdinary_sections : ∀ (M : spCoefficientTowers P.coefficients.l E.val T)
    (n : ℕ) (U : T.ProEtᵒᵖ)
    (s : ((spCoefficientCommRings P.coefficients.l F.val T).obj (op n)).obj.obj U)
    (x : ((((D.coordinates E).abelian T).equivalence.functor.obj M).level n).val.obj U),
    HEq
      ((systemOrdinary.hom.app M).val.app (op (n, U.unop))
        ((((D.coordinates F).ordinaryEvaluation T n).inv.app
          (A.data.extension.ordinary.obj M)).val.app U
            (((A.data.extension.level n).inv.app M).val.app U
              (SheafOfModules.systemModelTmul
                (((D.coordinates E).abelian T).scalar
                  (A.data.coefficients.tower.app (op n))).model _ U s x))))
      (SheafOfModules.systemModelTmul (D.scalars E F h T).model
        (((D.base E).realization T).functor.obj M) (op (n, U.unop)) s
          ((((D.coordinates E).ordinaryEvaluation T n).inv.app M).val.app U x))
  systemDerived : A.data.extension.derived ⋙
      (SpTowerCalculus.realization P.coefficients.l F.val (D.base F) T
        ((D.coordinates F).abelian T)).functor ≅
    (SpTowerCalculus.realization P.coefficients.l E.val (D.base E) T
      ((D.coordinates E).abelian T)).functor ⋙ (D.scalars E F h T).T
  systemDerived_rep :
    letI := ((D.coordinates E).abelian T).hasDerived
    letI := ((D.coordinates F).abelian T).hasDerived
    letI := (D.base E).realizationAdditive T
    letI := (D.base F).realizationAdditive T
    ∀ Q : CochainComplex (spCoefficientTowers P.coefficients.l E.val T) ℤ,
    HEq
      ((SpTowerCalculus.realization P.coefficients.l F.val (D.base F) T
        ((D.coordinates F).abelian T)).functor.map (A.data.extension.counit.app Q) ≫
          ((D.base F).realization T).functor.mapDerivedCategoryFactors.hom.app
            ((A.data.extension.ordinary.mapHomologicalComplex (.up ℤ)).obj Q) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex systemOrdinary.hom
            (.up ℤ)).app Q))
      (systemDerived.hom.app ((spTowerLocalization P.coefficients.l E.val T
        ((D.coordinates E).abelian T)).obj Q) ≫
          (D.scalars E F h T).T.map
            (((D.base E).realization T).functor.mapDerivedCategoryFactors.hom.app Q) ≫
          (D.scalars E F h T).model.ε.app
            ((((D.base E).realization T).functor.mapHomologicalComplex (.up ℤ)).obj Q))
  system : A.data.extension.derived ≅ towerScalar P D h T
  system_normalized : ∀ K : spDerivedCoefficientTowers P.coefficients.l E.val T
      ((D.coordinates E).abelian T),
    system.hom.app K =
      (SpTowerCalculus.realization P.coefficients.l F.val (D.base F) T
        ((D.coordinates F).abelian T)).unitIso.hom.app _ ≫
      (SpTowerCalculus.realization P.coefficients.l F.val (D.base F) T
        ((D.coordinates F).abelian T)).inverse.map (systemDerived.hom.app K)
end AlgebraicGeometry.ProEtale.FieldExtensionTowers
