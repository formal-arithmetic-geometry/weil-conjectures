/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReductionReindexStrictTensorAux
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorAssociativity
public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroCycleClosed
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorNormalization
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTotalTensorMapGenerators

/-! # The pure-tensor formula of the strict reduction tensor map

Source: Stacks 03EK, 07A4 and 0941.
(blueprint: lem-pod-reduction-reindex-strict-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReductionRepresentatives
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- An isomorphism of module sheaves is inverse on sections.
Source: Stacks 03CO. -/
theorem sheafOfModules_inv_hom_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {A B : SheafOfModules.{u + 1} R} (e : A ≅ B) (U : Cᵒᵖ)
    (s : A.val.obj U) : e.inv.val.app U (e.hom.val.app U s) = s := by
  rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val,
    e.hom_inv_id]
  rfl

/-- Sections of a composite of module-sheaf maps.
Source: Stacks 03CO. -/
theorem sheafOfModules_comp_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {A B D : SheafOfModules.{u + 1} R} (f : A ⟶ B) (g : B ⟶ D)
    (U : Cᵒᵖ) (s : A.val.obj U) : (f ≫ g).val.app U s = g.val.app U (f.val.app U s) :=
  rfl

/-- A natural isomorphism into module sheaves is inverse on sections.
Source: Stacks 03CO. -/
theorem sheafOfModules_natIso_inv_hom_apply {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}} {D : Type*} [Category D]
    {F G : D ⥤ SheafOfModules.{u + 1} R} (e : F ≅ G) (X : D) (U : Cᵒᵖ)
    (s : (F.obj X).val.obj U) : (e.inv.app X).val.app U ((e.hom.app X).val.app U s) = s :=
  sheafOfModules_inv_hom_apply (e.app X) U s

/-- The ordinary unit section is the reduction of `1 ⊗ x`.
Source: Stacks 06YY. -/
theorem scalarUnitSection_eq (W : Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    coefficientIntegralScalarUnitSection l E W n M U x =
      unrestrictedIntegralTensorSection l E W n M U 1 x :=
  finiteAdjunction_unit_apply l E W n M U x

private theorem tensorReductionStrictMap_section (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (k : ℤ) (V : W.ProEt)
    (s : (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q))).X k |>.val.obj
          (op (n, V))) :
    ((tensorReductionStrictMap l E W P Q).f k).val.app (op (n, V)) s =
      ((tensorReductionFiniteComponent l E W P Q n).f k).val.app (op V) s :=
  congrArg (fun φ ↦ (φ.f k).val.app (op V) s)
    (tensorReductionStrictMap_component l E W P Q n)

set_option profiler true in
-- The finite component unfolds four transported tensor comparisons.
/-- The strict reduction tensor map sends the reduction of `1 ⊗ (x ⊗ y)` to the tensor of the
reductions of `1 ⊗ x` and `1 ⊗ y`.
Source: Stacks 03EK, 07A4 and 0941. -/
theorem strictMap_generator (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (p q k : ℤ)
    (hpq : p + q = k) (V : W.ProEt)
    (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)) :
    ((tensorReductionStrictMap l E W P Q).f k).val.app (op (n, V))
      (((pullbackTensorReductionEvaluation l E W n).hom.app _).val.app (op V)
        (unrestrictedIntegralTensorSection l E W n _ (op V) 1
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq (op V) x y))) =
      coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)
        (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P)
        (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q)
        p q k hpq (op (n, V))
        (((pullbackTensorReductionEvaluation l E W n).hom.app (P.X p)).val.app (op V)
          (unrestrictedIntegralTensorSection l E W n _ (op V) 1 x))
        (((pullbackTensorReductionEvaluation l E W n).hom.app (Q.X q)).val.app (op V)
          (unrestrictedIntegralTensorSection l E W n _ (op V) 1 y)) := by
  rw [tensorReductionStrictMap_section]
  trace "PH199: component applied"
  unfold tensorReductionFiniteComponent
  dsimp only
  simp only [HomologicalComplex.comp_f, reductionEvaluationComplex_inv_f]
  erw [sheafOfModules_comp_apply]
  erw [sheafOfModules_natIso_inv_hom_apply]
  trace "PH199: cancellation done"
  rw [← scalarUnitSection_eq]
  erw [sheafOfModules_comp_apply, coefficientScalarTensorIso_hom_unitSection,
    sheafOfModules_comp_apply]
  trace "PH199: scalar tensor applied"
  have hm := coefficientTotalTensor_map_generator W (integralCoefficientCommRingSheaf l E W n)
    ((pullbackTensorReductionEvaluationComplex l E W n).hom.app P)
    ((pullbackTensorReductionEvaluationComplex l E W n).hom.app Q) p q k hpq (op V)
    (coefficientIntegralScalarUnitSection l E W n (P.X p) (op V) x)
    (coefficientIntegralScalarUnitSection l E W n (Q.X q) (op V) y)
  trace "PH199: tensor map prepared"
  erw [hm]
  simp only [reductionEvaluationComplex_hom_f, scalarUnitSection_eq]
  trace "PH199: inverse evaluation remains"
  exact coefficientEvaluationTensorIso_inv_generator l E W n
    (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P)
    (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q) p q k hpq (op V)
    (((pullbackTensorReductionEvaluation l E W n).hom.app (P.X p)).val.app (op V)
      (unrestrictedIntegralTensorSection l E W n _ (op V) 1 x))
    (((pullbackTensorReductionEvaluation l E W n).hom.app (Q.X q)).val.app (op V)
      (unrestrictedIntegralTensorSection l E W n _ (op V) 1 y))
  trace "PH199: proof completed"

end WeilConjectures.PodReductionRepresentatives
