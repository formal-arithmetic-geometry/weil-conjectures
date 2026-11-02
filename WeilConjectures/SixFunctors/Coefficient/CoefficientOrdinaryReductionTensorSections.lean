/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Generator calculus for ordinary coefficient reduction and tensor products

Source: Stacks 03EK, 07A4 and 0941.

Maps out of an ordinary finite scalar extension are fixed by the unit sections, and
maps out of a total tensor complex by its pure tensor generators. We record the
resulting naturality of the ordinary scalar tensor comparison and its compatibility
with the strict quotient maps.
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

noncomputable section
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] coefficientFiniteQuotientExistence
  coefficientFiniteQuotientDerivedExistence coefficientFiniteQuotientModel
  coefficientFiniteQuotientExtension coefficientFiniteQuotientUnitSection
  SheafOfModules.monoidalCategory scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionExtension coefficientFiniteQuotientDerived HasDerivedCategory.standard
  CoefficientClosedStructure.tensor coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceTopology constantSheaf coefficientSequenceEvaluation

attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf CategoryTheory.sheafCompose
  CommRingCat.hasForgetToRingCat

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator

/-- Maps out of an ordinary finite scalar extension agree once they agree on unit sections.
Source: Stacks 03CZ, 06YY. -/
theorem coefficientOrdinaryExtension_hom_ext (n : ℕ) {X : scalarReductionSource l E W}
    {Y : scalarReductionTarget l E W n} {f g : (scalarReductionExtension l E W n).obj X ⟶ Y}
    (h : ∀ (V : W.ProEtᵒᵖ) (x : X.val.obj V),
      f.val.app V (coefficientIntegralScalarUnitSection l E W n X V x) =
        g.val.app V (coefficientIntegralScalarUnitSection l E W n X V x)) : f = g := by
  apply ((coefficientOrdinaryScalarAdjunction l E W n).homEquiv X Y).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext V x
  exact h V x

/-- The unit-section formula characterizing the ordinary scalar tensor comparison.
Source: Stacks 03EK, 07A4. -/
theorem coefficientScalarTensorIso_hom_generator (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) (p q k : ℤ) (hpq : p + q = k)
    (V : W.ProEtᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    ((coefficientScalarTensorIso l E W n P Q).hom.f k).val.app V
      (coefficientIntegralScalarUnitSection l E W n _ V
        (coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq V x y)) =
      coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q) p q k hpq V
        (coefficientIntegralScalarUnitSection l E W n _ V x)
        (coefficientIntegralScalarUnitSection l E W n _ V y) := by
  unfold coefficientScalarTensorIso coefficientUniqueComparisonChoice
  exact (coefficientScalarTensorIso_exists l E W n P Q).choose_spec.1 p q k hpq V x y

/-- Ordinary scalar extension of a map sends unit sections to unit sections.
Source: Stacks 03CZ, 06YY. -/
theorem coefficientIntegralScalarUnitSection_map (n : ℕ) {X X' : scalarReductionSource l E W}
    (φ : X ⟶ X') (V : W.ProEtᵒᵖ) (x : X.val.obj V) :
    ((scalarReductionExtension l E W n).map φ).val.app V
        (coefficientIntegralScalarUnitSection l E W n X V x) =
      coefficientIntegralScalarUnitSection l E W n X' V (φ.val.app V x) :=
  (congrArg (fun k ↦ k.val.app V x)
    ((coefficientOrdinaryScalarAdjunction l E W n).unit.naturality φ)).symm

section Generic
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}

/-- An eqToHom of module sheaves is the identity on sections.
Source: Stacks 03CZ. -/
theorem sheafOfModules_eqToHom_section_heq {R : Sheaf J RingCat.{r}}
    {M N : SheafOfModules.{r} R} (p : M = N) (U : Cᵒᵖ) (y : M.val.obj U) :
    HEq ((eqToHom p).val.app U y) y := by
  subst p
  rfl

/-- The mate of a comparison of composite restrictions sends unit sections to unit sections.
Source: Stacks 03CZ, 03D7. -/
theorem coefficientQuotientNatTrans_unitSection {A Bm Bn : Sheaf J RingCat.{r}}
    (pm : A ⟶ Bm) (pn : A ⟶ Bn) (q : Bm ⟶ Bn)
    {Fm : SheafOfModules.{r} A ⥤ SheafOfModules.{r} Bm}
    {Fn : SheafOfModules.{r} A ⥤ SheafOfModules.{r} Bn}
    (am : Fm ⊣ SheafOfModules.restrictScalars pm) (an : Fn ⊣ SheafOfModules.restrictScalars pn)
    (e : SheafOfModules.restrictScalars q ⋙ SheafOfModules.restrictScalars pm ≅
      SheafOfModules.restrictScalars pn)
    (he : ∀ (N : SheafOfModules.{r} Bn) (U : Cᵒᵖ) (y : N.val.obj U),
      (e.inv.app N).val.app U y = y)
    (M : SheafOfModules.{r} A) (U : Cᵒᵖ) (x : M.val.obj U) :
    coefficientRestrictionSection q (Fn.obj M) U
      (((coefficientQuotientNatTrans am an (SheafOfModules.restrictScalars q) e).app M).val.app U
        (coefficientRestrictionSection pm (Fm.obj M) U ((am.unit.app M).val.app U x))) =
      coefficientRestrictionSection pn (Fn.obj M) U ((an.unit.app M).val.app U x) := by
  let t := an.unit.app M ≫ e.inv.app (Fn.obj M)
  have ht : am.unit.app M ≫ (SheafOfModules.restrictScalars pm).map
      ((am.homEquiv _ _).symm t) = t :=
    (am.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  exact (congrArg (fun k ↦ k.val.app U x) ht).trans (he _ U _)

end Generic

/-- The strict quotient map sends unit sections to unit sections.
Source: Stacks 06YY, 0941. -/
theorem coefficientOrdinaryQuotient_unitSection {m n : ℕ} (h : n ≤ m)
    (X : scalarReductionSource l E W) (V : W.ProEtᵒᵖ) (x : X.val.obj V) :
    coefficientRestrictionSection (normalizedDVRQuotient l E W h) _ V
      (((coefficientOrdinaryQuotient l E W h).app X).val.app V
        (coefficientIntegralScalarUnitSection l E W m X V x)) =
      coefficientIntegralScalarUnitSection l E W n X V x := by
  have hq : (coefficientOrdinaryQuotient l E W h).app X =
      coefficientOrdinaryQuotientComponent l E W h X := by
    unfold coefficientOrdinaryQuotient
    exact (coefficientOrdinaryQuotient_exists l E W h).choose_spec.1 X
  rw [hq]
  have key := coefficientQuotientNatTrans_unitSection
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t+1)} RingCat.{max u (t+1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W m))
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t+1)} RingCat.{max u (t+1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W n))
    (normalizedDVRQuotient l E W h)
    (Fm := scalarReductionExtension l E W m) (Fn := scalarReductionExtension l E W n)
  sorry

end
end WeilConjectures
