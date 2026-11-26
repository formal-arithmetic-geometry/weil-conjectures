/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import WeilConjectures.SmoothPurity.Pur.PurSequenceOrdinaryFactorization

/-! # The ordinary coefficient tensor and inverse-limit adjunction

The ordinary quotient tensor and inverse limit admit the prescribed sectionwise adjunction.

## Implementation details

At level `n` the tensor functor is identified with `scalarReductionExtension` using the
normalized scalar adjunctions, whose units send `x` to `1 ⊗ x`. The Hom bijection sends a system
map to the compatible family obtained by evaluating it on `1 ⊗ x`, which the inverse-limit
universal property identifies with a map into `ordinaryLimit`. Limits of complexes are computed
degreewise.

## References

* [Stacks Project, Tags 03D7 and 0941](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.CompletionUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

section OrdinaryConstruction
attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionExtension HasDerivedCategory.standard SheafOfModules.monoidalCategory
  constantSheaf

private theorem ordinary_projection_unit (O : PurSequenceOrdinaryAdjoints l E W)
    (M : scalarReductionSource l E W) (n : ℕ) :
    O.adjunction.unit.app M ≫ O.projection (O.pullback.obj M) n ≫
      (scalarReductionRestriction l E W n).map ((O.tensor n).hom.app M) =
      (purSequenceFiniteAdjunction l E W n).unit.app M := by
  have ht := O.transpose M (O.pullback.obj M) (O.adjunction.unit.app M) n
  rw [Adjunction.homEquiv_symm_unit, CategoryTheory.Functor.map_id] at ht
  erw [Category.comp_id] at ht
  rw [← Category.assoc, ← ht, Adjunction.homEquiv_unit]
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
  rw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

private def ordinaryAdjunction (O : PurSequenceOrdinaryAdjoints l E W) :
    O.pullback ⊣ ordinaryLimit l E W := O.adjunction.ofNatIsoRight O.limit

private theorem ordinary_projection_unit_fixed (O : PurSequenceOrdinaryAdjoints l E W)
    (M : scalarReductionSource l E W) (n : ℕ) :
    (ordinaryAdjunction l E W O).unit.app M ≫
      limit.π ((coefficientSequenceRestriction l E W).obj (O.pullback.obj M)) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        (O.pullback.obj M) ≫
      (scalarReductionRestriction l E W n).map ((O.tensor n).hom.app M) =
    (purSequenceFiniteAdjunction l E W n).unit.app M := by
  have hu := ordinary_projection_unit l E W O M n
  rw [O.projection_limit] at hu
  simp only [Category.assoc] at hu
  simpa only [ordinaryAdjunction, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc] using hu

end OrdinaryConstruction

private theorem finite_unit_tensor (M : scalarReductionSource l E W) (n : ℕ)
    (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    ((purSequenceFiniteAdjunction l E W n).unit.app M).val.app V x =
      unrestrictedIntegralTensorSection l E W n M V 1 x := by
  have hu := (scalarReductionExtension_adjunction.{t, u} l E W n).choose_spec M V x
  dsimp only [purSequenceFiniteAdjunction, unrestrictedIntegralTensorSection,
    unrestrictedIntegralReductionFunctor, unrestrictedIntegralReductionExistence,
    scalarReductionExistence] at hu ⊢
  exact hu

private theorem ordinary_unit_tensor (O : PurSequenceOrdinaryAdjoints l E W)
    (M : scalarReductionSource l E W) (n : ℕ) (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    (((ordinaryAdjunction l E W O).unit.app M ≫
      limit.π ((coefficientSequenceRestriction l E W).obj (O.pullback.obj M)) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        (O.pullback.obj M) ≫
      (scalarReductionRestriction l E W n).map ((O.tensor n).hom.app M)).val.app V) x =
      unrestrictedIntegralTensorSection l E W n M V 1 x := by
  exact (congrArg (fun f ↦ f.val.app V x)
    (ordinary_projection_unit_fixed l E W O M n)).trans (finite_unit_tensor l E W M n V x)

section CanonicalComparisons

-- The cone of ordinary inverse-limit projections in each degree.
private def termwiseLimitCone
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) : Cone Z.asFunctor where
  pt := ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
    scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj Z
  π :=
    { app := fun n ↦ (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app Z
      naturality := by
        intro n m f
        ext p : 1
        change 𝟙 _ ≫ limit.π (Z.X p) m =
          limit.π (Z.X p) n ≫ (Z.X p).map f
        exact (Category.id_comp _).trans (limit.w (Z.X p) f).symm }

private def termwiseLimitConeIsLimit
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    IsLimit (termwiseLimitCone l E W Z) :=
  HomologicalComplex.isLimitOfEval Z.asFunctor (termwiseLimitCone l E W Z)
    (fun p ↦ limit.isLimit (Z.X p))

private def termwiseLimitComparisonComponent
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj Z ≅
        limit Z.asFunctor :=
  (termwiseLimitConeIsLimit l E W Z).conePointUniqueUpToIso (limit.isLimit _)

private theorem termwiseLimitComparisonComponent_projection
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ) :
    (termwiseLimitComparisonComponent l E W Z).hom ≫ limit.π Z.asFunctor (op n) =
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app Z :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

private def termwiseLimitComparison :
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ) ≅
        roosLimitFunctor (A := scalarReductionSource l E W) :=
  NatIso.ofComponents (termwiseLimitComparisonComponent l E W) (by
    intro X Y f
    apply limit.hom_ext
    intro n
    change ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
        scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).map f ≫
        ((termwiseLimitComparisonComponent l E W Y).hom ≫ limit.π Y.asFunctor n) =
      (termwiseLimitComparisonComponent l E W X).hom ≫
        (limMap (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) ≫
          limit.π Y.asFunctor n)
    erw [termwiseLimitComparisonComponent_projection l E W Y n.unop]
    erw [limMap_π]
    erw [← Category.assoc,
      termwiseLimitComparisonComponent_projection l E W X n.unop]
    ext p : 1
    exact limMap_π (f.f p) n)

private theorem termwiseLimitComparison_projection
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ) (p : ℤ) :
    ((termwiseLimitComparison l E W).hom.app Z ≫ limit.π Z.asFunctor (op n)).f p =
      limit.π (Z.X p) (op n) :=
  congrArg (fun f ↦ f.f p) (termwiseLimitComparisonComponent_projection l E W Z n)

end CanonicalComparisons

/-- The ordinary quotient tensor and limit admit the prescribed sectionwise adjunction.
This statement involves no derived coefficient calculus or derived comparison. -/
theorem ordinaryModel_exists : Nonempty (OrdinaryModel l E W) := by
  -- The ordinary construction is already packaged by this factorization theorem.
  obtain ⟨O, _⟩ := purSequenceOrdinaryFactorization l E W
  refine ⟨{
    tensor := O.pullback
    additive := O.pullback_additive
    evaluation := O.tensor
    transition := fun M {m n} h ↦ O.tensor_transition M m n h
    adjunction := ordinaryAdjunction l E W O
    unit_tensor := ordinary_unit_tensor l E W O
    limitComparison := Functor.isoWhiskerLeft (tower l E W) (termwiseLimitComparison l E W)
    limitComparison_projection := ?_
  }⟩
  intro I n p
  exact termwiseLimitComparison_projection l E W ((tower l E W).obj I) n p

end WeilConjectures.CompletionUnit
