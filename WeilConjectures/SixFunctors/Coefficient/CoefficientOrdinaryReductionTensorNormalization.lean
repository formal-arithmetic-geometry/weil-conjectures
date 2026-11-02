/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionComparison
import all WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionComparison

/-! # Strict presentations of reduction through the ordinary quotient system

Source: Stacks 06YY, 07A4, 07A6 and 0941.

A strict reduction presentation `e : reduction (Q P) ≅ Q C` whose adjunct is the
localization of a strict map `z : P ⟶ lim C` is the localization of the ordinary
transpose `g : quotient P ⟶ C` of `z`, composed with the universal comparison `ε`.
The finite evaluations of `g` are the normalized evaluation isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.OrdinaryQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- A map out of the ordinary quotient system whose transpose has the finite scalar
units as projections evaluates to the normalized evaluation isomorphism.
Source: Stacks 03D7, 0941. -/
theorem evaluation_map_of_transpose (M : OrdinaryModel l E W)
    {X : scalarReductionSource l E W} {Y : coefficientSequenceModules l E W}
    (g : M.tensor.obj X ⟶ Y) (n : ℕ)
    (k : (coefficientSequenceEvaluation l E W n).obj Y ⟶ (scalarReductionExtension l E W n).obj X)
    (hg : M.adjunction.unit.app X ≫ (ordinaryLimit l E W).map g ≫
        limit.π ((coefficientSequenceRestriction l E W).obj Y) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app Y ≫
        (scalarReductionRestriction l E W n).map k =
      (scalarReductionExtension_adjunction l E W n).choose.unit.app X)
    (h0 : M.adjunction.unit.app X ≫
        limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj X)) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app (M.tensor.obj X) ≫
        (scalarReductionRestriction l E W n).map ((M.evaluation n).hom.app X) =
      (scalarReductionExtension_adjunction l E W n).choose.unit.app X) :
    (coefficientSequenceEvaluation l E W n).map g ≫ k = (M.evaluation n).hom.app X := by
  let a := (scalarReductionExtension_adjunction l E W n).choose
  let ρ := eqToIso (coefficientSequenceRestriction_evaluation l E W n)
  have hnat : limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj X)) (op n) ≫
      ρ.hom.app (M.tensor.obj X) ≫ (scalarReductionRestriction l E W n).map
        ((coefficientSequenceEvaluation l E W n).map g) =
      (ordinaryLimit l E W).map g ≫ limit.π ((coefficientSequenceRestriction l E W).obj Y) (op n) ≫
        ρ.hom.app Y := by
    have h1 := ρ.hom.naturality g
    dsimp only [Functor.comp_map] at h1
    erw [← h1, Functor.comp_map, lim_map, limMap_π_assoc]
    rfl
  have key : M.adjunction.unit.app X ≫
      limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj X)) (op n) ≫
      ρ.hom.app (M.tensor.obj X) ≫ (scalarReductionRestriction l E W n).map
        ((coefficientSequenceEvaluation l E W n).map g ≫ k) = a.unit.app X := by
    rw [← hg, Functor.map_comp, reassoc_of% hnat]
    rfl
  rw [← cancel_epi ((M.evaluation n).inv.app X), Iso.inv_hom_id_app]
  apply (a.homEquiv X _).injective
  rw [a.homEquiv_unit, a.homEquiv_unit]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  conv_lhs => rw [← h0]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app_assoc]
  exact key

/-- The ordinary adjunction unit followed by a finite projection is the finite scalar unit.
Source: Stacks 03D7, 0941. -/
theorem OrdinaryModel.unit_projection (M : OrdinaryModel l E W)
    (X : scalarReductionSource l E W) (n : ℕ) :
    M.adjunction.unit.app X ≫
        limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj X)) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app (M.tensor.obj X) ≫
        (scalarReductionRestriction l E W n).map ((M.evaluation n).hom.app X) =
      (scalarReductionExtension_adjunction l E W n).choose.unit.app X := by
  have hu := (scalarReductionExtension_adjunction l E W n).choose_spec X
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  exact (M.unit_tensor X n V x).trans (by
    dsimp only [unrestrictedIntegralTensorSection, unrestrictedIntegralReductionFunctor,
      unrestrictedIntegralReductionExistence, scalarReductionExistence] at hu ⊢
    exact (hu V x).symm)

/-- The ordinary transpose of a strict unit presentation evaluates, at every finite level,
to the normalized evaluation isomorphism of the quotient system.
Source: Stacks 03D7, 06YY, 0941. -/
theorem evaluation_mapHomologicalComplex_transpose (M : OrdinaryModel l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (z : P ⟶ ((ordinaryLimit l E W).mapHomologicalComplex (.up ℤ)).obj C) (n : ℕ)
    (k : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ⟶
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)
    (hz : z ≫ (NatTrans.mapHomologicalComplex
        (Functor.whiskerLeft (coefficientSequenceRestriction l E W) (lim.π (op n)))
          (.up ℤ)).app C ≫
        (NatIso.mapHomologicalComplex
          (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) (.up ℤ)).hom.app C ≫
        ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map k =
      ((scalarReductionExtension_adjunction l E W n).choose.mapHomologicalComplex
        (.up ℤ)).unit.app P) :
    ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map
        (((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv P C).symm z) ≫ k =
      (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app P := by
  obtain ⟨g, rfl⟩ : ∃ g, z = (M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv P C g :=
    ⟨_, (Equiv.apply_symm_apply _ _).symm⟩
  rw [Equiv.symm_apply_apply]
  apply HomologicalComplex.hom_ext
  intro p
  have hp := congrArg (fun f ↦ f.f p) hz
  simp only [HomologicalComplex.comp_f] at hp
  rw [HomologicalComplex.comp_f]
  have hg : M.adjunction.unit.app (P.X p) ≫ (ordinaryLimit l E W).map (g.f p) ≫
      limit.π ((coefficientSequenceRestriction l E W).obj (C.X p)) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app (C.X p) ≫
      (scalarReductionRestriction l E W n).map (k.f p) =
      (scalarReductionExtension_adjunction l E W n).choose.unit.app (P.X p) := by
    exact hp
  exact evaluation_map_of_transpose l E W M (g.f p) n (k.f p) hg
    (M.unit_projection l E W (P.X p) n)

/-- The structural limit comparison of the ordinary model is the canonical composite
comparison. Source: Stacks 0941. -/
theorem OrdinaryModel.limitComparison_termwise (M : OrdinaryModel l E W)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    M.limitComparison.hom.app C ≫ (termwiseLimitComparison l E W).inv.app ((tower l E W).obj C) =
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (coefficientSequenceRestriction l E W ⋙
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)))
        (.up ℤ)).inv.app C := by
  rw [← cancel_mono ((termwiseLimitComparison l E W).hom.app ((tower l E W).obj C)),
    Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  apply limit.hom_ext
  intro n
  apply HomologicalComplex.hom_ext
  intro p
  refine (M.limitComparison_projection C n.unop p).trans ?_
  rw [Category.assoc, HomologicalComplex.comp_f]
  erw [termwiseLimitComparison_projection l E W ((tower l E W).obj C) n.unop p]
  exact (Category.id_comp _).symm

/-- The system limit unit is the canonical right-derived unit of inverse limit after
exact restriction, as displayed in strict reduction presentations.
Source: Stacks 0941, 07A6. -/
theorem OrdinaryModel.systemLimitUnit_app (M : OrdinaryModel l E W)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    (systemLimitUnit l E W M (constantLimitUnit l E W)).app C =
      DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (coefficientSequenceRestriction l E W ⋙
              (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)))
            (.up ℤ)).inv.app C) ≫
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W
          ).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj
              (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)) ≫
        (coefficientConstantTowerLimit l E W).map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app C) := by
  rw [← M.limitComparison_termwise l E W C, Functor.map_comp, Category.assoc]
  have hqA : (DerivedCategory.quotientCompQhIso
      (ℕᵒᵖ ⥤ scalarReductionSource l E W)).hom.app ((tower l E W).obj C) = 𝟙 _ := rfl
  have hqiB (K : CochainComplex (scalarReductionSource l E W) ℤ) :
      (DerivedCategory.quotientCompQhIso (scalarReductionSource l E W)).inv.app K = 𝟙 _ := rfl
  have hf : ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomotopyCategoryFactors (.up ℤ)).inv.app
        ((tower l E W).obj C) = 𝟙 _ := rfl
  dsimp only [systemLimitUnit, constantLimitUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.trans_hom, Iso.symm_hom]
  simp only [Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc]
  erw [hqA, hqiB, hf]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.id_comp, Category.id_comp]

/-- A strict unit presentation of a left adjoint of the total limit is the universal
comparison followed by the localized ordinary transpose of its unit map, whose finite
evaluations are the normalized evaluation isomorphisms.
Source: Stacks 03D7, 06YY, 07A6, 0941. -/
theorem exists_transpose_of_unitPresentation (M : OrdinaryModel l E W)
    (L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
    (adj : L ⊣ coefficientSequenceLimit l E W)
    (ε : DerivedCategory.Q ⋙ L ⟶ M.quotient l E W ⋙ DerivedCategory.Q)
    (hhom : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
      (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (f : (M.quotient l E W).obj Q ⟶ I),
      adj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
          (ε.app Q ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
            ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
          (systemLimitUnit l E W M (constantLimitUnit l E W)).app I)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : L.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)
    (h : CoefficientStrictReductionUnitPresentation l E W L adj P C e κ) :
    ∃ g : (M.quotient l E W).obj P ⟶ C,
      e.hom = ε.app P ≫ DerivedCategory.Q.map g ∧
      ∀ n : ℕ, ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map g ≫
          (κ n).hom = (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app P := by
  unfold CoefficientStrictReductionUnitPresentation at h
  obtain ⟨z, h1, h2⟩ := h
  refine ⟨((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv P C).symm z, ?_, fun n ↦
    evaluation_mapHomologicalComplex_transpose l E W M P C z n (κ n).hom (h2 n)⟩
  apply (adj.homEquiv _ _).injective
  rw [h1, hhom, Equiv.apply_symm_apply, M.systemLimitUnit_app l E W C]

end WeilConjectures.OrdinaryQuotient
