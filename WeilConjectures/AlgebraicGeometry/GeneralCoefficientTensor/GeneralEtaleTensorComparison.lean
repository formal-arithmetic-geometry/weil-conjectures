/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientOrdinary.FiniteCoefficientOrdinaryDirectImage
public import WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
import Mathlib.RingTheory.Flat.Stability
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! # Fixed ordinary coefficient tensor comparison

Source: Stacks 06YY and 07A4; thm-coef-finite-hom, paragraphs 1 and 4.
(blueprint: lem-coef-general-etale-tensor-comparison).
The scalar functor is the fixed left adjoint of ordinary derived restriction.
Only the ordinary preservation lemmas and the generic derived tensor theorem are used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale.GeneralCoefficientTensor

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

/-- Ordinary sheafified extension of coefficients. Source: Stacks 03EK
(blueprint: lem-coef-general-etale-tensor-comparison). -/
abbrev ordinary (φ : A →+* B) (X : Scheme.{u}) :=
  ProEtale.etaleSheafExtendScalars φ X

/-- Additivity follows from the adjunction to additive ordinary restriction.
Source: Stacks 03EK (blueprint: lem-coef-general-etale-tensor-comparison). -/
instance ordinary_additive (φ : A →+* B) (X : Scheme.{u}) :
    (ordinary φ X).Additive :=
  (ProEtale.etaleSheafExtendScalarsAdjunction φ X).left_adjoint_additive

/-- The specified fixed derived extension. Source: Stacks 06YY
(blueprint: lem-coef-general-etale-tensor-comparison). -/
abbrev scalar (φ : A →+* B) (X : Scheme.{u}) :=
  CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ

/-- Ordinary extension preserves flat sheaves, as checked on geometric stalks.
Source: Stacks 03EK, 06YY (blueprint: lem-coef-general-etale-tensor-comparison).
Proof: the stalk of extension is extension of the stalk; base extension preserves flatness. -/
theorem ordinary_preservesFlat {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ X).PreservesFlat := by
  constructor
  intro M hM
  apply (flat_iff_forall_flat_sheafFiber_obj _).2
  intro Ω _ _ s
  let p : X.smallEtaleTopology.Point.{u + 1} :=
    (Scheme.pointSmallEtale s).ulift.{u + 1}
  let E : ModuleCat.{u + 1} A ⥤ ModuleCat.{u + 1} B :=
    ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ
  let : E.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).isLeftAdjoint
  let W := (Functor.whiskeringRight X.Etaleᵒᵖ (ModuleCat.{u + 1} A)
    (ModuleCat.{u + 1} B)).obj E
  let q := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let a := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)
  let e₀ := p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} B)
  let e₁ := p.presheafFiberCompIso E
  let e : ProEtale.etaleSheafExtendScalars φ X ⋙ p.sheafFiber ≅
      p.sheafFiber ⋙ E :=
    Functor.associator q (W ⋙ a) p.sheafFiber ≪≫
      Functor.isoWhiskerLeft q (Functor.associator W a p.sheafFiber) ≪≫
      Functor.isoWhiskerLeft q (Functor.isoWhiskerLeft W e₀) ≪≫
      Functor.isoWhiskerLeft q e₁ ≪≫
      (Functor.associator q p.presheafFiber E).symm
  exact ObjectProperty.prop_of_iso _ (e.app M).symm
    (extension_flat φ _ ((flat_iff_forall_flat_sheafFiber_obj M).1 hM s))

/-- Ordinary extension preserves quasi-isomorphisms between K-flat complexes.
Source: Stacks 06YY (blueprint: lem-coef-general-etale-tensor-comparison).
Proof: after exact faithful restriction it is tensor with the constant B-module;
K-flatness makes the tensor of the acyclic cone acyclic. -/
theorem ordinary_preservesKFlatQuasiIso (φ : A →+* B) (X : Scheme.{u}) :
    (ordinary φ X).PreservesKFlatQuasiIso := by
  let := φ.toAlgebra
  have : HasCountableCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨fun _ _ ↦ (inferInstance : HasColimitsOfSize.{0, 0}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))).has_colimits_of_shape _⟩
  constructor
  intro P Q hP hQ f hf
  exact CochainComplex.quasiIso_map_of_iso_tensorRight _ _
    (Sheaf.extendScalarsCompRestrictScalarsIso X.smallEtaleTopology A B) f hP hQ

attribute [local instance] ordinary_preservesFlat ordinary_preservesKFlatQuasiIso

/-- The adjunction-compatible identification with the total left derived functor.
Source: Stacks 06YY (blueprint: lem-coef-general-etale-tensor-comparison). -/
def modelIso (φ : A →+* B) (X : Scheme.{u}) :
    scalar φ X ≅ (ordinary φ X).leftDerivedFunctor :=
  (FiniteCoefficientOrdinary.scalarAdjunction X.smallEtaleTopology φ).leftAdjointUniq
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ X).derivedAdjunction.ofNatIsoRight
      (Sheaf.restrictScalars X.smallEtaleTopology φ).rightDerivedFunctorIsoMapDerivedCategory)

/-- The universal cochain counit of this fixed extension.
Source: Stacks 06YY (blueprint: lem-coef-general-etale-tensor-comparison). -/
def modelCounit (φ : A →+* B) (X : Scheme.{u})
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  (modelIso φ X).hom.app (_root_.DerivedCategory.Q.obj P) ≫
    (ordinary φ X).rightExact_cochainCounit P

/-- Binary comparison with the coefficient order fixed by ordinary balancing.
Source: Stacks 07A4 (blueprint: lem-coef-general-etale-tensor-comparison). -/
abbrev TensorFamily (φ : A →+* B) (X : Scheme.{u}) :=
  ∀ K L : DerivedCategoryModule A X,
    ((derivedTensor (ModuleCat B) X).obj ((scalar φ X).obj K)).obj
        ((scalar φ X).obj L) ≅
      (scalar φ X).obj (((derivedTensor (ModuleCat A) X).obj K).obj L)

/-- Naturality and the full flat-term K-flat normalization determine the family.
Source: Stacks 06YY, 07A4 (blueprint: lem-coef-general-etale-tensor-comparison). -/
def Canonical (φ : A →+* B) (X : Scheme.{u}) (μ : TensorFamily φ X) : Prop :=
  (∀ {K K' : DerivedCategoryModule A X} (f : K ⟶ K') (L : DerivedCategoryModule A X),
    ((derivedTensor (ModuleCat B) X).map ((scalar φ X).map f)).app
        ((scalar φ X).obj L) ≫ (μ K' L).hom =
      (μ K L).hom ≫ (scalar φ X).map (((derivedTensor (ModuleCat A) X).map f).app L)) ∧
  (∀ (K : DerivedCategoryModule A X) {L L' : DerivedCategoryModule A X} (f : L ⟶ L'),
    ((derivedTensor (ModuleCat B) X).obj ((scalar φ X).obj K)).map
        ((scalar φ X).map f) ≫ (μ K L').hom =
      (μ K L).hom ≫ (scalar φ X).map (((derivedTensor (ModuleCat A) X).obj K).map f)) ∧
  (letI := (ProEtale.etaleSheafExtendScalarsAdjunction φ X).isLeftAdjoint
   letI := (ProEtale.etaleSheafExtendScalarsAdjunction φ X).leftAdjointOplaxMonoidal
   Functor.rightExactTensorModelNormalization (ordinary φ X) (scalar φ X)
     (modelCounit φ X) μ)

/-- Existence and uniqueness of the normalized fixed-coefficient comparison.
Source: Stacks 06YY, 07A4 (blueprint: lem-coef-general-etale-tensor-comparison).
Proof: ordinary sheafified scalar extension is strong monoidal, preserves flat sheaves
and K-flat quasi-isomorphisms. Derive its ordinary oplax tensorator and transport it
along the unique adjunction-compatible modelIso. The generic derived tensor theorem
proves both naturality equations and the normalization, and proves uniqueness by
cancellation on flat-term K-flat representatives followed by naturality on resolutions.
-/
theorem existsUnique (φ : A →+* B) (X : Scheme.{u}) :
    ∃! μ : TensorFamily φ X, Canonical φ X μ := by
  let E := ordinary φ X
  let : E.IsLeftAdjoint := (ProEtale.etaleSheafExtendScalarsAdjunction φ X).isLeftAdjoint
  let : E.OplaxMonoidal :=
    (ProEtale.etaleSheafExtendScalarsAdjunction φ X).leftAdjointOplaxMonoidal
  let : E.Monoidal := CategoryTheory.composeAndSheafifyMonoidal X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)
  have h := Functor.rightExact_tensorComparison_existsUnique E (scalar φ X)
    (modelIso φ X) (modelCounit φ X) (fun _ ↦ rfl)
  exact h

/-- The unique normalized family; its data is fixed by the full model equation.
Source: Stacks 07A4 (blueprint: lem-coef-general-etale-tensor-comparison). -/
def comparison (φ : A →+* B) (X : Scheme.{u}) : TensorFamily φ X :=
  (existsUnique φ X).choose

/-- The defining naturality and normalization equations.
Source: Stacks 07A4 (blueprint: lem-coef-general-etale-tensor-comparison). -/
theorem comparison_canonical (φ : A →+* B) (X : Scheme.{u}) :
    Canonical φ X (comparison φ X) :=
  (existsUnique φ X).choose_spec.1

end AlgebraicGeometry.Etale.GeneralCoefficientTensor
