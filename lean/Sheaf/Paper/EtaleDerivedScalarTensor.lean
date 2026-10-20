/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q158
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Paper.WitnessCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange

/-!
# Ordinary derived scalar extension in the constant-coefficient presentation

Source: Stacks Project, Tags 03EK and 06YY
(blueprint: lem-pur-derived-change-of-rings).
The general ring-sheaf interface is reexported. The additional interface uses
ModuleCat-valued sheaves and fixes the scalar/tensor comparison on K-flat representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.mapDerivedCategory

/-- Additivity of the existing sheafified sectionwise scalar extension.
Source: Stacks 03EK (blueprint: lem-pur-derived-change-of-rings).
Proof: its adjunction to additive restriction implies additivity. -/
@[instance] theorem scalarSheafExtension_additive
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ T).Additive := by
  exact (ProEtale.etaleSheafExtendScalarsAdjunction φ T).left_adjoint_additive

/-- The published scalar-extension functor in the small-etale specialization.
This is an abbreviation for the existing chosen left adjoint, not a new construction.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
abbrev scalarExtension
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule B T :=
  ProEtale.pbcFixedScalarExtension T.smallEtaleTopology φ

/-- B as an A-module sheaf, using actual exact restriction of scalars.
Source: Stacks 03EK (blueprint: lem-pur-derived-change-of-rings). -/
def scalarCoefficientSheaf
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
    (𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)))

/-- B_T[0], with its restricted A-action.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def scalarCoefficient
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) : DerivedCategoryModule A T :=
  (_root_.DerivedCategory.singleFunctor _ 0).obj (scalarCoefficientSheaf φ T)

/-- The ordinary balancing map M tensor_A B to the restricted scalar extension.
It is scalar unit, followed by the lax tensorator of restriction and the right unitor.
Source: Stacks 03EK (blueprint: lem-pur-derived-change-of-rings). -/
def scalarSheafTensorMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    M ⊗ scalarCoefficientSheaf φ T ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
        ((ProEtale.etaleSheafExtendScalars φ T).obj M) :=
  (ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app M ▷
      scalarCoefficientSheaf φ T ≫
    Functor.LaxMonoidal.μ (Sheaf.restrictScalars T.smallEtaleTopology φ)
      ((ProEtale.etaleSheafExtendScalars φ T).obj M) (𝟙_ _) ≫
    (Sheaf.restrictScalars T.smallEtaleTopology φ).map (ρ_ _).hom

private theorem balancing_naturality
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [R.LaxMonoidal] (adj : L ⊣ R)
    {M N : C} (a : M ⟶ N) :
    a ▷ R.obj (𝟙_ D) ≫
        (adj.unit.app N ▷ R.obj (𝟙_ D) ≫
          Functor.LaxMonoidal.μ R (L.obj N) (𝟙_ D) ≫ R.map (ρ_ (L.obj N)).hom) =
      (adj.unit.app M ▷ R.obj (𝟙_ D) ≫
          Functor.LaxMonoidal.μ R (L.obj M) (𝟙_ D) ≫ R.map (ρ_ (L.obj M)).hom) ≫
        R.map (L.map a) := by
  have hn : a ≫ adj.unit.app N = adj.unit.app M ≫ R.map (L.map a) :=
    adj.unit.naturality a
  rw [← comp_whiskerRight_assoc, hn]
  rw [comp_whiskerRight_assoc, Functor.LaxMonoidal.μ_natural_left_assoc]
  rw [← R.map_comp, rightUnitor_naturality, R.map_comp]
  simp only [Category.assoc]

/-- Naturality of the balancing map.
Source: Stacks 03EK (blueprint: lem-pur-derived-change-of-rings).
Proof: apply naturality of the scalar unit, the lax tensorator, and the right unitor.
On sections this is (m tensor b) maps to b tensor a(m). -/
theorem scalarSheafTensorMap_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)} (a : M ⟶ N) :
    a ▷ scalarCoefficientSheaf φ T ≫ scalarSheafTensorMap φ T N =
      scalarSheafTensorMap φ T M ≫
        (Sheaf.restrictScalars T.smallEtaleTopology φ).map
          ((ProEtale.etaleSheafExtendScalars φ T).map a) := by
  exact balancing_naturality (ProEtale.etaleSheafExtendScalarsAdjunction φ T) a

/-- The ordinary balancing map, as a natural transformation.
Source: Stacks 03EK (blueprint: lem-pur-derived-change-of-rings). -/
def scalarSheafTensorTransformation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    tensorRight (scalarCoefficientSheaf φ T) ⟶
      ProEtale.etaleSheafExtendScalars φ T ⋙ Sheaf.restrictScalars T.smallEtaleTopology φ where
  app := scalarSheafTensorMap φ T
  naturality _ _ a := scalarSheafTensorMap_naturality φ T a

/-- The scalar adjunction unit on complex representatives before transposition.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def scalarDerivedRepresentativeUnit
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    {F : D ⥤ E} {U : E ⥤ D} [F.Additive] [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] (adj : F ⊣ U) :
    _root_.DerivedCategory.Q (C := D) ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q (C := E) ⋙
        U.mapDerivedCategory :=
  Functor.whiskerRight
      ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv ≫
        NatTrans.mapHomologicalComplex adj.unit (.up ℤ) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ U)) (.up ℤ)).inv)
      _root_.DerivedCategory.Q ≫
    Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ)) U.mapDerivedCategoryFactors.inv

/-- Transposition packages all representative maps into one natural transformation.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def scalarDerivedRepresentativeTransformation
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    {F : D ⥤ E} {U : E ⥤ D} [F.Additive] [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] (adj : F ⊣ U)
    {L : _root_.DerivedCategory D ⥤ _root_.DerivedCategory E}
    (ad : L ⊣ U.mapDerivedCategory) :
    _root_.DerivedCategory.Q ⋙ L ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q where
  app P := (ad.homEquiv _ _).symm ((scalarDerivedRepresentativeUnit adj).app P)
  naturality C C' h := ad.homEquiv_naturality_right_square
    (_root_.DerivedCategory.Q.map h) ((scalarDerivedRepresentativeUnit adj).app C')
    ((scalarDerivedRepresentativeUnit adj).app C)
    (_root_.DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map h))
    ((scalarDerivedRepresentativeUnit adj).naturality h)

/-- The canonical scalar representative transformation with concrete sheaf complex functors.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def scalarExtensionRepresentativeTransformation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    _root_.DerivedCategory.Q ⋙ scalarExtension φ T ⟶
      (ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ) ⋙
        _root_.DerivedCategory.Q :=
  scalarDerivedRepresentativeTransformation
      (ProEtale.etaleSheafExtendScalarsAdjunction φ T)
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))

/-- The derived-extension counit on a cochain representative, including the quotient factor.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def scalarExtensionRepresentative
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (scalarExtension φ T).obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) :=
  (scalarExtensionRepresentativeTransformation φ T).app P

/-- Exact restriction of the scalar-extension representative map.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def scalarRestrictedExtensionRepresentative
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).obj
        ((scalarExtension φ T).obj (_root_.DerivedCategory.Q.obj P)) ⟶
      _root_.DerivedCategory.Q.obj
        (((ProEtale.etaleSheafExtendScalars φ T ⋙
          Sheaf.restrictScalars T.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).obj P) :=
  (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map
      (scalarExtensionRepresentative φ T P) ≫
    (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.hom.app
      (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) ≫
    _root_.DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (ProEtale.etaleSheafExtendScalars φ T ⋙
          Sheaf.restrictScalars T.smallEtaleTopology φ)) (.up ℤ)).hom.app P)


/-- Tensoring with F[0], in the general monoidal-category interface.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def scalarTensorModelFunctor
    {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (F : C) : _root_.DerivedCategory C ⥤ _root_.DerivedCategory C :=
  tensorRight ((_root_.DerivedCategory.singleFunctor C 0).obj F)

/-- Normalization by the ordinary balancing map on cochain representatives.
This general helper shares the monoidal data with the tensor-model API before specialization.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def scalarTensorModelNormalization
    {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (F : C) {V : C ⥤ C} [V.Additive]
    (τ : tensorRight F ⟶ V) {G : _root_.DerivedCategory C ⥤ _root_.DerivedCategory C}
    (e : G ≅ scalarTensorModelFunctor F)
    (r : ∀ P : CochainComplex C ℤ,
      G.obj (_root_.DerivedCategory.Q.obj P) ⟶
        _root_.DerivedCategory.Q.obj ((V.mapHomologicalComplex (.up ℤ)).obj P)) : Prop :=
  ∀ P : CochainComplex C ℤ,
    e.hom.app (_root_.DerivedCategory.Q.obj P) ≫
        Functor.LaxMonoidal.μ (_root_.DerivedCategory.Q (C := C)) P
          ((HomologicalComplex.single C (.up ℤ) 0).obj F) ≫
        _root_.DerivedCategory.Q.map
          ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor C) F).hom.app P) ≫
        _root_.DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app P) = r P

private theorem tensor_model_eq
    (D : Type w) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology D) :
    (derivedTensor D T).flip.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F) =
      scalarTensorModelFunctor F := by
  rfl

/-- The site-specific tensor and the general tensor-model functor have the same data.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings).
Proof: unfold derivedTensor, scalarCoefficient and scalarTensorModelFunctor.
Both sides are curriedTensor on the same derived monoidal structure, with its
second argument the restricted B-unit sheaf in degree zero. -/
theorem scalarTensorFunctor_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (derivedTensor (ModuleCat.{u + 1} A) T).flip.obj (scalarCoefficient φ T) =
      scalarTensorModelFunctor (scalarCoefficientSheaf φ T) := by
  exact tensor_model_eq (ModuleCat.{u + 1} A) T (scalarCoefficientSheaf φ T)

/-- The scalar/tensor comparison is uniquely fixed on K-flat representatives.
Source: Stacks 06YY, using 03EK (blueprint: lem-pur-derived-change-of-rings).
Proof: the ordinary balancing map sends m tensor b to b tensor m and is an
isomorphism after sheafification. Apply it termwise to a K-flat resolution P.
The left-derived counit computes scalar extension on P. The canonical lax tensorator
of Q, followed by the total-tensor/single-complex comparison, is the tensor-model
isomorphism on K-flat P. Exact restriction
commutes with Q. These maps yield the displayed normalized isomorphism. For a
quasi-isomorphism between K-flat resolutions all maps commute by naturality, so
localization gives a natural isomorphism independent of the resolution. Naturality
with respect to a K-flat resolution gives the normalization on every complex. Every
object has such a resolution; the same equations determine every component,
which proves uniqueness of the natural isomorphism. -/
theorem scalarTensorIso_existsUnique
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    ∃! e : scalarExtension φ T ⋙ Sheaf.derivedRestrictScalars T.smallEtaleTopology φ ≅
        (derivedTensor (ModuleCat.{u + 1} A) T).flip.obj (scalarCoefficient φ T),
      scalarTensorModelNormalization (scalarCoefficientSheaf φ T)
        (scalarSheafTensorTransformation φ T)
        (e ≪≫ eqToIso (scalarTensorFunctor_eq φ T))
        (scalarRestrictedExtensionRepresentative φ T) := by
  sorry

/-- Canonical scalar/tensor identification; its defining theorem determines it uniquely.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def scalarTensorIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    scalarExtension φ T ⋙ Sheaf.derivedRestrictScalars T.smallEtaleTopology φ ≅
      (derivedTensor (ModuleCat.{u + 1} A) T).flip.obj (scalarCoefficient φ T) :=
  (scalarTensorIso_existsUnique φ T).choose

end AlgebraicGeometry.Etale
