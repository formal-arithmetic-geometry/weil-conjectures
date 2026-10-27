/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.Paper.DerivedPullbackTensorHom
import all Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ConstantCoefficientObjectsConstructible
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
import Sheaf.Paper.SfScalarExtensionComposition
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Data.Fintype.Order
import Sheaf.CategoryTheory.ScalarLocalization
import Sheaf.NumberTheory.Padics.FiniteCoefficientFields

/-! # Finite product descent to field coefficients

Source: blueprint main-20261015, def-pur-section-invariant, final invertibility assertion,
finite-clopen transport steps 10--11
(blueprint: lem-pur-finite-product-field-coefficient-descent).

The categories and all three coefficient-stage operations are the recorded intrinsic
constructions. In particular rationalization is raw and common-stage objects are pairs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u w

open CategoryTheory AlgebraicGeometry TensorProduct
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures
namespace FiniteProductFieldDescent

variable (P : PurityFiniteSetting.{u})

/-- The source-implied inverse of ell in each residue field, transported from the
published stalk unit along the residue homomorphism. This supplies no extra assumption.
Source: purity conventions, ell different from p
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
@[instance_reducible]
def residueInvertible (Y : Over (Spec (CommRingCat.of P.field.k))) (y : Y.left) :
    Invertible (P.coefficients.l : Y.left.residueField y) :=
  letI := (P.coefficientPrime_isUnit_stalk Y.left Y.hom y).invertible
  (Invertible.map (IsLocalRing.residue (Y.left.presheaf.stalk y))
    (P.coefficients.l : Y.left.presheaf.stalk y)).copy _ (map_natCast _ _).symm

attribute [instance] residueInvertible

/-- The recorded integral constructible category, at the canonical small model of E.
Source: blueprint coefficient conventions
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def integralCategory (E : Index P.coefficients.l P.coefficients.Qbar)
    (Y : Over (Spec (CommRingCat.of P.field.k))) :=
  sfIntegralConstructibleCategory P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) Y.left

/-- Cache the inherited Category structure on the specialized integral category.
Source: blueprint coefficient categories
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
instance integralCategoryStructure (E : Index P.coefficients.l P.coefficients.Qbar)
    (Y : Over (Spec (CommRingCat.of P.field.k))) :
    Category.{u + 2} (integralCategory P E Y) :=
  ObjectProperty.FullSubcategory.category
    (sfIntegralConstructible P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) Y.left)

/-- Cache the inherited Preadditive structure on the specialized integral category.
Source: blueprint coefficient categories
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
instance integralPreadditive (E : Index P.coefficients.l P.coefficients.Qbar)
    (Y : Over (Spec (CommRingCat.of P.field.k))) :
    Preadditive (integralCategory P E Y) :=
  inferInstanceAs (Preadditive (sfIntegralConstructibleCategory P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) Y.left))

/-- Cache the inherited Linear structure on the specialized integral category.
Source: blueprint coefficient categories
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
instance integralLinear (E : Index P.coefficients.l P.coefficients.Qbar)
    (Y : Over (Spec (CommRingCat.of P.field.k))) :
    Linear (Padic.coefficientExtensionIntegers P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E)) (integralCategory P E Y) :=
  sfIntegralConstructibleLinear P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) Y.left

/-- The recorded raw rational category, at the canonical small model of E.
Source: blueprint coefficient conventions
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def rationalCategory (E : Index P.coefficients.l P.coefficients.Qbar)
    (Y : Over (Spec (CommRingCat.of P.field.k))) :=
  sfRationalConstructibleCategory P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) Y.left

/-- Cache the inherited Category structure on the specialized rational category.
Source: blueprint coefficient categories
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
instance rationalCategoryStructure (E : Index P.coefficients.l P.coefficients.Qbar)
    (Y : Over (Spec (CommRingCat.of P.field.k))) :
    Category.{u + 2} (rationalCategory P E Y) :=
  ScalarLocalization.category
    (Padic.coefficientExtensionIntegers P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E))
    (integralCategory P E Y)
    (Padic.coefficientExtensionUniformizer P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E))

/-- Cache the inherited Preadditive structure on the specialized rational category.
Source: blueprint coefficient categories
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
instance rationalPreadditive (E : Index P.coefficients.l P.coefficients.Qbar)
    (Y : Over (Spec (CommRingCat.of P.field.k))) :
    Preadditive (rationalCategory P E Y) :=
  inferInstanceAs (Preadditive (sfRationalConstructibleCategory P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) Y.left))

/-- The recorded completed tensor, at the canonical small model of E.
Source: blueprint coefficient conventions
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def integralTensor (E : Index P.coefficients.l P.coefficients.Qbar)
    (Y : Over (Spec (CommRingCat.of P.field.k))) :
    integralCategory P E Y × integralCategory P E Y ⥤ integralCategory P E Y :=
  constructibleIntegralTensor P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) Y.left

/-- The recorded rational tensor, at the canonical small model of E.
Source: blueprint coefficient conventions
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def rationalTensor (E : Index P.coefficients.l P.coefficients.Qbar)
    (Y : Over (Spec (CommRingCat.of P.field.k))) :
    rationalCategory P E Y × rationalCategory P E Y ⥤ rationalCategory P E Y :=
  rationalDerivedTensor P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) Y.left

/-- The actual integral component restriction, without choosing an equivalence.
Source: blueprint finite-clopen coefficient transport
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def integralRestriction (E : Index P.coefficients.l P.coefficients.Qbar)
    {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :
    integralCategory P E X ⥤ integralCategory P E Y :=
  constructibleIntegralPullback P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) j.left

/-- The actual rational component restriction, without choosing an equivalence.
Source: blueprint finite-clopen coefficient transport
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def rationalRestriction (E : Index P.coefficients.l P.coefficients.Qbar)
    {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :
    rationalCategory P E X ⥤ rationalCategory P E Y :=
  rationalDerivedPullback P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) j.left

/-- The recorded completed integral scalar transition on the constructible subcategory.
Source: blueprint coefficient extensions
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def integralScalar (E L : Index P.coefficients.l P.coefficients.Qbar) (h : E ≤ L)
    (Y : Over (Spec (CommRingCat.of P.field.k))) :
    integralCategory P E Y ⥤ integralCategory P L Y :=
  GeneralAlgebraicallyClosedCoefficients.integralTransition
    P.coefficients.l P.coefficients.Qbar Y.left E L h

/-- The actual regular completed module, with its published constructibility witness.
Source: blueprint coefficient unit
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def integralUnit (E : Index P.coefficients.l P.coefficients.Qbar)
    (Y : Over (Spec (CommRingCat.of P.field.k))) : integralCategory P E Y :=
  ⟨integralConstantCoefficientObject P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) Y.left,
    (integralConstantCoefficient_constructible P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) Y.left
      P.field P.coefficients.different).2.1⟩

/-- The raw localization functor, retaining the integral object set.
Source: blueprint rationalization Hom formula
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def localization (E : Index P.coefficients.l P.coefficients.Qbar)
    (Y : Over (Spec (CommRingCat.of P.field.k))) :
    integralCategory P E Y ⥤ rationalCategory P E Y :=
  sfRationalConstructibleLocalization P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) Y.left

/-- The existing common-stage category at a k-scheme, with independent finite index size.
Source: blueprint common-stage coefficient categories
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def commonCategory (Y : Over (Spec (CommRingCat.of P.field.k))) :=
  generalAlgebraicallyClosedConstructibleCategory P.coefficients.l P.coefficients.Qbar Y.left

/-- Cache the actual category structure on the specialized pair category.
Source: blueprint common-stage coefficient categories
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
instance commonCategoryStructure (Y : Over (Spec (CommRingCat.of P.field.k))) :
    Category.{u + 2} (commonCategory P Y) :=
  GeneralAlgebraicallyClosedCoefficients.pairCategory
    P.coefficients.l P.coefficients.Qbar Y.left

/-- The actual common-stage restriction, on the recorded pair category.
Source: blueprint common-stage coefficient transport
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def commonRestriction {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :
    commonCategory P X ⥤ commonCategory P Y :=
  commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar j.left

/-- The canonical integral pullback/scalar comparison, not an arbitrary map.
Source: blueprint integral scalar comparisons
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def pullbackScalar (E L : Index P.coefficients.l P.coefficients.Qbar) (h : E ≤ L)
    {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X)
    (K : integralCategory P E X) :
    (integralScalar P E L h Y).obj ((integralRestriction P E j).obj K) ≅
      (integralRestriction P L j).obj ((integralScalar P E L h X).obj K) :=
  integralPullbackScalarComparison P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E)
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar L)
    (coefficientInclusion P.coefficients.l P.coefficients.Qbar E L h) j.left K

/-- The canonical integral tensor/scalar comparison.
Source: blueprint integral scalar comparisons
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def tensorScalar (E L : Index P.coefficients.l P.coefficients.Qbar) (h : E ≤ L)
    (Y : Over (Spec (CommRingCat.of P.field.k))) (M N : integralCategory P E Y) :
    (integralScalar P E L h Y).obj ((integralTensor P E Y).obj (M, N)) ≅
      (integralTensor P L Y).obj
        ((integralScalar P E L h Y).obj M, (integralScalar P E L h Y).obj N) :=
  integralTensorScalarComparison P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E)
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar L)
    (coefficientInclusion P.coefficients.l P.coefficients.Qbar E L h) Y.left M N

variable (X : Over (Spec (CommRingCat.of P.field.k)))
  {I : Type w} [Finite I]
  (Xi : I → Over (Spec (CommRingCat.of P.field.k))) (j : ∀ i, Xi i ⟶ X)

/-- Cache the existing category structures for the component family; this is pointwise
instance inference, with no new categorical data.
Source: blueprint finite-product coefficient categories
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
instance integralFamily (E : Index P.coefficients.l P.coefficients.Qbar)
    (Y : I → Over (Spec (CommRingCat.of P.field.k))) :
    ∀ i, Category.{u + 2} (integralCategory P E (Y i)) := fun _i ↦ inferInstance

/-- Cache the existing category structures for the component family; this is pointwise
instance inference, with no new categorical data.
Source: blueprint finite-product coefficient categories
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
instance rationalFamily (E : Index P.coefficients.l P.coefficients.Qbar)
    (Y : I → Over (Spec (CommRingCat.of P.field.k))) :
    ∀ i, Category.{u + 2} (rationalCategory P E (Y i)) := fun _i ↦ inferInstance

/-- Cache the recorded pair-category structure for each component.
Source: blueprint finite-product common-stage categories
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
instance commonFamily (Y : I → Over (Spec (CommRingCat.of P.field.k))) :
    ∀ i, Category.{u + 2} (commonCategory P (Y i)) := fun _i ↦ inferInstance

/-- The assumed integral comparisons, bundled without changing their objects or maps.
The last two equations are precisely preservation of integral scalar extension by
restriction's tensor and unit comparisons. Scalar pullback and tensor comparisons
are the normalized published ones. The unit scalar comparison is included as part
of the assumed coefficient-unit preservation, at each scheme occurring in the cover.
Source: blueprint finite-clopen transport, hypothesis of steps 10--11
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
structure IntegralComparisons where
  equivalence : ∀ E : Index P.coefficients.l P.coefficients.Qbar,
    (Functor.pi' (A := integralCategory P E X)
      (C := fun i : I ↦ integralCategory P E (Xi i))
      (fun i : I ↦ integralRestriction P E (j i))).IsEquivalence
  linear : ∀ (E : Index P.coefficients.l P.coefficients.Qbar) (i : I),
    (integralRestriction P E (j i)).Linear
      (Padic.coefficientExtensionIntegers P.coefficients.l
        (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E))
  tensor : ∀ (E : Index P.coefficients.l P.coefficients.Qbar) (i : I),
    integralTensor P E X ⋙ integralRestriction P E (j i) ≅
      ((integralRestriction P E (j i)).prod (integralRestriction P E (j i))) ⋙
        integralTensor P E (Xi i)
  unit : ∀ (E : Index P.coefficients.l P.coefficients.Qbar) (i : I),
    (integralRestriction P E (j i)).obj (integralUnit P E X) ≅ integralUnit P E (Xi i)
  sourceScalarUnit : ∀ (E L : Index P.coefficients.l P.coefficients.Qbar) (h : E ≤ L),
    (integralScalar P E L h X).obj (integralUnit P E X) ≅ integralUnit P L X
  componentScalarUnit : ∀ (E L : Index P.coefficients.l P.coefficients.Qbar) (h : E ≤ L)
    (i : I),
    (integralScalar P E L h (Xi i)).obj (integralUnit P E (Xi i)) ≅ integralUnit P L (Xi i)
  tensor_scalar : ∀ (E L : Index P.coefficients.l P.coefficients.Qbar) (h : E ≤ L)
    (i : I) (M N : integralCategory P E X),
    (integralScalar P E L h (Xi i)).map ((tensor E i).hom.app (M, N)) ≫
        (tensorScalar P E L h (Xi i)
          ((integralRestriction P E (j i)).obj M)
          ((integralRestriction P E (j i)).obj N)).hom ≫
        (integralTensor P L (Xi i)).map
          (Prod.mkHom (pullbackScalar P E L h (j i) M).hom
            (pullbackScalar P E L h (j i) N).hom) =
      (pullbackScalar P E L h (j i) ((integralTensor P E X).obj (M, N))).hom ≫
        (integralRestriction P L (j i)).map (tensorScalar P E L h X M N).hom ≫
        (tensor L i).hom.app
          ((integralScalar P E L h X).obj M, (integralScalar P E L h X).obj N)
  unit_scalar : ∀ (E L : Index P.coefficients.l P.coefficients.Qbar) (h : E ≤ L) (i : I),
    (integralScalar P E L h (Xi i)).map (unit E i).hom ≫ (componentScalarUnit E L h i).hom =
      (pullbackScalar P E L h (j i) (integralUnit P E X)).hom ≫
        (integralRestriction P L (j i)).map (sourceScalarUnit E L h).hom ≫ (unit L i).hom

variable [hft : LocallyOfFiniteType X.hom] [hqc : QuasiCompact X.hom]
  [hopen : ∀ i, IsOpenImmersion (j i).left]
  [hclosed : ∀ i, IsClosedImmersion (j i).left]
  (hdisjoint : ∀ i i', i ≠ i' → Disjoint (Set.range (j i).left) (Set.range (j i').left))
  (hcover : (⋃ i, Set.range (j i).left) = Set.univ)
  (H : IntegralComparisons P X Xi j)

section Generic
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] integralDerivedPullback integralCompletedTensor
  integralScalarExtension integralOrdinaryScalar completedIntegralCoefficientSheafUnrestricted


private theorem rawBifunctorIso
    {R : Type*} [CommRing R] {C D : Type*} [Category C] [Preadditive C] [Linear R C]
    [Category D] [Preadditive D] [Linear R D] (t : R)
    (U V : C × C ⥤ D) (e : U ≅ V)
    (F G : ScalarLocalization R C t × ScalarLocalization R C t ⥤
      ScalarLocalization R D t)
    (hF : ∀ M N, F.obj (M, N) = ⟨U.obj (M.obj, N.obj)⟩)
    (hG : ∀ M N, G.obj (M, N) = ⟨V.obj (M.obj, N.obj)⟩)
    (bF : ∀ M M' N N',
      ∃ b : (M ⟶ M') →+ (N ⟶ N') →+
        (F.obj (M, N) ⟶ F.obj (M', N')),
        (∀ f g, F.map (Prod.mkHom f g) = b f g) ∧
        ∀ (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (c d : Localization.Away t),
          HEq (b (c ⊗ₜ[R] f) (d ⊗ₜ[R] g)) ((c * d) ⊗ₜ[R] U.map (Prod.mkHom f g)))
    (bG : ∀ M M' N N',
      ∃ b : (M ⟶ M') →+ (N ⟶ N') →+
        (G.obj (M, N) ⟶ G.obj (M', N')),
        (∀ f g, G.map (Prod.mkHom f g) = b f g) ∧
        ∀ (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (c d : Localization.Away t),
          HEq (b (c ⊗ₜ[R] f) (d ⊗ₜ[R] g)) ((c * d) ⊗ₜ[R] V.map (Prod.mkHom f g))) :
    ∃! a : F ≅ G, ∀ M N, HEq (a.hom.app (M, N))
      ((ScalarLocalization.localization R D t).map (e.hom.app (M.obj, N.obj)))  := by
  obtain ⟨a, ha, hu⟩ := rawBilinearIso_existsUnique t t id U V e F G
    (fun K ↦ hF K.1 K.2) (fun K ↦ hG K.1 K.2) bF bG
  refine ⟨a, fun M N ↦ ha (M, N), ?_⟩
  intro a' ha'
  exact hu a' (fun K ↦ ha' K.1 K.2)

private theorem map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B A' B' : C} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst A'
  subst B'
  cases h
  rfl

private theorem prod_heq {C : Type u} [Category.{w} C]
    {A B A' B' D E D' E' : C}
    (hA : A = A') (hB : B = B') (hD : D = D') (hE : E = E')
    {f : A ⟶ B} {f' : A' ⟶ B'} {g : D ⟶ E} {g' : D' ⟶ E'}
    (hf : HEq f f') (hg : HEq g g') : HEq (Prod.mkHom f g) (Prod.mkHom f' g') := by
  subst A'
  subst B'
  subst D'
  subst E'
  cases hf
  cases hg
  rfl

attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  sfRationalScalarExtension commonStageDerivedPullback commonStageDerivedTensor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rationalDerivedPullbackSpec (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    let F := rationalDerivedPullback l E f;
      F.Additive ∧
      (∀ K, F.obj K = ⟨(constructibleIntegralPullback l E f).obj K.obj⟩) ∧
      (∀ (K L : sfIntegralConstructibleCategory l E Y) (a : K ⟶ L)
        (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
        HEq (F.map (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a :
          (sfRationalConstructibleLocalization l E Y).obj K ⟶
            (sfRationalConstructibleLocalization l E Y).obj L))
          (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
            (constructibleIntegralPullback l E f).map a)) := by
  unfold rationalDerivedPullback
  exact (rationalDerivedPullback_existsUnique l E f).exists.choose_spec

private theorem genericTensorComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (μ : constructibleIntegralTensor l E X ⋙ constructibleIntegralPullback l E q ≅
      (constructibleIntegralPullback l E q).prod (constructibleIntegralPullback l E q) ⋙
        constructibleIntegralTensor l E Y) :
    ∃! e : rationalDerivedTensor l E X ⋙ rationalDerivedPullback l E q ≅
      (rationalDerivedPullback l E q).prod (rationalDerivedPullback l E q) ⋙
        rationalDerivedTensor l E Y,
      ∀ M N : sfRationalConstructibleCategory l E X,
        HEq (e.hom.app (M, N)) ((sfRationalConstructibleLocalization l E Y).map
          (μ.hom.app (M.obj, N.obj))) := by
  let F := rationalDerivedPullback l E q
  let T := rationalDerivedTensor l E X
  let U := rationalDerivedTensor l E Y
  have hs := rationalDerivedPullbackSpec l
    E q
  have ht := rationalTensor_spec l
    E X
  have hu := rationalTensor_spec l
    E Y
  have : F.Additive := by
    simpa only [F] using hs.1
  let R := Padic.coefficientExtensionIntegers l
    E
  let t := Padic.coefficientExtensionUniformizer l
    E
  apply rawBifunctorIso
    (C := sfIntegralConstructibleCategory l
      E X)
    (D := sfIntegralConstructibleCategory l
      E Y) t
    (constructibleIntegralTensor l E X ⋙ constructibleIntegralPullback l E q)
    ((constructibleIntegralPullback l E q).prod (constructibleIntegralPullback l E q) ⋙
      constructibleIntegralTensor l E Y) (μ) (T ⋙ F) (F.prod F ⋙ U)
  · intro M N
    change F.obj (T.obj (M, N)) = _
    have hT := ht.1 (M, N)
    change T.obj (M, N) = _ at hT
    have hF := hs.2.1
      (ScalarLocalization.mk ((constructibleIntegralTensor l E X).obj (M.obj, N.obj)))
    exact (congrArg F.obj hT).trans hF
  · intro M N
    change U.obj (F.obj M, F.obj N) = _
    have hu' := hu.1 (F.obj M, F.obj N)
    have hm := hs.2.1 M
    have hn := hs.2.1 N
    change U.obj (F.obj M, F.obj N) = _ at hu'
    change F.obj M = _ at hm
    change F.obj N = _ at hn
    exact hu'.trans (congrArg
      (fun MN ↦ ScalarLocalization.mk ((constructibleIntegralTensor l E Y).obj MN))
      (congrArg₂ Prod.mk (congrArg ScalarLocalization.obj hm)
        (congrArg ScalarLocalization.obj hn)))
  · intro M M' N N'
    obtain ⟨b, hb, hbt⟩ := ht.2 M M' N N'
    let c : (M ⟶ M') →+ (N ⟶ N') →+
        ((T ⋙ F).obj (M, N) ⟶ (T ⋙ F).obj (M', N')) :=
      { toFun := fun f ↦
          { toFun := fun g ↦ F.map (b f g)
            map_zero' := by simp
            map_add' := by intros; simp }
        map_zero' := by ext g; simp
        map_add' := by intros; ext g; simp }
    refine ⟨c, ?_, ?_⟩
    · intro f g
      exact congrArg F.map (hb f g)
    · intro f g a d
      exact (map_heq F (ht.1 (M, N)) (ht.1 (M', N')) (hbt f g a d)).trans
        (hs.2.2 _ _ _ (a * d))
  · intro M M' N N'
    obtain ⟨b, hb, hbt⟩ := hu.2 (F.obj M) (F.obj M') (F.obj N) (F.obj N')
    let c : (M ⟶ M') →+ (N ⟶ N') →+
        ((F.prod F ⋙ U).obj (M, N) ⟶ (F.prod F ⋙ U).obj (M', N')) :=
      { toFun := fun f ↦
          { toFun := fun g ↦ b (F.map f) (F.map g)
            map_zero' := by simp
            map_add' := by intros; simp }
        map_zero' := by ext g; simp
        map_add' := by intros; ext g; simp }
    refine ⟨c, ?_, ?_⟩
    · intro f g
      exact hb (F.map f) (F.map g)
    · intro f g a d
      change HEq (b (F.map (a ⊗ₜ[R] f)) (F.map (d ⊗ₜ[R] g))) _
      rw [← hb]
      have h := map_heq U
        (congrArg₂ Prod.mk (hs.2.1 M) (hs.2.1 N))
        (congrArg₂ Prod.mk (hs.2.1 M') (hs.2.1 N'))
        (prod_heq (hs.2.1 M) (hs.2.1 M') (hs.2.1 N) (hs.2.1 N')
          (hs.2.2 _ _ f a) (hs.2.2 _ _ g d))
      obtain ⟨b', hb', hbt'⟩ := hu.2
        (ScalarLocalization.mk ((constructibleIntegralPullback l E q).obj M.obj))
        (ScalarLocalization.mk ((constructibleIntegralPullback l E q).obj M'.obj))
        (ScalarLocalization.mk ((constructibleIntegralPullback l E q).obj N.obj))
        (ScalarLocalization.mk ((constructibleIntegralPullback l E q).obj N'.obj))
      exact h.trans ((heq_of_eq (hb' _ _)).trans
        (hbt' ((constructibleIntegralPullback l E q).map f)
          ((constructibleIntegralPullback l E q).map g) a d))


private theorem genericHomCoordinates (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K M : sfIntegralConstructibleCategory l E X) (f : K ⟶ M) (a : E) :
    HEq ((rationalDerivedPullback l E q).map
      ((sfRationalHomCoordinates l E X
        ((sfRationalConstructibleLocalization l E X).obj K)
        ((sfRationalConstructibleLocalization l E X).obj M)).symm (f ⊗ₜ a)))
      ((sfRationalHomCoordinates l E Y
        ((sfRationalConstructibleLocalization l E Y).obj
          ((constructibleIntegralPullback l E q).obj K))
        ((sfRationalConstructibleLocalization l E Y).obj
          ((constructibleIntegralPullback l E q).obj M))).symm
        ((constructibleIntegralPullback l E q).map f ⊗ₜ a)) := by
  let c := (sfRationalCoefficientEquiv l E).symm a
  have coord (W : Scheme.{u}) (A B : sfIntegralConstructibleCategory l E W)
      (g : A ⟶ B) :
      (sfRationalHomCoordinates l E W ⟨A⟩ ⟨B⟩).symm (g ⊗ₜ a) = c ⊗ₜ g := by
    apply (sfRationalHomCoordinates l E W ⟨A⟩ ⟨B⟩).injective
    rw [AddEquiv.apply_symm_apply]
    have hc := (sfRationalHomCoordinates_existsUnique l E W ⟨A⟩ ⟨B⟩).exists.choose_spec c g
    exact (hc.trans (congrArg (fun z ↦ g ⊗ₜ z)
      ((sfRationalCoefficientEquiv l E).apply_symm_apply a))).symm
  change HEq ((rationalDerivedPullback l E q).map
    ((sfRationalHomCoordinates l E X ⟨K⟩ ⟨M⟩).symm (f ⊗ₜ a)))
    ((sfRationalHomCoordinates l E Y
      ⟨(constructibleIntegralPullback l E q).obj K⟩
      ⟨(constructibleIntegralPullback l E q).obj M⟩).symm
      ((constructibleIntegralPullback l E q).map f ⊗ₜ a))
  rw [coord X K M f, coord Y _ _ ((constructibleIntegralPullback l E q).map f)]
  exact (rationalDerivedPullbackSpec l E q).2.2 K M f c


end Generic

include hft hqc hopen hclosed hdisjoint hcover H in
/-- Restriction descends through raw rationalization and the actual common-stage pairs.
No idempotent completion occurs; the finite-Tor field categories are the same categories.
Source: blueprint final invertibility assertion, transport steps 10--11
(blueprint: lem-pur-finite-product-field-coefficient-descent).
Proof: (1) extend each integral restriction linearly on tensor Homs, using its O_E
linearity for balancing and its functor laws for identities and composition.
(2) The integral Hom bijection tensored with E, followed by TensorProduct.piLeft,
is the rational Hom map, so it is bijective, including the empty product.
(3) Objects have not changed; integral essential surjectivity proves rational essential
surjectivity. Apply the fully-faithful/essentially-surjective equivalence criterion.
(4) Rationalize the normalized integral scalar, tensor and unit comparisons.
(5) Common-stage pullback conjugates representatives by precisely these comparisons;
tower coherence respects eventual equality and cancels intermediate comparisons.
(6) Finitely many coefficient fields have a finite common compositum, with Q_l for
an empty family. (7) Extend all component objects there and glue by rational essential
surjectivity. (8) Extend a finite tuple of arrows there and lift by rational fullness.
(9) Extend finitely many equality witnesses to one field and apply rational faithfulness;
no injectivity of transition Hom maps is used. (10) The same common-field argument
checks tensor and unit equations and composition. (11) Empty products are terminal
categories; the integral equivalence makes their Homs zero, as are their rational
localizations and common-stage colimits. Field finite-Tor categories are aliases. -/
theorem restriction_equivalences :
    (∀ E : Index P.coefficients.l P.coefficients.Qbar,
      (Functor.pi' (A := rationalCategory P E X)
        (C := fun i : I ↦ rationalCategory P E (Xi i))
        (fun i : I ↦ rationalRestriction P E (j i))).IsEquivalence) ∧
    (Functor.pi'
      (A := commonCategory P X)
      (C := fun i : I ↦ commonCategory P (Xi i))
      (fun i : I ↦ commonRestriction P (j i))).IsEquivalence := by
  sorry


section HomCoordinates
set_option allowUnsafeReducibility true in
attribute [local reducible] rationalCategory rationalCategoryStructure rationalPreadditive
  integralCategory integralCategoryStructure integralPreadditive integralLinear localization

include hft hqc hopen hclosed hdisjoint hcover H in
/-- Rational restriction's pure-tensor formula in Hom-first E coordinates.
Its finite-product Hom isomorphism is the existing TensorProduct.piLeft.
Source: blueprint rationalization transport, steps 1--3
(blueprint: lem-pur-finite-product-field-coefficient-descent).
Proof: the integral equivalence identifies the global Hom module with the product
of the component Hom modules. Its inverse is linear by injectivity of the forward
linear map. Tensor both inverse maps with E. TensorProduct.piLeft then gives the
canonical linear equivalence TensorProduct.piLeft. The definition
of rationalDerivedPullback is the linear extension of the same integral map;
its uniqueness characterization and sfRationalHomCoordinates give the second formula.
Thus its Hom map is precisely this isomorphism. The empty product is the zero module. -/
theorem hom_tensor_formula (E : Index P.coefficients.l P.coefficients.Qbar)
    (K M : integralCategory P E X) :
    (∀ (f : K ⟶ M) (a : Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) (i : I),
      HEq ((rationalRestriction P E (j i)).map
        ((sfRationalHomCoordinates P.coefficients.l
          (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) X.left
          ((localization P E X).obj K) ((localization P E X).obj M)).symm (f ⊗ₜ a)))
        ((sfRationalHomCoordinates P.coefficients.l
          (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) (Xi i).left
          ((localization P E (Xi i)).obj ((integralRestriction P E (j i)).obj K))
          ((localization P E (Xi i)).obj ((integralRestriction P E (j i)).obj M))).symm
          ((integralRestriction P E (j i)).map f ⊗ₜ a))) := by
  intro f a i
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact genericHomCoordinates P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) (j i).left K M f a

end HomCoordinates
include hft hqc hopen hclosed hdisjoint hcover H in
/-- Every component tuple glues at one finite coefficient field, containing every
field of definition in the tuple. The empty tuple uses the base coefficient field.
Source: blueprint common-stage transport, steps 6--7
(blueprint: lem-pur-finite-product-field-coefficient-descent).
Proof: iteratively take the finite compositum of all fields in the finite family;
start at Q_l, so this includes the empty family. Extend all objects to this field.
Rational essential surjectivity gives K and the displayed component isomorphisms.
The common-stage isomorphisms are represented by those same isomorphisms and their
inverses, using the canonical scalar identity comparisons. -/
theorem objects_at_common_field
    (B : ∀ i, commonCategory P (Xi i)) :
    ∃ (L : Index P.coefficients.l P.coefficients.Qbar)
      (hB : ∀ i, (B i).stage ≤ L) (K : rationalCategory P L X),
      ∀ i, Nonempty ((rationalRestriction P L (j i)).obj K ≅ (B i).toStage (hB i)) := by
  obtain ⟨L, hB⟩ := Finite.exists_le (fun i ↦ (B i).stage)
  let F := Functor.pi' (A := rationalCategory P L X)
    (C := fun i : I ↦ rationalCategory P L (Xi i))
    (fun i : I ↦ rationalRestriction P L (j i))
  have : F.IsEquivalence :=
    (restriction_equivalences P X Xi j hdisjoint hcover H).1 L
  obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage F (fun i ↦ (B i).toStage (hB i))
  exact ⟨L, hB, K, fun i ↦ ⟨(Pi.eval _ i).mapIso e⟩⟩

include hft hqc hopen hclosed hdisjoint hcover H in
/-- A finite tuple of component arrows has one global representative over one common
finite field. Each component of this representative is given by the existing normalized
commonStageDerivedPullback formula, so the same L represents them simultaneously.
Source: blueprint common-stage transport, steps 5--8
(blueprint: lem-pur-finite-product-field-coefficient-descent).
Proof: represent each component arrow and collect its representative field together
with the endpoint fields. A finite compositum contains them all. Extend each arrow
there and conjugate by the canonical scalar/restriction comparisons to get a tuple
of rational restriction arrows. Rational fullness gives a single global u. Its
common-stage class has exactly the prescribed images by the normalized representative
formula. For arrows between arbitrary component tuples, conjugate by the object
preimage isomorphisms from objects_at_common_field and use this same construction. -/
theorem arrows_at_common_field
    (A B : commonCategory P X)
    (v : ∀ i, (commonRestriction P (j i)).obj A ⟶ (commonRestriction P (j i)).obj B) :
    ∃ (L : Index P.coefficients.l P.coefficients.Qbar) (hA : A.stage ≤ L)
      (hB : B.stage ≤ L) (u : StageHom A B ⟨L, hA, hB⟩),
      ∀ i, (commonRestriction P (j i)).map
        (GeneralAlgebraicallyClosedCoefficients.ofHom A B L hA hB u) = v i := by
  let F := Functor.pi' (A := commonCategory P X)
    (C := fun i : I ↦ commonCategory P (Xi i))
    (fun i : I ↦ commonRestriction P (j i))
  have : F.IsEquivalence :=
    (restriction_equivalences P X Xi j hdisjoint hcover H).2
  obtain ⟨a, ha⟩ := F.map_surjective (X := A) (Y := B) v
  obtain ⟨L, hA, hB, u, rfl⟩ := (representatives A B).1 a
  exact ⟨L, hA, hB, u, fun i ↦ congrFun ha i⟩

include hft hqc hopen hclosed hdisjoint hcover H in
/-- Component equality is exactly equality of the global representatives after a single
further finite coefficient extension. No injectivity of Hom transitions is assumed.
Source: blueprint common-stage transport, step 9
(blueprint: lem-pur-finite-product-field-coefficient-descent).
Proof: each component equality is witnessed at some finite overfield by the actual
pair-category representative criterion. Enlarge their finite family, and the two input
fields, to a single compositum. Canonical comparison naturality identifies the component
restrictions of the transported global arrows. Rational faithfulness at that field gives
global equality. Conversely global equality there gives component equality by functoriality.
For I empty there are no component witnesses to collect: choose a common upper field
of the two input fields and use the empty-product rational Hom bijection there. -/
theorem component_equality_iff_eventual
    (A B : commonCategory P X)
    (L M : Common A B) (f : StageHom A B L) (g : StageHom A B M) :
    (∀ i, (commonRestriction P (j i)).map
        (GeneralAlgebraicallyClosedCoefficients.ofHom A B L.val L.property.1 L.property.2 f) =
      (commonRestriction P (j i)).map
        (GeneralAlgebraicallyClosedCoefficients.ofHom A B M.val M.property.1 M.property.2 g)) ↔
      ∃ (N : Common A B) (hL : L ≤ N) (hM : M ≤ N),
        transport A B L N hL f = transport A B M N hM g := by
  let F := Functor.pi' (A := commonCategory P X)
    (C := fun i : I ↦ commonCategory P (Xi i))
    (fun i : I ↦ commonRestriction P (j i))
  have : F.IsEquivalence :=
    (restriction_equivalences P X Xi j hdisjoint hcover H).2
  rw [← (representatives A B).2 L M f g]
  constructor
  · intro h
    exact F.map_injective (funext h)
  · intro h i
    exact congrArg (commonRestriction P (j i)).map h



include hft hqc hopen hclosed hdisjoint hcover H in
/-- Rational restriction's tensor comparison is the rationalization of the assumed
integral tensor comparison, component by component.
Source: blueprint transport, step 4
(blueprint: lem-pur-finite-product-field-coefficient-descent).
Proof: localize the integral comparison and its inverse. The defining object formulas
of rational pullback and tensor identify its endpoints with the displayed functors.
Naturality on two pure arrows is integral naturality multiplied by the product of
the two scalars. Extend separately by additivity to all arrows. The component formula
fixes the natural isomorphism uniquely, and no new objects or summands are adjoined. -/
theorem rational_tensor_existsUnique
    (E : Index P.coefficients.l P.coefficients.Qbar) (i : I) :
    ∃! μ : rationalTensor P E X ⋙ rationalRestriction P E (j i) ≅
      ((rationalRestriction P E (j i)).prod (rationalRestriction P E (j i))) ⋙
        rationalTensor P E (Xi i),
      ∀ M N : rationalCategory P E X,
        HEq (μ.hom.app (M, N))
          ((localization P E (Xi i)).map ((H.tensor E i).hom.app (M.obj, N.obj))) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact genericTensorComparison P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) (j i).left (H.tensor E i)

/-- The tensor comparison fixed by integral localization, not an arbitrary isomorphism.
Source: blueprint transport, step 4
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def rationalTensorComparison (E : Index P.coefficients.l P.coefficients.Qbar) (i : I) :
    rationalTensor P E X ⋙ rationalRestriction P E (j i) ≅
      ((rationalRestriction P E (j i)).prod (rationalRestriction P E (j i))) ⋙
        rationalTensor P E (Xi i) :=
  (rational_tensor_existsUnique P X Xi j hdisjoint hcover H E i).exists.choose



section ScalarUnitProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] sfRationalScalarExtension
private theorem genericScalarUnit (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (Y : Scheme.{u})
    (A : sfIntegralConstructibleCategory l E Y)
    (B : sfIntegralConstructibleCategory l L Y)
    (ν : (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj A ≅ B) :
    ∃! e : (sfRationalScalarExtension l E Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
      ((sfRationalConstructibleLocalization l E Y).obj A) ≅
        (sfRationalConstructibleLocalization l L Y).obj B,
      HEq e.hom ((sfRationalConstructibleLocalization l L Y).map ν.hom) := by
  let Q := sfRationalConstructibleLocalization l L Y
  have ho := (sfRationalScalarExtension_existsUnique l E Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1
      ((sfRationalConstructibleLocalization l E Y).obj A)
  unfold sfRationalScalarExtension
  let e := eqToIso ho ≪≫ Q.mapIso ν
  have he : HEq e.hom (Q.map ν.hom) := eqToHom_comp_heq (Q.map ν.hom) ho
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  exact eq_of_heq (he'.trans he.symm)



set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem genericUnitComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : sfIntegralConstructibleCategory l E X)
    (B : sfIntegralConstructibleCategory l E Y)
    (ε : (constructibleIntegralPullback l E q).obj A ≅ B) :
    ∃! e : (rationalDerivedPullback l E q).obj
      ((sfRationalConstructibleLocalization l E X).obj A) ≅
        (sfRationalConstructibleLocalization l E Y).obj B,
      HEq e.hom ((sfRationalConstructibleLocalization l E Y).map ε.hom) := by
  let Q := sfRationalConstructibleLocalization l E Y
  have ho : (rationalDerivedPullback l E q).obj
      ((sfRationalConstructibleLocalization l E X).obj A) =
      ScalarLocalization.mk ((constructibleIntegralPullback l E q).obj A) := by
    unfold rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l E q).exists.choose_spec.2.1
      ((sfRationalConstructibleLocalization l E X).obj A)
  let e := eqToIso ho ≪≫ Q.mapIso ε
  have he : HEq e.hom (Q.map ε.hom) := eqToHom_comp_heq (Q.map ε.hom) ho
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  exact eq_of_heq (he'.trans he.symm)

end ScalarUnitProof

include hft hqc hopen hclosed hdisjoint hcover H in
/-- The unit restriction comparison is exactly the rationalized integral unit comparison.
Source: blueprint transport, step 4
(blueprint: lem-pur-finite-product-field-coefficient-descent).
Proof: apply raw localization to the assumed integral unit isomorphism and its inverse.
The rational pullback object formula identifies the source with the localization of
the integral restriction. The prescribed hom determines the isomorphism uniquely. -/
theorem rational_unit_existsUnique
    (E : Index P.coefficients.l P.coefficients.Qbar) (i : I) :
    ∃! e : (rationalRestriction P E (j i)).obj
      ((localization P E X).obj (integralUnit P E X)) ≅
        (localization P E (Xi i)).obj (integralUnit P E (Xi i)),
      HEq e.hom ((localization P E (Xi i)).map (H.unit E i).hom) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact genericUnitComparison P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E) (j i).left
    (integralUnit P E X) (integralUnit P E (Xi i)) (H.unit E i)


/-- The rational unit restriction comparison, fixed by its integral representative.
Source: blueprint transport, step 4
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def rationalUnitComparison (E : Index P.coefficients.l P.coefficients.Qbar) (i : I) :
    (rationalRestriction P E (j i)).obj ((localization P E X).obj (integralUnit P E X)) ≅
      (localization P E (Xi i)).obj (integralUnit P E (Xi i)) :=
  (rational_unit_existsUnique P X Xi j hdisjoint hcover H E i).exists.choose

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The canonical rational scalar transition on the recorded coefficient stage system.
Source: blueprint coefficient extensions
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def rationalScalar (E L : Index P.coefficients.l P.coefficients.Qbar) (h : E ≤ L)
    (Y : Over (Spec (CommRingCat.of P.field.k))) :
    rationalCategory P E Y ⥤ rationalCategory P L Y :=
  GeneralAlgebraicallyClosedCoefficients.transition
    P.coefficients.l P.coefficients.Qbar Y.left E L h

/-- The normalized rational pullback/scalar comparison already specified by the operations.
Source: blueprint coefficient extensions
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def rationalPullbackScalar (E L : Index P.coefficients.l P.coefficients.Qbar) (h : E ≤ L)
    {Y Z : Over (Spec (CommRingCat.of P.field.k))} (f : Y ⟶ Z) :
    rationalRestriction P E f ⋙ rationalScalar P E L h Y ≅
      rationalScalar P E L h Z ⋙ rationalRestriction P L f :=
  rationalPullbackScalarComparison P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E)
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar L)
    (coefficientInclusion P.coefficients.l P.coefficients.Qbar E L h) f.left

/-- The normalized rational tensor/scalar comparison already specified by the operations.
Source: blueprint coefficient extensions
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def rationalTensorScalar (E L : Index P.coefficients.l P.coefficients.Qbar) (h : E ≤ L)
    (Y : Over (Spec (CommRingCat.of P.field.k))) :
    rationalTensor P E Y ⋙ rationalScalar P E L h Y ≅
      (rationalScalar P E L h Y).prod (rationalScalar P E L h Y) ⋙ rationalTensor P L Y :=
  rationalTensorScalarComparison P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E)
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar L)
    (coefficientInclusion P.coefficients.l P.coefficients.Qbar E L h) Y.left

include hft hqc hopen hclosed hdisjoint hcover H in
/-- Tensor preservation commutes with every coefficient extension, including identities.
The scalar comparison is the published canonical one; its naturality and tower
identities are retained in the common-stage restriction construction.
Source: blueprint transport, step 4
(blueprint: lem-pur-finite-product-field-coefficient-descent).
Proof: rationalize H.tensor_scalar. Each of its factors is the localization of the
corresponding integral factor by the normalized comparison characterizations.
Functoriality of localization preserves the equality of composites, giving this square.
The same argument applied to the canonical integral identity and tower equations
retains their coherence. -/
theorem rational_tensor_scalar_compatible
    (E L : Index P.coefficients.l P.coefficients.Qbar) (h : E ≤ L)
    (i : I) (M N : rationalCategory P E X) :
    (rationalScalar P E L h (Xi i)).map
        ((rationalTensorComparison P X Xi j hdisjoint hcover H E i).hom.app (M, N)) ≫
      (rationalTensorScalar P E L h (Xi i)).hom.app
        ((rationalRestriction P E (j i)).obj M, (rationalRestriction P E (j i)).obj N) ≫
      (rationalTensor P L (Xi i)).map
        (Prod.mkHom ((rationalPullbackScalar P E L h (j i)).hom.app M)
          ((rationalPullbackScalar P E L h (j i)).hom.app N)) =
    (rationalPullbackScalar P E L h (j i)).hom.app ((rationalTensor P E X).obj (M, N)) ≫
      (rationalRestriction P L (j i)).map
        ((rationalTensorScalar P E L h X).hom.app (M, N)) ≫
      (rationalTensorComparison P X Xi j hdisjoint hcover H L i).hom.app
        ((rationalScalar P E L h X).obj M, (rationalScalar P E L h X).obj N) := by
  sorry

/-- Rationalization of a coefficient-unit scalar comparison, fixed on its integral map.
Source: blueprint transport, step 4
(blueprint: lem-pur-finite-product-field-coefficient-descent).
Proof: localize the given integral unit comparison and its inverse. The normalized
scalar-extension object formula identifies their endpoints. The prescribed hom fixes
the isomorphism uniquely, including identity coefficient extensions. -/
theorem rational_scalar_unit_existsUnique
    (E L : Index P.coefficients.l P.coefficients.Qbar) (h : E ≤ L)
    (Y : Over (Spec (CommRingCat.of P.field.k)))
    (ν : (integralScalar P E L h Y).obj (integralUnit P E Y) ≅ integralUnit P L Y) :
    ∃! e : (rationalScalar P E L h Y).obj
      ((localization P E Y).obj (integralUnit P E Y)) ≅
        (localization P L Y).obj (integralUnit P L Y),
      HEq e.hom ((localization P L Y).map ν.hom) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact genericScalarUnit P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar E)
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar L)
    (coefficientInclusion P.coefficients.l P.coefficients.Qbar E L h) Y.left
    (integralUnit P E Y) (integralUnit P L Y) ν


/-- The prescribed scalar-unit comparison after raw localization.
Source: blueprint transport, step 4
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def rationalScalarUnit (E L : Index P.coefficients.l P.coefficients.Qbar) (h : E ≤ L)
    (Y : Over (Spec (CommRingCat.of P.field.k)))
    (ν : (integralScalar P E L h Y).obj (integralUnit P E Y) ≅ integralUnit P L Y) :=
  (rational_scalar_unit_existsUnique P E L h Y ν).exists.choose

include hft hqc hopen hclosed hdisjoint hcover H in
/-- Unit preservation commutes with each coefficient extension under the canonical
pullback/scalar comparison and the rationalized integral unit comparisons.
Source: blueprint transport, step 4
(blueprint: lem-pur-finite-product-field-coefficient-descent).
Proof: apply localization to H.unit_scalar. The three uniquely prescribed rational
unit maps and the normalized pullback/scalar comparison are precisely its factors.
Functoriality identifies the two localized composites with the displayed paths. -/
theorem rational_unit_scalar_compatible
    (E L : Index P.coefficients.l P.coefficients.Qbar) (h : E ≤ L) (i : I) :
    (rationalScalar P E L h (Xi i)).map
        (rationalUnitComparison P X Xi j hdisjoint hcover H E i).hom ≫
      (rationalScalarUnit P E L h (Xi i) (H.componentScalarUnit E L h i)).hom =
    (rationalPullbackScalar P E L h (j i)).hom.app
        ((localization P E X).obj (integralUnit P E X)) ≫
      (rationalRestriction P L (j i)).map
        (rationalScalarUnit P E L h X (H.sourceScalarUnit E L h)).hom ≫
      (rationalUnitComparison P X Xi j hdisjoint hcover H L i).hom := by
  sorry

/-- The recorded common-stage tensor, formed at the coefficient compositum.
Source: blueprint common-stage coefficient operations
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def commonTensor (Y : Over (Spec (CommRingCat.of P.field.k))) :
    commonCategory P Y × commonCategory P Y ⥤ commonCategory P Y :=
  commonStageDerivedTensor P.coefficients.l P.coefficients.Qbar Y.left

/-- The coefficient unit as the actual pair at the specified finite stage.
Source: blueprint common-stage coefficient unit
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def commonUnit (E : Index P.coefficients.l P.coefficients.Qbar)
    (Y : Over (Spec (CommRingCat.of P.field.k))) :
    commonCategory P Y :=
  ⟨E, (localization P E Y).obj (integralUnit P E Y)⟩

/-- The normalized common-stage tensor restriction source.
Source: blueprint transport, step 10
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
abbrev tensorSource (i : I)
    (M N : commonCategory P X) :=
  commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left
    (commonStageTensorObject P.coefficients.l P.coefficients.Qbar X.left M N)

/-- The normalized common-stage tensor restriction target, at the same compositum.
Source: blueprint transport, step 10
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
abbrev tensorTarget (i : I)
    (M N : commonCategory P X) :=
  commonStageTensorObject P.coefficients.l P.coefficients.Qbar (Xi i).left
    (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left M)
    (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left N)

/-- The actual comparison arrow at a common finite field: identify restriction and
tensor at that field, apply the rational comparison, and undo the target identifications.
Every comparison here is the published normalized scalar comparison.
Source: blueprint common-stage tensor formula, step 10
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def tensorRepresentative (i : I)
    (M N : commonCategory P X)
    (L : Index P.coefficients.l P.coefficients.Qbar)
    (h : Padic.finiteCoefficientCompositum
      P.coefficients.l P.coefficients.Qbar M.stage N.stage ≤ L) :
    ((tensorSource P X Xi j i M N).toStage h ⟶
      (tensorTarget P X Xi j i M N).toStage h) :=
  (commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar (j i).left
    (commonStageTensorObject P.coefficients.l P.coefficients.Qbar X.left M N) L h).hom ≫
  (rationalRestriction P L (j i)).map
    (commonStageTensorComparison P.coefficients.l P.coefficients.Qbar X.left M N L h).hom ≫
  (rationalTensorComparison P X Xi j hdisjoint hcover H L i).hom.app
    (M.toStage (((Padic.finiteCoefficientFields_properties
      P.coefficients.l P.coefficients.Qbar).1 M.stage N.stage).1.trans h),
      N.toStage (((Padic.finiteCoefficientFields_properties
        P.coefficients.l P.coefficients.Qbar).1 M.stage N.stage).2.trans h)) ≫
  (rationalTensor P L (Xi i)).map
    (Prod.mkHom
      (commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar (j i).left M L
        (((Padic.finiteCoefficientFields_properties
          P.coefficients.l P.coefficients.Qbar).1 M.stage N.stage).1.trans h)).inv
      (commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar (j i).left N L
        (((Padic.finiteCoefficientFields_properties
          P.coefficients.l P.coefficients.Qbar).1 M.stage N.stage).2.trans h)).inv) ≫
  (commonStageTensorComparison P.coefficients.l P.coefficients.Qbar (Xi i).left
    (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left M)
    (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left N) L h).inv

include hft hqc hopen hclosed hdisjoint hcover H in
/-- Common-stage tensor preservation has the canonical representative at every common
finite coefficient field. This states independence of representatives and enlargement,
and compatibility with the finite-stage scalar comparisons, in addition to naturality.
Source: blueprint common-stage transport, steps 5 and 10
(blueprint: lem-pur-finite-product-field-coefficient-descent).
Proof: at the compositum use the rational tensor comparison between the normalized
source and target. At any larger field its scalar extension is tensorRepresentative:
this is rational_tensor_scalar_compatible, conjugated by the canonical tensor and
pullback scalar comparisons. Their tower equations give equality after any further
extension. Hence these arrows define a common-stage comparison independent of all
representatives. Rational inverses give its inverse. Put two input arrows at one common
field; rational naturality there proves naturality of their classes. Every object and
arrow has such a representative, so the displayed formula also proves uniqueness.
Identities and composition use the existing common-stage functor laws, whose middle
comparisons cancel. Every structural equation is checked at a common finite field. -/
theorem common_tensor_existsUnique (i : I) :
    ∃! μ : commonTensor P X ⋙ commonRestriction P (j i) ≅
      ((commonRestriction P (j i)).prod (commonRestriction P (j i))) ⋙ commonTensor P (Xi i),
      ∀ (M N : commonCategory P X)
        (L : Index P.coefficients.l P.coefficients.Qbar)
        (h : Padic.finiteCoefficientCompositum
          P.coefficients.l P.coefficients.Qbar M.stage N.stage ≤ L),
        HEq (μ.hom.app (M, N))
          (GeneralAlgebraicallyClosedCoefficients.ofHom
            (tensorSource P X Xi j i M N) (tensorTarget P X Xi j i M N) L h h
            (tensorRepresentative P X Xi j hdisjoint hcover H i M N L h)) := by
  sorry

include hft hqc hopen hclosed hdisjoint hcover H in
/-- The common-stage coefficient unit comparison is represented at its chosen finite
field by the rationalized integral unit comparison, with the specified identity-extension
unitors. Unit comparisons at enlarged stages satisfy rational_unit_scalar_compatible.
Source: blueprint common-stage transport, steps 4, 5 and 10--11
(blueprint: lem-pur-finite-product-field-coefficient-descent).
Proof: represent the rational unit comparison at E, conjugating by the normalized
identity scalar-extension unitors. The common-stage pullback object formula identifies
its source with the normalized restricted unit. Rational inverses give an inverse
common-stage class. The finite-stage scalar/unit square makes its extension to every
larger field the same class, independently of representatives. The representative
formula fixes its hom, hence the isomorphism uniquely. The construction uses the actual
regular module and its raw localization; it never adjoins an idempotent summand. -/
theorem common_unit_existsUnique
    (E : Index P.coefficients.l P.coefficients.Qbar) (i : I) :
    ∃! e : (commonRestriction P (j i)).obj (commonUnit P E X) ≅ commonUnit P E (Xi i),
      HEq e.hom
        (GeneralAlgebraicallyClosedCoefficients.ofHom
          (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar (j i).left
            (commonUnit P E X))
          (commonUnit P E (Xi i)) E le_rfl le_rfl
          (((operationStageTransitionIso P.coefficients.l P.coefficients.Qbar
              (Xi i).left E E le_rfl) ≪≫
            GeneralAlgebraicallyClosedCoefficients.unitor
              P.coefficients.l P.coefficients.Qbar (Xi i).left E).hom.app
              ((rationalRestriction P E (j i)).obj
                ((localization P E X).obj (integralUnit P E X))) ≫
            (rationalUnitComparison P X Xi j hdisjoint hcover H E i).hom ≫
            ((operationStageTransitionIso P.coefficients.l P.coefficients.Qbar
              (Xi i).left E E le_rfl) ≪≫
            GeneralAlgebraicallyClosedCoefficients.unitor
              P.coefficients.l P.coefficients.Qbar (Xi i).left E).inv.app
              ((localization P E (Xi i)).obj (integralUnit P E (Xi i))))) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  let A' := commonStagePullbackObject P.coefficients.l P.coefficients.Qbar
    (j i).left (commonUnit P E X)
  let B' := commonUnit P E (Xi i)
  let S := stageSystem P.coefficients.l P.coefficients.Qbar (Xi i).left
  let c := operationStageTransitionIso P.coefficients.l P.coefficients.Qbar
    (Xi i).left E E le_rfl ≪≫ unitor P.coefficients.l P.coefficients.Qbar (Xi i).left E
  let d : A'.toStage le_rfl ≅ B'.toStage le_rfl :=
    c.app ((rationalRestriction P E (j i)).obj
      ((localization P E X).obj (integralUnit P E X))) ≪≫
      rationalUnitComparison P X Xi j hdisjoint hcover H E i ≪≫
      (c.app ((localization P E (Xi i)).obj (integralUnit P E (Xi i)))).symm
  let e₀ : A' ≅ B' := S.isoToStage A' le_rfl ≪≫ (S.ι E).mapIso d ≪≫
    (S.isoToStage B' le_rfl).symm
  have hd : e₀.hom = ofHom A' B' E le_rfl le_rfl d.hom :=
    (StageSystem.mkHom_eq_isoToStage (S := S) (X := A') (Y := B')
      (n := E) le_rfl le_rfl d.hom).symm
  have ho : (commonRestriction P (j i)).obj (commonUnit P E X) = A' := by
    unfold commonRestriction commonStageDerivedPullback
    exact (commonStageDerivedPullback_existsUnique P.coefficients.l
      P.coefficients.Qbar (j i).left).exists.choose_spec.1 (commonUnit P E X)
  let e := eqToIso ho ≪≫ e₀
  have he : HEq e.hom (ofHom A' B' E le_rfl le_rfl d.hom) :=
    (eqToHom_comp_heq e₀.hom ho).trans (heq_of_eq hd)
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  exact eq_of_heq (he'.trans he.symm)


end FiniteProductFieldDescent
end WeilConjectures
