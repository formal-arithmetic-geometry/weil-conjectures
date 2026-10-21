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
  sorry

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
  sorry

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
  sorry

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
  sorry


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
  sorry

/-- The tensor comparison fixed by integral localization, not an arbitrary isomorphism.
Source: blueprint transport, step 4
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def rationalTensorComparison (E : Index P.coefficients.l P.coefficients.Qbar) (i : I) :
    rationalTensor P E X ⋙ rationalRestriction P E (j i) ≅
      ((rationalRestriction P E (j i)).prod (rationalRestriction P E (j i))) ⋙
        rationalTensor P E (Xi i) :=
  (rational_tensor_existsUnique P X Xi j hdisjoint hcover H E i).exists.choose

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
  sorry

/-- The rational unit restriction comparison, fixed by its integral representative.
Source: blueprint transport, step 4
(blueprint: lem-pur-finite-product-field-coefficient-descent). -/
def rationalUnitComparison (E : Index P.coefficients.l P.coefficients.Qbar) (i : I) :
    (rationalRestriction P E (j i)).obj ((localization P E X).obj (integralUnit P E X)) ≅
      (localization P E (Xi i)).obj (integralUnit P E (Xi i)) :=
  (rational_unit_existsUnique P X Xi j hdisjoint hcover H E i).exists.choose

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
  sorry

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
  sorry

end FiniteProductFieldDescent
end WeilConjectures
