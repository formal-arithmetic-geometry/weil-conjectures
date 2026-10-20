/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.PurInverseImageTensorHom
public import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.Paper.SpecifiedPullbackComparisonAlpha
import Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization

/-!
# Coefficient compatibility of the specified integral inverse-image comparison

Source: Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4), pp. 50--51.
The scalar compatibility formula is the agent calculation from the specified
quotient-cone maps (blueprint: lem-weil-isomorphism-comparison-scalar-extension).
The ordinary tensor is expressed in its exact finite-free model. Its completion
comparison is identified with the specified universal derived-tensor comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The two ordinary tensor models have the same pure tensors, with their canonical
coefficient actions. Source: the quotient-cone calculation at Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension).
Proof: the two coefficient maps agree after every quotient projection, so are equal.
The sheafified balanced tensor constructions therefore have identical generators
and relations. Send each displayed generator to the other displayed generator.
This gives inverse natural maps, uniquely determined by local tensor generation. -/
theorem isomorphismScalarSheafModel_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! e : integralOrdinaryScalar l E L ι W ≅ completedOrdinaryScalarExtension l E L ι W,
      ∀ (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
        (a : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
        (x : M.val.obj U),
        (e.hom.app M).val.app U (integralOrdinaryTensorSection l E L ι W M U a x) =
          completedScalarTensorSection l E L ι W M U a x := by
  sorry

/-- The actual identity on pure tensors between the two recorded ordinary models.
Source: Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension). -/
def isomorphismScalarSheafModel (W : AlgebraicGeometry.Scheme.{u}) :=
  (isomorphismScalarSheafModel_existsUnique l E L ι W).exists.choose

/-- Identify the exact finite-free tensor model with the universal derived tensor
model, retaining its counit and the SPECIFIED completion comparison χ.
Source: the quotient-cone calculation accompanying Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension).
Proof: both completed coefficient maps have the same finite residue projections,
so they coincide. Their ordinary functors are canonically identified on sheafified
pure tensors. Finite freeness makes ordinary extension exact on every complex.
The universal left-derived counit therefore identifies its localization with
completedDerivedScalarExtension on every complex. The displayed normalization
uniquely determines that natural isomorphism by localization. On a good resolution,
both completion maps have the same quotient augmentation and zero shifted-product
coordinate. Their normalized descent proves the second equation. -/
theorem isomorphismScalarModel_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! e : integralOrdinaryDerivedScalar l E L ι W ≅
        completedDerivedScalarExtension l E L ι W,
      (∀ P : CochainComplex (integralTowerModules l E W) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E L ι W P =
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (isomorphismScalarSheafModel l E L ι W)
                (ComplexShape.up ℤ)).hom.app P)) ∧
      e.hom ≫ completedScalarComparison l E L ι W = scalarCompletion l E L ι W := by
  sorry

/-- The sectionwise tensor comparison is uniquely fixed on every local pure tensor.
Here U maps to (U,g∘u), so the underlying section y is literally y₀, and the target
scalar c_L(g⁻¹a₀) is the displayed completed coefficient map applied to a₀.
Source: inverse-image tensor comparison and Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension).
Proof: inverse-image tensor compatibility sends the transported pure tensor to the
same tensor on (U,g∘u). The coefficient projection equations make it balanced over
R_E, and c_L gives its R_L-linearity. The reverse tensor rule is its inverse.
Restrictions and module maps commute with the formula. Sheafification extends
these maps; local generation by pure tensors proves uniqueness. -/
theorem isomorphismScalarTensor_existsUnique
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃! b : inverseImageIntegralModules l E g ⋙ integralOrdinaryScalar l E L ι X ≅
        integralOrdinaryScalar l E L ι Y ⋙ inverseImageIntegralModules l L g,
      ∀ (M : integralTowerModules l E Y) (U : X.ProEt)
        (y : M.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
        (a : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        (b.hom.app M).val.app (op U)
          (integralOrdinaryTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) (op U)
            ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) a) y) =
          integralOrdinaryTensorSection l E L ι Y M
            (op ((proEtaleIsoPostcompose g).obj U)) a y := by
  sorry

/-- The actual tensor isomorphism b on sheaves, fixed by its local tensor rule.
Source: Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension). -/
def isomorphismScalarTensor {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :=
  (isomorphismScalarTensor_existsUnique l E L ι g).exists.choose

/-- Exact inverse image and finite-free extension descend this same tensor isomorphism.
Source: Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension). -/
def isomorphismScalarTensorDerived {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :
    inverseImageIntegralDerived l E g ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      integralOrdinaryDerivedScalar l E L ι Y ⋙ inverseImageIntegralDerived l L g :=
  (Functor.mapDerivedCategoryCompIso (inverseImageIntegralModules l E g)
    (integralOrdinaryScalar l E L ι X)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (isomorphismScalarTensor l E L ι g) ≪≫
    Functor.mapDerivedCategoryCompIso (integralOrdinaryScalar l E L ι Y)
      (inverseImageIntegralModules l L g)

/-- Both inputs to the X-side completion comparisons lie in the recorded bounded
constructible, derived-complete category. Source: Bhatt--Scholze 6.5.9(4), and the
isomorphism-derived-pullback assertion
(blueprint: lem-weil-isomorphism-comparison-scalar-extension).
Proof: the sectionwise inverse-image equivalence transports the coefficient actions,
finite quotient reductions, and their constructible partitions. Exactness transports
cohomology and its common finite interval. It commutes with the quotient-unit Roos
triangle, giving completeness of inverse image. The recorded completed pullback is
naturally identified with that inverse image on these objects by
lem-weil-isomorphism-derived-pullback. This identification preserves the constructible
and completeness predicates, giving the second clause. -/
theorem isomorphismComparisonInputs_constructible
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (integralTowerModules l E Y))
    (_hK : sfIntegralConstructible l E Y K) :
    sfIntegralConstructible l E X ((inverseImageIntegralDerived l E g).obj K) ∧
      sfIntegralConstructible l E X ((integralDerivedPullback l E g).obj K) := by
  sorry

/-- α is tensor associativity followed by the strict quotient completion comparisons:
the recorded `scalarPullbackCompleted` of the scalar-operation lemma, whose completeness
inputs come from hK and the constructibility theorem above.
Source: Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension). -/
def isomorphismComparisonScalarAlpha {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    (integralScalarExtension l E L ι X).obj ((integralDerivedPullback l E g).obj K) ⟶
      (integralDerivedPullback l L g).obj ((integralScalarExtension l E L ι Y).obj K) :=
  (scalarPullbackCompleted l E L ι g K hK.1
    (isomorphismComparisonInputs_constructible l E g hX hY K hK).2.1).hom

/-- β = G_L(χ_Y) ∘ b ∘ χ_X⁻¹, using the specified completion comparison.
Source: Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension). -/
def isomorphismComparisonScalarBeta {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    (integralScalarExtension l E L ι X).obj ((inverseImageIntegralDerived l E g).obj K) ⟶
      (inverseImageIntegralDerived l L g).obj ((integralScalarExtension l E L ι Y).obj K) :=
  (scalarCompletionIso l E L ι X ((inverseImageIntegralDerived l E g).obj K)
    ((isomorphismComparisonInputs_constructible l E g hX hY K hK).1.1)).inv ≫
    (isomorphismScalarTensorDerived l E L ι g).hom.app K ≫
    (inverseImageIntegralDerived l L g).map ((scalarCompletion l E L ι Y).app K)

/-- The specified integral comparison commutes with finite coefficient extension.
Source: Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4), pp. 50--51; the compatibility
itself is the agent calculation of the specified quotient-cone maps
(blueprint: lem-weil-isomorphism-comparison-scalar-extension).
Proof:
1. Exact inverse image transports completed coefficient actions through c_E,c_L.
Their finite projection equations commute with quotient transitions
(lem-weil-proetale-isomorphism-inverse-image and the comparison definition).
2. Choose a flat-term K-flat P→K (lem-pc-kflat-resolution). The inverse-image
pure-tensor rule gives b_P, strictly compatible with reductions, and therefore b_K
(lem-pur-isomorphism-inverse-image-tensor-hom).
3. The specified χ is natural and invertible on complete inputs; finite freeness
allows ordinary tensor on every complex, including Roos cones
(lem-weil-finite-free-completed-scalar-comparison).
4. Q=P⊗R_L is flat-term K-flat (lem-pur-kflat-change-of-rings). The same-index
finite pullback/scalar maps give δ_P, acting on BOTH Roos coordinates. The canonical
α is Lg_L*(χ_Y) [δ_P] χ_X⁻¹
(lem-weil-specified-pullback-comparison-alpha and the scalar-operation comparison).
5. The three invertible factors of β have precisely the displayed endpoints.
6. Normalization of the specified κ identifies it with θ⁻¹G(u), independently of
resolutions, naturally in derived maps. Apply this to χ_Y to obtain
Lg_L*(χ_Y) κ_(C_Y K) = κ_(T_Y K) G_L(χ_Y)
(lem-weil-isomorphism-derived-pullback-comparison-normalization).
7. On a local generator y⊗s, both δ_P C_X(κ_E) and κ_L b_P have m-component
(g⁻¹(p⊗1))⊗π_m(s). Balancing and the projection equation for c_L give this
identity. Both shifted augmentations are zero; δ_P preserves that zero. Hence the
ENTIRE cone maps agree, and localization gives [δ_P] C_X(κ_E)=κ_L b_K.
8. Precompose the required square with χ_(X,G_E K). Its naturality and step 4 turn
the left side into Lg_L*(χ_Y)[δ_P]C_X(κ_E). Steps 7 and 6 identify this with
κ_(T_Y K)G_L(χ_Y)b_K. Cancel χ_(X,G_E K). All equalities occur in the actual
localization; no cone representing T_Y K is assumed K-flat. -/
theorem isomorphismComparison_scalarExtension
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    (integralScalarExtension l E L ι X).map
        (inverseImagePullbackComparisonDerived l E g hX hY K) ≫
      isomorphismComparisonScalarAlpha l E L ι g hX hY K hK =
    isomorphismComparisonScalarBeta l E L ι g hX hY K hK ≫
      inverseImagePullbackComparisonDerived l L g hX hY
        ((integralScalarExtension l E L ι Y).obj K) := by
  sorry

end WeilConjectures
