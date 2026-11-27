/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalScalarBalancedLocalization
public import WeilConjectures.AlgebraicGeometry.Rational.RationalScalarCompletionUnitSquare
public import WeilConjectures.AlgebraicGeometry.Rational.RationalPullbackCompositionCoherence
public import WeilConjectures.CategoryTheory.ProperBaseChange.LocalizationInverseImageCoherence
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Rational.RationalScalarMixedIntegralGeometric
import WeilConjectures.AlgebraicGeometry.Rational.RationalScalarMixedIntegralTower
import WeilConjectures.AlgebraicGeometry.Rational.RationalScalarMixedNormalizationAssoc
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalAdjunctionUnit
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.Rational.RationalPullbackFlatComputationCounit
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleRationalHomComparison
import WeilConjectures.AlgebraicGeometry.Rational.RationalPullComputation
import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.OrdinaryCocycle

/-! # Cancellation in the specified mixed rational realization square

Theta and D below are rationalBalancedTheta and extension along
rationalBalancedCoefficient. The completed comparison is rationalScalarStrictBeta.
The pullback alpha is the supplied, generator-normalized dependency record's alpha.
The ordinary zeta is normalized on tensor generators and derived computation counits.

## Implementation details

The geometric and coefficient coherences of zeta are checked on K-flat representatives. There
rational pullback and scalar extension are computed termwise, so `ambient_normalization`
reduces both equations to equations of ordinary module maps, which are checked on unit
generators. Every derived object is the localization of a K-flat complex.

## References

* Bhatt--Scholze, Remark 6.8.15, pp. 61--62
* Stacks 0D6D, 0A0E and 0A0G
* Stacks 0D6D, 099N
* Stacks 0G7E, 0D6D and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime]
variable (E F : Type u) [Field E] [Field F]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
variable (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- The specified strict beta, restricted and rationalized, on every unchanged raw object. -/
def rationalMixedBetaComponent (g : X ⟶ Y)
    (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
    (sXF : RationalModuleRealization l F X) (sYF : RationalModuleRealization l F Y)
    (aE : RationalRealizationPullbackComparison l E g sXE sYE)
    (aF : RationalRealizationPullbackComparison l F g sXF sYF)
    (K : PbcRationalDerivedCategory l E Y Fact.out Fact.out) :
    (pbcRationalScalarExtension l E F i X Fact.out Fact.out).obj (aE.rawPull.obj K) ≅
      aF.rawPull.obj ((pbcRationalScalarExtension l E F i Y Fact.out Fact.out).obj K) :=
  (pbcRationalScalarExtension l E F i X Fact.out Fact.out).mapIso
      (eqToIso (aE.raw_objects K.obj)) ≪≫
    (pbcRationalization X (pbcIntegralDatum l F) (pbcUniformizer l F)).mapIso
      (ObjectProperty.isoMk _
        (X := (pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj
          ((aE.integral.completedFunctor l E).obj K.obj))
        (Y := (aF.integral.completedFunctor l F).obj
          ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K.obj))
        ((rationalScalarStrictBeta l E F i g).app K.obj.obj)) ≪≫
    (eqToIso (aF.raw_objects
      ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K.obj))).symm

/-- The mixed square for the specific alpha and the specified scalar/pullback comparison.
The ordinary comparison is fixed on tensor units and on derived computation counits;
its section formula determines the balanced map, including all coefficient factors. -/
structure RationalScalarMixedUnitCancellation (g : X ⟶ Y)
    (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
    (sXF : RationalModuleRealization l F X) (sYF : RationalModuleRealization l F Y)
    (aE : RationalRealizationPullbackComparison l E g sXE sYE)
    (aF : RationalRealizationPullbackComparison l F g sXF sYF)
    where
  /-- The localized finite-quotient coefficient square. -/
  coefficient_square : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
      (rationalBalancedCoefficient l E F i Y) ≫ aF.rationalCoefficient = aE.rationalCoefficient ≫
      (rationalBalancedCoefficient l E F i X)
  /-- The ordinary scalar/pullback comparison. -/
  ordinary : pbcExtend (rationalBalancedCoefficient l E F i Y) ⋙ rationalPullModule l F g
      aF.rationalCoefficient ≅
    rationalPullModule l E g aE.rationalCoefficient ⋙ pbcExtend (rationalBalancedCoefficient l E F
      i X)
  /-- Inserting tensor units gives the same pulled-back generator on both sides.
  Scalar linearity then gives l' tensor b' tensor k ↦ l'b' tensor g⁻¹k. -/
  ordinary_units : ∀ (M : pbcModules Y (rationalCoefficientSheaf l Y E))
      (V : Y.ProEt) (m : M.val.obj (op V)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (pbcTensorSection aF.rationalCoefficient
        ((proEtaleRingModulePullback g (rationalCoefficientSheaf l Y F)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y F)) (Iso.refl _)).obj
              ((pbcExtend (rationalBalancedCoefficient l E F i Y)).obj M))
        (op ((proEtaleBaseChange g).obj V)) 1
        (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l Y F)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y F)) (Iso.refl _)
          ((pbcExtend (rationalBalancedCoefficient l E F i Y)).obj M) V
          (pbcTensorSection (rationalBalancedCoefficient l E F i Y) M (op V) 1 m))) =
    pbcTensorSection (rationalBalancedCoefficient l E F i X)
      ((rationalPullModule l E g aE.rationalCoefficient).obj M)
      (op ((proEtaleBaseChange g).obj V)) 1
      (pbcTensorSection aE.rationalCoefficient
        ((proEtaleRingModulePullback g (rationalCoefficientSheaf l Y E)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y E)) (Iso.refl _)).obj M)
        (op ((proEtaleBaseChange g).obj V)) 1
        (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l Y E)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y E)) (Iso.refl _) M V m))
  /-- Its derived comparison. -/
  zeta : rationalPullDerived l E g aE.rationalCoefficient ⋙
      pbcDerivedExtend (rationalBalancedCoefficient l E F i X) ≅
    pbcDerivedExtend (rationalBalancedCoefficient l E F i Y) ⋙
      rationalPullDerived l F g aF.rationalCoefficient
  /-- The ordinary balanced map is the computation of that derived comparison. -/
  ambient_normalization : ∀ P : CochainComplex
      (pbcModules Y (rationalCoefficientSheaf l Y E)) ℤ,
    zeta.inv.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
          (rationalPullComplexCounit l E g aE.rationalCoefficient P) ≫
        pbcComplexCounit (rationalBalancedCoefficient l E F i X)
          (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex
            (.up ℤ)).obj P) =
      (rationalPullDerived l F g aF.rationalCoefficient).map
          (pbcComplexCounit (rationalBalancedCoefficient l E F i Y) P) ≫
        rationalPullComplexCounit l F g aF.rationalCoefficient
          (((pbcExtend (rationalBalancedCoefficient l E F i Y)).mapHomologicalComplex (.up ℤ)).obj
      P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)
  /-- The raw comparison, given by `rationalScalarStrictBeta`. -/
  beta : aE.rawPull ⋙ pbcRationalScalarExtension l E F i X Fact.out Fact.out ≅
    pbcRationalScalarExtension l E F i Y Fact.out Fact.out ⋙ aF.rawPull
  /-- All components, not just their endpoint isomorphism classes, are fixed. -/
  beta_normalization : ∀ K : PbcRationalDerivedCategory l E Y Fact.out Fact.out,
    beta.app K = rationalMixedBetaComponent l E F i g sXE sYE sXF sYF aE aF K
  /-- The mixed realization square commutes on every raw rational object. -/
  compatibility : ∀ K : PbcRationalDerivedCategory l E Y Fact.out Fact.out,
    (rationalBalancedTheta l E F i X sXE sXF).hom.app (aE.rawPull.obj K) ≫
        (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
          (aE.alpha.hom.app K) ≫ zeta.hom.app (sYE.J.obj K) =
      sXF.J.map (beta.hom.app K) ≫
        aF.alpha.hom.app
          ((pbcRationalScalarExtension l E F i Y Fact.out Fact.out).obj K) ≫
        (rationalPullDerived l F g aF.rationalCoefficient).map
          ((rationalBalancedTheta l E F i Y sYE sYF).hom.app K)

variable (g : X ⟶ Y)
  (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
  (sXF : RationalModuleRealization l F X) (sYF : RationalModuleRealization l F Y)
  (aE : RationalRealizationPullbackComparison l E g sXE sYE)
  (aF : RationalRealizationPullbackComparison l F g sXF sYF)

/-- The mixed equation uses exactly the owning dependencies' theta, D, strict beta and alpha. -/
theorem rationalScalarMixedUnitCancellation :
    Nonempty (RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF) := by
  sorry

section GeometricHelpers
variable {Z : Scheme.{u}} [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]
variable (h : Z ⟶ X) (sZE : RationalModuleRealization l E Z)
  (ahE : RationalRealizationPullbackComparison l E h sZE sXE)
  (acE : RationalRealizationPullbackComparison l E (h ≫ g) sZE sYE)

/-- The ambient compositor extracted from the full normalized dependency theorem.
Its tensor-generator, inverse-image-pasting, computation-counit and strict-unit equations
fix its maps; this does not select from an unnormalized endpoint-isomorphism existence. -/
def rationalMixedGeometricCompositor :
    rationalPullDerived l E g aE.rationalCoefficient ⋙
      rationalPullDerived l E h ahE.rationalCoefficient ≅
    rationalPullDerived l E (h ≫ g) acE.rationalCoefficient := by
  have hc := rationalPullbackCompositionCoherence l E g h sYE sXE sZE aE ahE acE
  unfold HasRationalPullbackCompositionCoherence at hc
  exact hc.2.2.2.2.choose_spec.2.choose

/-- The ordinary module compositor extracted from the same normalized dependency theorem. -/
def rationalMixedModuleCompositor :
    rationalPullModule l E g aE.rationalCoefficient ⋙
      rationalPullModule l E h ahE.rationalCoefficient ≅
    rationalPullModule l E (h ≫ g) acE.rationalCoefficient := by
  have hc := rationalPullbackCompositionCoherence l E g h sYE sXE sZE aE ahE acE
  unfold HasRationalPullbackCompositionCoherence at hc
  exact hc.2.2.2.2.choose

attribute [local irreducible] rationalCoefficientSheaf in
/-- The module compositor sends iterated unit generators to the restricted unit generator. -/
theorem rationalMixedModuleCompositor_unit (M : pbcModules Y (rationalCoefficientSheaf l Y E))
    (V : Y.ProEt) (m : M.val.obj (op V)) :
    ((rationalMixedModuleCompositor l E g sXE sYE aE h sZE ahE acE).hom.app M).val.app
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
      (rationalCoherenceUnit l E h ahE.rationalCoefficient
        ((rationalPullModule l E g aE.rationalCoefficient).obj M)
        ((proEtaleBaseChange g).obj V)
        (rationalCoherenceUnit l E g aE.rationalCoefficient M V m)) =
    ((rationalPullModule l E (h ≫ g) acE.rationalCoefficient).obj M).val.map
      ((MorphismProperty.Over.pullbackComp h g).inv.app V).op
        (rationalCoherenceUnit l E (h ≫ g) acE.rationalCoefficient M V m) := by
  have hc := rationalPullbackCompositionCoherence l E g h sYE sXE sZE aE ahE acE
  unfold HasRationalPullbackCompositionCoherence at hc
  have hu := hc.2.2.2.2.choose_spec.1 M V m 1 1
  have hs (T : Scheme.{u}) (N : pbcModules T (rationalCoefficientSheaf l T E)) (U : T.ProEtᵒᵖ)
      (x : N.val.obj U) : rationalCoherenceSmul l E T N U 1 x = x := by
    unfold rationalCoherenceSmul
    exact one_smul _ _
  have hsc : rationalCoherenceScalar l E h ahE.rationalCoefficient
      ((proEtaleBaseChange g).obj V) 1 = 1 := by
    unfold rationalCoherenceScalar
    rw [map_one, map_one]
  rw [hs, hs, hsc, one_mul, hs] at hu
  exact hu

/-- The ambient compositor is the derived module compositor on computation counits. -/
theorem rationalMixedGeometricCompositor_counit
    (P : CochainComplex (pbcModules Y (rationalCoefficientSheaf l Y E)) ℤ) :
    (rationalMixedGeometricCompositor l E g sXE sYE aE h sZE ahE acE).hom.app
        (DerivedCategory.Q.obj P) ≫
      rationalPullComplexCounit l E (h ≫ g) acE.rationalCoefficient P =
    (rationalPullDerived l E h ahE.rationalCoefficient).map
        (rationalPullComplexCounit l E g aE.rationalCoefficient P) ≫
      rationalPullComplexCounit l E h ahE.rationalCoefficient
        (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (rationalMixedModuleCompositor l E g sXE sYE aE h sZE ahE acE) (.up ℤ)).hom.app P) := by
  have hc := rationalPullbackCompositionCoherence l E g h sYE sXE sZE aE ahE acE
  unfold HasRationalPullbackCompositionCoherence at hc
  exact hc.2.2.2.2.choose_spec.2.choose_spec.1 P

end GeometricHelpers

section IdentityHelpers
variable (a : RationalRealizationPullbackComparison l E (𝟙 X) sXE sXE)

end IdentityHelpers

section GeometricCoherence
variable {Z : Scheme.{u}} [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]
variable (h : Z ⟶ X) (sZE : RationalModuleRealization l E Z)
  (sZF : RationalModuleRealization l F Z)
  (ahE : RationalRealizationPullbackComparison l E h sZE sXE)
  (acE : RationalRealizationPullbackComparison l E (h ≫ g) sZE sYE)
  (ahF : RationalRealizationPullbackComparison l F h sZF sXF)
  (acF : RationalRealizationPullbackComparison l F (h ≫ g) sZF sYF)
  (mg : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
  (mh : RationalScalarMixedUnitCancellation l E F i h sZE sXE sZF sXF ahE ahF)
  (mc : RationalScalarMixedUnitCancellation l E F i (h ≫ g) sZE sYE sZF sYF acE acF)

omit [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))] in
/-- Maps out of the twice pulled-back scalar extension are detected on iterated unit
generators. -/
private theorem mixed_geometric_hom_ext (M : pbcModules Y (rationalCoefficientSheaf l Y E))
    {N : pbcModules Z (rationalCoefficientSheaf l Z F)}
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l Y F) ⟶ rationalCoefficientSheaf l X F)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l X F) ⟶ rationalCoefficientSheaf l Z F)
    (a b : (rationalPullModule l F h ch).obj ((rationalPullModule l F g cg).obj
      ((pbcExtend (rationalBalancedCoefficient l E F i Y)).obj M)) ⟶ N)
    (H : ∀ (V : Y.ProEt) (m : M.val.obj (op V)),
      a.val.app (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
          (rationalCoherenceUnit l F h ch _ ((proEtaleBaseChange g).obj V)
            (rationalCoherenceUnit l F g cg _ V
              (pbcTensorSection (rationalBalancedCoefficient l E F i Y) M (op V) 1 m))) =
        b.val.app (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
          (rationalCoherenceUnit l F h ch _ ((proEtaleBaseChange g).obj V)
            (rationalCoherenceUnit l F g cg _ V
              (pbcTensorSection (rationalBalancedCoefficient l E F i Y) M (op V) 1 m)))) :
    a = b := by
  apply ((rationalPullModuleAdjunction l F h ch).homEquiv _ _).injective
  apply ((rationalPullModuleAdjunction l F g cg).homEquiv _ _).injective
  apply ((pbcScalarAdjunction (rationalBalancedCoefficient l E F i Y)).homEquiv _ _).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext m
  simp only [Adjunction.homEquiv_unit]
  change a.val.app _ (((rationalPullModuleAdjunction l F h ch).unit.app _).val.app _
      (((rationalPullModuleAdjunction l F g cg).unit.app _).val.app _
        (((pbcScalarAdjunction (rationalBalancedCoefficient l E F i Y)).unit.app M).val.app
          V m))) =
    b.val.app _ (((rationalPullModuleAdjunction l F h ch).unit.app _).val.app _
      (((rationalPullModuleAdjunction l F g cg).unit.app _).val.app _
        (((pbcScalarAdjunction (rationalBalancedCoefficient l E F i Y)).unit.app M).val.app
          V m)))
  rw [WeilConjectures.FdIntegralScalarForward.pbcScalarAdjunction_unit,
    rationalPullModule_unit, rationalPullModule_unit]
  exact H V.unop m

attribute [local irreducible] rationalCoefficientSheaf in
/-- The three ordinary comparisons and the two module compositors commute. -/
private theorem mixed_geometric_ordinary (M : pbcModules Y (rationalCoefficientSheaf l Y E)) :
    (rationalPullModule l F h ahF.rationalCoefficient).map (mg.ordinary.hom.app M) ≫
        mh.ordinary.hom.app ((rationalPullModule l E g aE.rationalCoefficient).obj M) ≫
        (pbcExtend (rationalBalancedCoefficient l E F i Z)).map
          ((rationalMixedModuleCompositor l E g sXE sYE aE h sZE ahE acE).hom.app M) =
      (rationalMixedModuleCompositor l F g sXF sYF aF h sZF ahF acF).hom.app
          ((pbcExtend (rationalBalancedCoefficient l E F i Y)).obj M) ≫
        mc.ordinary.hom.app M := by
  have hg (V : Y.ProEt) (m : M.val.obj (op V)) :
      (mg.ordinary.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
          (rationalCoherenceUnit l F g aF.rationalCoefficient _ V
            (pbcTensorSection (rationalBalancedCoefficient l E F i Y) M (op V) 1 m)) =
        pbcTensorSection (rationalBalancedCoefficient l E F i X)
          ((rationalPullModule l E g aE.rationalCoefficient).obj M)
          (op ((proEtaleBaseChange g).obj V)) 1
          (rationalCoherenceUnit l E g aE.rationalCoefficient M V m) := by
    unfold rationalCoherenceUnit
    exact mg.ordinary_units M V m
  have hh (V : X.ProEt)
      (m : ((rationalPullModule l E g aE.rationalCoefficient).obj M).val.obj (op V)) :
      (mh.ordinary.hom.app ((rationalPullModule l E g aE.rationalCoefficient).obj M)).val.app
          (op ((proEtaleBaseChange h).obj V))
          (rationalCoherenceUnit l F h ahF.rationalCoefficient _ V
            (pbcTensorSection (rationalBalancedCoefficient l E F i X) _ (op V) 1 m)) =
        pbcTensorSection (rationalBalancedCoefficient l E F i Z)
          ((rationalPullModule l E h ahE.rationalCoefficient).obj
            ((rationalPullModule l E g aE.rationalCoefficient).obj M))
          (op ((proEtaleBaseChange h).obj V)) 1
          (rationalCoherenceUnit l E h ahE.rationalCoefficient _ V m) := by
    unfold rationalCoherenceUnit
    exact mh.ordinary_units _ V m
  have hc (V : Y.ProEt) (m : M.val.obj (op V)) :
      (mc.ordinary.hom.app M).val.app (op ((proEtaleBaseChange (h ≫ g)).obj V))
          (rationalCoherenceUnit l F (h ≫ g) acF.rationalCoefficient _ V
            (pbcTensorSection (rationalBalancedCoefficient l E F i Y) M (op V) 1 m)) =
        pbcTensorSection (rationalBalancedCoefficient l E F i Z)
          ((rationalPullModule l E (h ≫ g) acE.rationalCoefficient).obj M)
          (op ((proEtaleBaseChange (h ≫ g)).obj V)) 1
          (rationalCoherenceUnit l E (h ≫ g) acE.rationalCoefficient M V m) := by
    unfold rationalCoherenceUnit
    exact mc.ordinary_units M V m
  apply mixed_geometric_hom_ext l E F i g h M aF.rationalCoefficient ahF.rationalCoefficient
  intro V m
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [rationalPullModule_map_unit l F h ahF.rationalCoefficient (mg.ordinary.hom.app M)]
  rw [hg]
  erw [hh, WeilConjectures.FdIntegralScalarForward.pbcTensor_map,
    rationalMixedModuleCompositor_unit, rationalMixedModuleCompositor_unit]
  erw [PresheafOfModules.naturality_apply, hc, pbcTensorSection_restrict]
  rfl

omit [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))] in
/-- Two natural transformations agreeing at one object agree at every isomorphic object. -/
private theorem mixed_app_eq_of_iso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (τ τ' : F ⟶ G) {A B : C} (e : A ≅ B) (h : τ.app A = τ'.app A) : τ.app B = τ'.app B := by
  rw [← cancel_epi (F.map e.hom), τ.naturality, τ'.naturality, h]

/-- On K-flat representatives, the inverse composition equation follows from the ordinary one. -/
private theorem mixed_geometric_kflat
    (P : CochainComplex (pbcModules Y (rationalCoefficientSheaf l Y E)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology Y)
      (R := rationalCoefficientSheaf l Y E) P) :
    (rationalPullDerived l F h ahF.rationalCoefficient).map
        (mg.zeta.inv.app (DerivedCategory.Q.obj P)) ≫
      mh.zeta.inv.app ((rationalPullDerived l E g aE.rationalCoefficient).obj
        (DerivedCategory.Q.obj P)) =
    (rationalMixedGeometricCompositor l F g sXF sYF aF h sZF ahF acF).hom.app
        ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj
          (DerivedCategory.Q.obj P)) ≫
      mc.zeta.inv.app (DerivedCategory.Q.obj P) ≫
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i Z)).map
        ((rationalMixedGeometricCompositor l E g sXE sYE aE h sZE ahE acE).inv.app
          (DerivedCategory.Q.obj P)) := by
  have hPg := rationalPullModule_isKFlat l E g aE.rationalCoefficient P hP
  have hPhg := rationalPullModule_isKFlat l E h ahE.rationalCoefficient _ hPg
  have := rationalPullComplexCounit_isIso l E g aE.rationalCoefficient
    aE.rational_normalization P
  have := rationalPullComplexCounit_isIso l E h ahE.rationalCoefficient
    ahE.rational_normalization
    (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex (.up ℤ)).obj P)
  have := pbcComplexCounit_isIso (rationalBalancedCoefficient l E F i Z) _ hPhg
  have n1 : mh.zeta.inv.app ((rationalPullDerived l E g aE.rationalCoefficient).obj
        (DerivedCategory.Q.obj P)) ≫
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i Z)).map
        ((rationalPullDerived l E h ahE.rationalCoefficient).map
          (rationalPullComplexCounit l E g aE.rationalCoefficient P)) =
      (rationalPullDerived l F h ahF.rationalCoefficient).map
        ((pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
          (rationalPullComplexCounit l E g aE.rationalCoefficient P)) ≫
      mh.zeta.inv.app (DerivedCategory.Q.obj
        (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex
          (.up ℤ)).obj P)) :=
    (mh.zeta.inv.naturality _).symm
  have n2 := rationalPullComplexCounit_naturality l F h ahF.rationalCoefficient
    (P := ((pbcExtend (rationalBalancedCoefficient l E F i X)).mapHomologicalComplex
      (.up ℤ)).obj
        (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex
          (.up ℤ)).obj P))
    (P' := ((rationalPullModule l F g aF.rationalCoefficient).mapHomologicalComplex
      (.up ℤ)).obj
        (((pbcExtend (rationalBalancedCoefficient l E F i Y)).mapHomologicalComplex
          (.up ℤ)).obj P))
    ((NatIso.mapHomologicalComplex mg.ordinary (.up ℤ)).hom.app P)
  have e1 : (rationalMixedGeometricCompositor l E g sXE sYE aE h sZE ahE acE).inv.app
        (DerivedCategory.Q.obj P) ≫
      (rationalPullDerived l E h ahE.rationalCoefficient).map
        (rationalPullComplexCounit l E g aE.rationalCoefficient P) ≫
      rationalPullComplexCounit l E h ahE.rationalCoefficient
        (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex
          (.up ℤ)).obj P) =
      rationalPullComplexCounit l E (h ≫ g) acE.rationalCoefficient P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (rationalMixedModuleCompositor l E g sXE sYE aE h sZE ahE acE) (.up ℤ)).inv.app P) := by
    rw [← cancel_epi ((rationalMixedGeometricCompositor l E g sXE sYE aE h sZE ahE acE).hom.app
      (DerivedCategory.Q.obj P)), Iso.hom_inv_id_app_assoc,
      reassoc_of% (rationalMixedGeometricCompositor_counit l E g sXE sYE aE h sZE ahE acE P),
      ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have e2 := pbcComplexCounit_naturality (rationalBalancedCoefficient l E F i Z)
    (P := ((rationalPullModule l E h ahE.rationalCoefficient).mapHomologicalComplex (.up ℤ)).obj
      (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex
        (.up ℤ)).obj P))
    ((NatIso.mapHomologicalComplex
      (rationalMixedModuleCompositor l E g sXE sYE aE h sZE ahE acE) (.up ℤ)).inv.app P)
  have e1D : (pbcDerivedExtend (rationalBalancedCoefficient l E F i Z)).map
        ((rationalMixedGeometricCompositor l E g sXE sYE aE h sZE ahE acE).inv.app
          (DerivedCategory.Q.obj P)) ≫
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i Z)).map
        ((rationalPullDerived l E h ahE.rationalCoefficient).map
          (rationalPullComplexCounit l E g aE.rationalCoefficient P)) ≫
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i Z)).map
        (rationalPullComplexCounit l E h ahE.rationalCoefficient
          (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex
            (.up ℤ)).obj P)) ≫
      pbcComplexCounit (rationalBalancedCoefficient l E F i Z)
        (((rationalPullModule l E h ahE.rationalCoefficient).mapHomologicalComplex (.up ℤ)).obj
          (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex
            (.up ℤ)).obj P)) =
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i Z)).map
          (rationalPullComplexCounit l E (h ≫ g) acE.rationalCoefficient P) ≫
        pbcComplexCounit (rationalBalancedCoefficient l E F i Z)
          (((rationalPullModule l E (h ≫ g) acE.rationalCoefficient).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          (((pbcExtend (rationalBalancedCoefficient l E F i Z)).mapHomologicalComplex
            (.up ℤ)).map ((NatIso.mapHomologicalComplex
              (rationalMixedModuleCompositor l E g sXE sYE aE h sZE ahE acE) (.up ℤ)).inv.app
                P)) := by
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, e1,
      Functor.map_comp_assoc, e2]
  have e3 := (rationalMixedGeometricCompositor l F g sXF sYF aF h sZF ahF acF).hom.naturality
    (pbcComplexCounit (rationalBalancedCoefficient l E F i Y) P)
  have e4 := rationalMixedGeometricCompositor_counit l F g sXF sYF aF h sZF ahF acF
    (((pbcExtend (rationalBalancedCoefficient l E F i Y)).mapHomologicalComplex (.up ℤ)).obj P)
  have hM : ((rationalPullModule l F h ahF.rationalCoefficient).mapHomologicalComplex
        (.up ℤ)).map ((NatIso.mapHomologicalComplex mg.ordinary (.up ℤ)).hom.app P) ≫
      (NatIso.mapHomologicalComplex mh.ordinary (.up ℤ)).hom.app
        (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex
          (.up ℤ)).obj P) =
      (NatIso.mapHomologicalComplex
          (rationalMixedModuleCompositor l F g sXF sYF aF h sZF ahF acF) (.up ℤ)).hom.app
        (((pbcExtend (rationalBalancedCoefficient l E F i Y)).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      (NatIso.mapHomologicalComplex mc.ordinary (.up ℤ)).hom.app P ≫
      ((pbcExtend (rationalBalancedCoefficient l E F i Z)).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex
          (rationalMixedModuleCompositor l E g sXE sYE aE h sZE ahE acE) (.up ℤ)).inv.app P) := by
    ext n : 1
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatIso.mapHomologicalComplex_hom_app_f, NatIso.mapHomologicalComplex_inv_app_f]
    rw [← cancel_mono ((pbcExtend (rationalBalancedCoefficient l E F i Z)).map
      ((rationalMixedModuleCompositor l E g sXE sYE aE h sZE ahE acE).hom.app (P.X n)))]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact mixed_geometric_ordinary (mg := mg) (mh := mh) (mc := mc) (M := P.X n)
  rw [← cancel_mono ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Z)).map
      ((rationalPullDerived l E h ahE.rationalCoefficient).map
        (rationalPullComplexCounit l E g aE.rationalCoefficient P)) ≫
    (pbcDerivedExtend (rationalBalancedCoefficient l E F i Z)).map
      (rationalPullComplexCounit l E h ahE.rationalCoefficient
        (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex
          (.up ℤ)).obj P)) ≫
    pbcComplexCounit (rationalBalancedCoefficient l E F i Z)
      (((rationalPullModule l E h ahE.rationalCoefficient).mapHomologicalComplex (.up ℤ)).obj
        (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex
          (.up ℤ)).obj P)))]
  simp only [Category.assoc]
  conv_lhs => rw [reassoc_of% n1, mh.ambient_normalization, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, Category.assoc, mg.ambient_normalization,
    Functor.map_comp_assoc, Functor.map_comp_assoc, reassoc_of% n2]
  conv_rhs => rw [e1D, reassoc_of% mc.ambient_normalization, ← reassoc_of% e3,
    reassoc_of% e4]
  simp only [← Functor.map_comp]
  rw [hM]

/-- The same zeta comparisons commute with geometric composition. -/
theorem rationalMixedGeometricComposition
    (K : DerivedCategory (pbcModules Y (rationalCoefficientSheaf l Y E))) :
    mh.zeta.hom.app ((rationalPullDerived l E g aE.rationalCoefficient).obj K) ≫
        (rationalPullDerived l F h ahF.rationalCoefficient).map (mg.zeta.hom.app K) =
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i Z)).map
          ((rationalMixedGeometricCompositor l E g sXE sYE aE h sZE ahE acE).hom.app K) ≫
        mc.zeta.hom.app K ≫
        (rationalMixedGeometricCompositor l F g sXF sYF aF h sZF ahF acF).inv.app
          ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj K) := by
  have key : ∀ K : DerivedCategory (pbcModules Y (rationalCoefficientSheaf l Y E)),
      (rationalPullDerived l F h ahF.rationalCoefficient).map (mg.zeta.inv.app K) ≫
        mh.zeta.inv.app ((rationalPullDerived l E g aE.rationalCoefficient).obj K) =
      (rationalMixedGeometricCompositor l F g sXF sYF aF h sZF ahF acF).hom.app
          ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj K) ≫
        mc.zeta.inv.app K ≫
        (pbcDerivedExtend (rationalBalancedCoefficient l E F i Z)).map
          ((rationalMixedGeometricCompositor l E g sXE sYE aE h sZE ahE acE).inv.app K) := by
    intro K
    obtain ⟨P, hP, ⟨e⟩⟩ := pbcDerived_exists_kFlat K
    let τ₁ := (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight mg.zeta.inv (rationalPullDerived l F h ahF.rationalCoefficient) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (rationalPullDerived l E g aE.rationalCoefficient) mh.zeta.inv
    let τ₂ := Functor.whiskerLeft (pbcDerivedExtend (rationalBalancedCoefficient l E F i Y))
        (rationalMixedGeometricCompositor l F g sXF sYF aF h sZF ahF acF).hom ≫
      mc.zeta.inv ≫
      Functor.whiskerRight (rationalMixedGeometricCompositor l E g sXE sYE aE h sZE ahE acE).inv
        (pbcDerivedExtend (rationalBalancedCoefficient l E F i Z)) ≫
      (Functor.associator _ _ _).hom
    have h₁ (K) : τ₁.app K =
        (rationalPullDerived l F h ahF.rationalCoefficient).map (mg.zeta.inv.app K) ≫
          mh.zeta.inv.app ((rationalPullDerived l E g aE.rationalCoefficient).obj K) := by
      simp [τ₁]
    have h₂ (K) : τ₂.app K =
        (rationalMixedGeometricCompositor l F g sXF sYF aF h sZF ahF acF).hom.app
            ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj K) ≫
          mc.zeta.inv.app K ≫
          (pbcDerivedExtend (rationalBalancedCoefficient l E F i Z)).map
            ((rationalMixedGeometricCompositor l E g sXE sYE aE h sZE ahE acE).inv.app K) := by
      simp [τ₂]
    rw [← h₁, ← h₂]
    apply mixed_app_eq_of_iso τ₁ τ₂ e
    rw [h₁, h₂]
    exact mixed_geometric_kflat (mg := mg) (mh := mh) (mc := mc) (P := P) (hP := hP)
  let L := mh.zeta.app ((rationalPullDerived l E g aE.rationalCoefficient).obj K) ≪≫
    (rationalPullDerived l F h ahF.rationalCoefficient).mapIso (mg.zeta.app K)
  let R := (pbcDerivedExtend (rationalBalancedCoefficient l E F i Z)).mapIso
      ((rationalMixedGeometricCompositor l E g sXE sYE aE h sZE ahE acE).app K) ≪≫
    mc.zeta.app K ≪≫
    ((rationalMixedGeometricCompositor l F g sXF sYF aF h sZF ahF acF).app
      ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj K)).symm
  exact (Iso.inv_eq_inv L R).1 (by simpa [L, R] using key K)

end GeometricCoherence

section CoefficientCoherence
variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)
  (sXG : RationalModuleRealization l G X) (sYG : RationalModuleRealization l G Y)
  (aG : RationalRealizationPullbackComparison l G g sXG sYG)
  (mEF : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
  (mFG : RationalScalarMixedUnitCancellation l F G j g sXF sYF sXG sYG aF aG)
  (mEG : RationalScalarMixedUnitCancellation l E G (j.comp i) g
    sXE sYE sXG sYG aE aG)

omit [IsNoetherian X] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))] in
/-- Maps out of the pulled-back iterated scalar extension are detected on unit generators. -/
private theorem mixed_tower_hom_ext (M : pbcModules Y (rationalCoefficientSheaf l Y E))
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l Y G) ⟶ rationalCoefficientSheaf l X G)
    {N : pbcModules X (rationalCoefficientSheaf l X G)}
    (a b : (rationalPullModule l G g cg).obj
      ((pbcExtend (rationalBalancedCoefficient l F G j Y)).obj
        ((pbcExtend (rationalBalancedCoefficient l E F i Y)).obj M)) ⟶ N)
    (H : ∀ (V : Y.ProEt) (m : M.val.obj (op V)),
      a.val.app (op ((proEtaleBaseChange g).obj V))
          (rationalCoherenceUnit l G g cg _ V
            (pbcTensorSection (rationalBalancedCoefficient l F G j Y) _ (op V) 1
              (pbcTensorSection (rationalBalancedCoefficient l E F i Y) M (op V) 1 m))) =
        b.val.app (op ((proEtaleBaseChange g).obj V))
          (rationalCoherenceUnit l G g cg _ V
            (pbcTensorSection (rationalBalancedCoefficient l F G j Y) _ (op V) 1
              (pbcTensorSection (rationalBalancedCoefficient l E F i Y) M (op V) 1 m)))) :
    a = b := by
  apply ((rationalPullModuleAdjunction l G g cg).homEquiv _ _).injective
  apply WeilConjectures.FdIntegralScalarForward.pbcTensor_ext₂
    (rationalBalancedCoefficient l E F i Y) (rationalBalancedCoefficient l F G j Y)
  intro V m
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change a.val.app _ (((rationalPullModuleAdjunction l G g cg).unit.app _).val.app V _) =
    b.val.app _ (((rationalPullModuleAdjunction l G g cg).unit.app _).val.app V _)
  rw [rationalPullModule_unit]
  exact H V.unop m

/-- The ordinary comparisons respect the ordinary coefficient associators. -/
private theorem mixed_tower_ordinary (M : pbcModules Y (rationalCoefficientSheaf l Y E)) :
    mFG.ordinary.hom.app ((pbcExtend (rationalBalancedCoefficient l E F i Y)).obj M) ≫
        (pbcExtend (rationalBalancedCoefficient l F G j X)).map (mEF.ordinary.hom.app M) ≫
        (WeilConjectures.FdIntegralScalarForward.pbcExtendComp
          (rationalBalancedCoefficient l E F i X) (rationalBalancedCoefficient l F G j X)
          (rationalBalancedCoefficient l E G (j.comp i) X)
          (rationalBalancedCoefficient_comp l E F i X G j)).hom.app
            ((rationalPullModule l E g aE.rationalCoefficient).obj M) =
      (rationalPullModule l G g aG.rationalCoefficient).map
          ((WeilConjectures.FdIntegralScalarForward.pbcExtendComp
            (rationalBalancedCoefficient l E F i Y) (rationalBalancedCoefficient l F G j Y)
            (rationalBalancedCoefficient l E G (j.comp i) Y)
            (rationalBalancedCoefficient_comp l E F i Y G j)).hom.app M) ≫
        mEG.ordinary.hom.app M := by
  have hFG (V : Y.ProEt)
      (m : ((pbcExtend (rationalBalancedCoefficient l E F i Y)).obj M).val.obj (op V)) :
      (mFG.ordinary.hom.app ((pbcExtend (rationalBalancedCoefficient l E F i Y)).obj M)).val.app
          (op ((proEtaleBaseChange g).obj V))
          (rationalCoherenceUnit l G g aG.rationalCoefficient _ V
            (pbcTensorSection (rationalBalancedCoefficient l F G j Y) _ (op V) 1 m)) =
        pbcTensorSection (rationalBalancedCoefficient l F G j X)
          ((rationalPullModule l F g aF.rationalCoefficient).obj
            ((pbcExtend (rationalBalancedCoefficient l E F i Y)).obj M))
          (op ((proEtaleBaseChange g).obj V)) 1
          (rationalCoherenceUnit l F g aF.rationalCoefficient _ V m) := by
    unfold rationalCoherenceUnit
    exact mFG.ordinary_units _ V m
  have hEF (V : Y.ProEt) (m : M.val.obj (op V)) :
      (mEF.ordinary.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
          (rationalCoherenceUnit l F g aF.rationalCoefficient _ V
            (pbcTensorSection (rationalBalancedCoefficient l E F i Y) M (op V) 1 m)) =
        pbcTensorSection (rationalBalancedCoefficient l E F i X)
          ((rationalPullModule l E g aE.rationalCoefficient).obj M)
          (op ((proEtaleBaseChange g).obj V)) 1
          (rationalCoherenceUnit l E g aE.rationalCoefficient M V m) := by
    unfold rationalCoherenceUnit
    exact mEF.ordinary_units M V m
  have hEG (V : Y.ProEt) (m : M.val.obj (op V)) :
      (mEG.ordinary.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
          (rationalCoherenceUnit l G g aG.rationalCoefficient _ V
            (pbcTensorSection (rationalBalancedCoefficient l E G (j.comp i) Y) M (op V) 1 m)) =
        pbcTensorSection (rationalBalancedCoefficient l E G (j.comp i) X)
          ((rationalPullModule l E g aE.rationalCoefficient).obj M)
          (op ((proEtaleBaseChange g).obj V)) 1
          (rationalCoherenceUnit l E g aE.rationalCoefficient M V m) := by
    unfold rationalCoherenceUnit
    exact mEG.ordinary_units M V m
  apply mixed_tower_hom_ext (i := i) (j := j) (g := g) (M := M) (cg := aG.rationalCoefficient)
  intro V m
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [hFG, WeilConjectures.FdIntegralScalarForward.pbcTensor_map, hEF,
    WeilConjectures.FdIntegralScalarForward.pbcExtendComp_tensor]
  erw [rationalPullModule_map_unit l G g aG.rationalCoefficient
    ((WeilConjectures.FdIntegralScalarForward.pbcExtendComp
      (rationalBalancedCoefficient l E F i Y) (rationalBalancedCoefficient l F G j Y)
      (rationalBalancedCoefficient l E G (j.comp i) Y)
      (rationalBalancedCoefficient_comp l E F i Y G j)).hom.app M)]
  erw [WeilConjectures.FdIntegralScalarForward.pbcExtendComp_tensor, hEG]

/-- On K-flat representatives, the inverse tower equation follows from the ordinary one. -/
private theorem mixed_tower_kflat
    (P : CochainComplex (pbcModules Y (rationalCoefficientSheaf l Y E)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology Y)
      (R := rationalCoefficientSheaf l Y E) P) :
    mFG.zeta.inv.app ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj
        (DerivedCategory.Q.obj P)) ≫
      (pbcDerivedExtend (rationalBalancedCoefficient l F G j X)).map
        (mEF.zeta.inv.app (DerivedCategory.Q.obj P)) ≫
      (pbcReductionNormalization (rationalBalancedCoefficient l E F i X)
        (rationalBalancedCoefficient l F G j X)
        (rationalBalancedCoefficient l E G (j.comp i) X)
        (rationalBalancedCoefficient_comp l E F i X G j)
        ((rationalPullDerived l E g aE.rationalCoefficient).obj
          (DerivedCategory.Q.obj P))).hom =
    (rationalPullDerived l G g aG.rationalCoefficient).map
        ((pbcReductionNormalization (rationalBalancedCoefficient l E F i Y)
          (rationalBalancedCoefficient l F G j Y)
          (rationalBalancedCoefficient l E G (j.comp i) Y)
          (rationalBalancedCoefficient_comp l E F i Y G j) (DerivedCategory.Q.obj P)).hom) ≫
      mEG.zeta.inv.app (DerivedCategory.Q.obj P) := by
  have hPg := rationalPullModule_isKFlat l E g aE.rationalCoefficient P hP
  have := rationalPullComplexCounit_isIso l E g aE.rationalCoefficient
    aE.rational_normalization P
  have := pbcComplexCounit_isIso (rationalBalancedCoefficient l E G (j.comp i) X) _ hPg
  have n1 := pbcReductionNormalization_naturality (rationalBalancedCoefficient l E F i X)
    (rationalBalancedCoefficient l F G j X) (rationalBalancedCoefficient l E G (j.comp i) X)
    (rationalBalancedCoefficient_comp l E F i X G j)
    (rationalPullComplexCounit l E g aE.rationalCoefficient P)
  have a1 := pbcReductionNormalization_counit (rationalBalancedCoefficient l E F i X)
    (rationalBalancedCoefficient l F G j X) (rationalBalancedCoefficient l E G (j.comp i) X)
    (rationalBalancedCoefficient_comp l E F i X G j)
    (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex (.up ℤ)).obj P)
  have a2 := pbcReductionNormalization_counit (rationalBalancedCoefficient l E F i Y)
    (rationalBalancedCoefficient l F G j Y) (rationalBalancedCoefficient l E G (j.comp i) Y)
    (rationalBalancedCoefficient_comp l E F i Y G j) P
  have n3 := pbcComplexCounit_naturality (rationalBalancedCoefficient l F G j X)
    (P := ((pbcExtend (rationalBalancedCoefficient l E F i X)).mapHomologicalComplex
      (.up ℤ)).obj
        (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex
          (.up ℤ)).obj P))
    (P' := ((rationalPullModule l F g aF.rationalCoefficient).mapHomologicalComplex
      (.up ℤ)).obj
        (((pbcExtend (rationalBalancedCoefficient l E F i Y)).mapHomologicalComplex
          (.up ℤ)).obj P))
    ((NatIso.mapHomologicalComplex mEF.ordinary (.up ℤ)).hom.app P)
  have n4 : mFG.zeta.inv.app ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj
        (DerivedCategory.Q.obj P)) ≫
      (pbcDerivedExtend (rationalBalancedCoefficient l F G j X)).map
        ((rationalPullDerived l F g aF.rationalCoefficient).map
          (pbcComplexCounit (rationalBalancedCoefficient l E F i Y) P)) =
      (rationalPullDerived l G g aG.rationalCoefficient).map
        ((pbcDerivedExtend (rationalBalancedCoefficient l F G j Y)).map
          (pbcComplexCounit (rationalBalancedCoefficient l E F i Y) P)) ≫
      mFG.zeta.inv.app (DerivedCategory.Q.obj
        (((pbcExtend (rationalBalancedCoefficient l E F i Y)).mapHomologicalComplex
          (.up ℤ)).obj P)) :=
    (mFG.zeta.inv.naturality _).symm
  have n5 := rationalPullComplexCounit_naturality l G g aG.rationalCoefficient
    (P := ((pbcExtend (rationalBalancedCoefficient l E G (j.comp i) Y)).mapHomologicalComplex
      (.up ℤ)).obj P)
    (P' := ((pbcExtend (rationalBalancedCoefficient l F G j Y)).mapHomologicalComplex
      (.up ℤ)).obj
        (((pbcExtend (rationalBalancedCoefficient l E F i Y)).mapHomologicalComplex
          (.up ℤ)).obj P))
    ((NatIso.mapHomologicalComplex (WeilConjectures.FdIntegralScalarForward.pbcExtendComp
      (rationalBalancedCoefficient l E F i Y) (rationalBalancedCoefficient l F G j Y)
      (rationalBalancedCoefficient l E G (j.comp i) Y)
      (rationalBalancedCoefficient_comp l E F i Y G j)) (.up ℤ)).hom.app P)
  have hM : (NatIso.mapHomologicalComplex mFG.ordinary (.up ℤ)).hom.app
        (((pbcExtend (rationalBalancedCoefficient l E F i Y)).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      ((pbcExtend (rationalBalancedCoefficient l F G j X)).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex mEF.ordinary (.up ℤ)).hom.app P) ≫
      (NatIso.mapHomologicalComplex (WeilConjectures.FdIntegralScalarForward.pbcExtendComp
        (rationalBalancedCoefficient l E F i X) (rationalBalancedCoefficient l F G j X)
        (rationalBalancedCoefficient l E G (j.comp i) X)
        (rationalBalancedCoefficient_comp l E F i X G j)) (.up ℤ)).hom.app
          (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex
            (.up ℤ)).obj P) =
      ((rationalPullModule l G g aG.rationalCoefficient).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex (WeilConjectures.FdIntegralScalarForward.pbcExtendComp
          (rationalBalancedCoefficient l E F i Y) (rationalBalancedCoefficient l F G j Y)
          (rationalBalancedCoefficient l E G (j.comp i) Y)
          (rationalBalancedCoefficient_comp l E F i Y G j)) (.up ℤ)).hom.app P) ≫
      (NatIso.mapHomologicalComplex mEG.ordinary (.up ℤ)).hom.app P := by
    ext n : 1
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatIso.mapHomologicalComplex_hom_app_f]
    exact mixed_tower_ordinary (mEF := mEF) (mFG := mFG) (mEG := mEG) (M := P.X n)
  rw [← cancel_mono ((pbcDerivedExtend (rationalBalancedCoefficient l E G (j.comp i) X)).map
      (rationalPullComplexCounit l E g aE.rationalCoefficient P) ≫
    pbcComplexCounit (rationalBalancedCoefficient l E G (j.comp i) X)
      (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex (.up ℤ)).obj P))]
  simp only [Category.assoc]
  conv_lhs => rw [← reassoc_of% n1, a1, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    Category.assoc, mEF.ambient_normalization, Functor.map_comp_assoc, Functor.map_comp_assoc,
    reassoc_of% n3, reassoc_of% n4, reassoc_of% mFG.ambient_normalization]
  conv_rhs => rw [mEG.ambient_normalization, ← Functor.map_comp_assoc, a2,
    Functor.map_comp_assoc, Functor.map_comp_assoc, reassoc_of% n5]
  simp only [← Functor.map_comp]
  rw [hM]

/-- The same zeta comparisons respect the specified coefficient associators. -/
theorem rationalMixedCoefficientTower
    (K : DerivedCategory (pbcModules Y (rationalCoefficientSheaf l Y E))) :
    (pbcDerivedExtend (rationalBalancedCoefficient l F G j X)).map (mEF.zeta.hom.app K) ≫
      mFG.zeta.hom.app ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj K) ≫
      (rationalPullDerived l G g aG.rationalCoefficient).map
        ((pbcReductionNormalization (rationalBalancedCoefficient l E F i Y)
          (rationalBalancedCoefficient l F G j Y)
          (rationalBalancedCoefficient l E G (j.comp i) Y)
          (rationalBalancedCoefficient_comp l E F i Y G j) K).hom) =
    (pbcReductionNormalization (rationalBalancedCoefficient l E F i X)
      (rationalBalancedCoefficient l F G j X)
      (rationalBalancedCoefficient l E G (j.comp i) X)
      (rationalBalancedCoefficient_comp l E F i X G j)
      ((rationalPullDerived l E g aE.rationalCoefficient).obj K)).hom ≫
        mEG.zeta.hom.app K := by
  let NX := (Adjunction.leftAdjointCompIso
    (pbcDerivedScalarAdjunction (rationalBalancedCoefficient l E F i X))
    (pbcDerivedScalarAdjunction (rationalBalancedCoefficient l F G j X))
    (pbcDerivedScalarAdjunction (rationalBalancedCoefficient l E G (j.comp i) X))
    (pbcDerivedRestrictComp _ _ _ (rationalBalancedCoefficient_comp l E F i X G j))).hom
  let NY := (Adjunction.leftAdjointCompIso
    (pbcDerivedScalarAdjunction (rationalBalancedCoefficient l E F i Y))
    (pbcDerivedScalarAdjunction (rationalBalancedCoefficient l F G j Y))
    (pbcDerivedScalarAdjunction (rationalBalancedCoefficient l E G (j.comp i) Y))
    (pbcDerivedRestrictComp _ _ _ (rationalBalancedCoefficient_comp l E F i Y G j))).hom
  have key : ∀ K : DerivedCategory (pbcModules Y (rationalCoefficientSheaf l Y E)),
      mFG.zeta.inv.app ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj K) ≫
        (pbcDerivedExtend (rationalBalancedCoefficient l F G j X)).map (mEF.zeta.inv.app K) ≫
        (pbcReductionNormalization (rationalBalancedCoefficient l E F i X)
          (rationalBalancedCoefficient l F G j X)
          (rationalBalancedCoefficient l E G (j.comp i) X)
          (rationalBalancedCoefficient_comp l E F i X G j)
          ((rationalPullDerived l E g aE.rationalCoefficient).obj K)).hom =
      (rationalPullDerived l G g aG.rationalCoefficient).map
          ((pbcReductionNormalization (rationalBalancedCoefficient l E F i Y)
            (rationalBalancedCoefficient l F G j Y)
            (rationalBalancedCoefficient l E G (j.comp i) Y)
            (rationalBalancedCoefficient_comp l E F i Y G j) K).hom) ≫
        mEG.zeta.inv.app K := by
    intro K
    obtain ⟨P, hP, ⟨e⟩⟩ := pbcDerived_exists_kFlat K
    let τ₁ := (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (pbcDerivedExtend (rationalBalancedCoefficient l E F i Y))
        mFG.zeta.inv ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight mEF.zeta.inv (pbcDerivedExtend (rationalBalancedCoefficient l F G j X)) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (rationalPullDerived l E g aE.rationalCoefficient) NX
    let τ₂ := Functor.whiskerRight NY (rationalPullDerived l G g aG.rationalCoefficient) ≫
      mEG.zeta.inv
    have h₁ (K) : τ₁.app K =
        mFG.zeta.inv.app ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj K) ≫
          (pbcDerivedExtend (rationalBalancedCoefficient l F G j X)).map
            (mEF.zeta.inv.app K) ≫
          (pbcReductionNormalization (rationalBalancedCoefficient l E F i X)
            (rationalBalancedCoefficient l F G j X)
            (rationalBalancedCoefficient l E G (j.comp i) X)
            (rationalBalancedCoefficient_comp l E F i X G j)
            ((rationalPullDerived l E g aE.rationalCoefficient).obj K)).hom := by
      simp [τ₁, NX, pbcReductionNormalization_hom_eq]
    have h₂ (K) : τ₂.app K =
        (rationalPullDerived l G g aG.rationalCoefficient).map
            ((pbcReductionNormalization (rationalBalancedCoefficient l E F i Y)
              (rationalBalancedCoefficient l F G j Y)
              (rationalBalancedCoefficient l E G (j.comp i) Y)
              (rationalBalancedCoefficient_comp l E F i Y G j) K).hom) ≫
          mEG.zeta.inv.app K := by
      simp [τ₂, NY, pbcReductionNormalization_hom_eq]
    rw [← h₁, ← h₂]
    apply mixed_app_eq_of_iso τ₁ τ₂ e
    rw [h₁, h₂]
    exact mixed_tower_kflat (mEF := mEF) (mFG := mFG) (mEG := mEG) (P := P) (hP := hP)
  rw [← cancel_epi (mFG.zeta.inv.app
      ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj K) ≫
    (pbcDerivedExtend (rationalBalancedCoefficient l F G j X)).map (mEF.zeta.inv.app K))]
  conv_rhs => rw [Category.assoc, reassoc_of% (key K), Iso.inv_hom_id_app]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Iso.inv_hom_id_app_assoc]

end CoefficientCoherence

section Pentagon
variable (G H : Type u) [Field G] [Field H]
  [Algebra ℚ_[l] G] [Algebra ℚ_[l] H]
  [FiniteDimensional ℚ_[l] G] [FiniteDimensional ℚ_[l] H]
  (j : F →ₐ[ℚ_[l]] G) (k : G →ₐ[ℚ_[l]] H)
  (sXH : RationalModuleRealization l H X) (sYH : RationalModuleRealization l H Y)
  (aH : RationalRealizationPullbackComparison l H g sXH sYH)
  (mEH : RationalScalarMixedUnitCancellation l E H (k.comp (j.comp i)) g
    sXE sYE sXH sYH aE aH)

end Pentagon

end AlgebraicGeometry.Scheme
