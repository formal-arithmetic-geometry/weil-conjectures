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

/-! # Cancellation in the specified mixed rational realization square

Source: Bhatt--Scholze, Remark 6.8.15, pp. 61--62; Stacks Tags 0G7E, 0D6D and 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Theta and D below are rationalBalancedTheta and extension along
rationalBalancedCoefficient. The completed comparison is rationalScalarStrictBeta.
The pullback alpha is the supplied, generator-normalized dependency record's alpha.
The ordinary zeta is normalized on tensor generators and derived computation counits.
No declarations from the downstream parent scalar-coherence module are imported.
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

/-- The specified strict beta, restricted and rationalized, on every unchanged raw object.
Source: BS 6.8.15; Stacks 0A0E, 099N
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
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

/-- Scalar extension of the actual invertible completion unit, including raw-object transports.
Source: BS 6.8.15 (blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedUnitPrecomposition (g : X ⟶ Y)
    (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
    (sXF : RationalModuleRealization l F X)
    (aE : RationalRealizationPullbackComparison l E g sXE sYE)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :=
  sXF.J.map
    ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).map
      ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map
        (ObjectProperty.homMk
          (X := ⟨(pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj,
            aE.integral.ordinary_mem K⟩)
          (Y := (aE.integral.completedFunctor l E).obj K)
          ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj)) ≫
        eqToHom (aE.raw_objects K).symm))

/-- The mixed square for the specific alpha and the specified scalar/pullback comparison.
The ordinary comparison is fixed on tensor units and on derived computation counits;
its section formula determines the balanced map, including all coefficient factors.
Source: BS 6.8.15; Stacks 0D6D, 0A0E and 0A0G
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
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
  /-- The raw comparison is the actual rationalScalarStrictBeta, with no new choice. -/
  beta : aE.rawPull ⋙ pbcRationalScalarExtension l E F i X Fact.out Fact.out ≅
    pbcRationalScalarExtension l E F i Y Fact.out Fact.out ⋙ aF.rawPull
  /-- All components, not just their endpoint isomorphism classes, are fixed. -/
  beta_normalization : ∀ K : PbcRationalDerivedCategory l E Y Fact.out Fact.out,
    beta.app K = rationalMixedBetaComponent l E F i g sXE sYE sXF sYF aE aF K
  /-- The displayed equation, in the node's orientation, for every raw rational object. -/
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

/-- The mixed equation uses exactly the owning dependencies' theta, D, strict beta and alpha.
Source: BS Remark 6.8.15, pp. 61--62; Stacks 0G7E, 0D6D, 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof, following the seven steps of this node:
1. Ordinary pullback and finite scalar extension preserve the three integral
constructibility conditions. The actual quotient-completion units are invertible.
2. Precompose by scalar extension of that unit. Naturality of rationalBalancedTheta
and alpha_normalization cancel the E unit. The actual unit equation for
rationalScalarStrictBeta and alpha_normalization cancel the F unit on the other path.
3. On a simultaneous flat-term K-flat model the remaining normalized maps flatten
l' tensor b' tensor p to l' i(b') tensor p. The finite-projection coefficient square
makes this balanced. It commutes with restrictions and differentials, hence descends.
Cancel the invertible precomposition to obtain compatibility for the specified maps.
4. Multiply integral naturality by the reciprocal denominator. The annihilating-power
fraction criterion proves descent even when the integral Hom groups have torsion.
5. For two geometric maps use the canonical inverse-image compositor. Both remaining
ordinary routes send l'' tensor l' tensor p to l'' c_h(l') tensor p; identity is
multiplication. The derived computation counits retain these particular maps.
6. Substitute alpha as ordinary balancing after inverse completion unit. The reflected
unit and compositor equations cancel every adjacent inverse-unit/unit pair.
7. For successive fields the specified scalar associators flatten to multiplication;
three scalar factors have product nml independently of parentheses. Thus the four-field
pentagon, identity and both orders of mixed pasting agree. Reinsert the same outer
units, and descend all these equations to raw fractions as in step 4. -/
theorem rationalScalarMixedUnitCancellation :
    Nonempty (RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF) := by
  sorry

/-- The left route of the specified raw mixed square.
Source: BS 6.8.15 (blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedLeft (m : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
    (K : PbcRationalDerivedCategory l E Y Fact.out Fact.out) :=
  (rationalBalancedTheta l E F i X sXE sXF).hom.app (aE.rawPull.obj K) ≫
    (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
      (aE.alpha.hom.app K) ≫ m.zeta.hom.app (sYE.J.obj K)

/-- The right route of the specified raw mixed square.
Source: BS 6.8.15 (blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedRight (m : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
    (K : PbcRationalDerivedCategory l E Y Fact.out Fact.out) :=
  sXF.J.map (m.beta.hom.app K) ≫
    aF.alpha.hom.app ((pbcRationalScalarExtension l E F i Y Fact.out Fact.out).obj K) ≫
    (rationalPullDerived l F g aF.rationalCoefficient).map
      ((rationalBalancedTheta l E F i Y sYE sYF).hom.app K)

/-- The common ordinary balanced map after precomposing by the specified unit.
Source: BS 6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedOrdinaryPath
    (m : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :=
  (rationalBalancedTheta l E F i X sXE sXF).hom.app
      ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj
        ⟨(pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj,
          aE.integral.ordinary_mem K⟩) ≫
    (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
      (eqToHom (sXE.objects
        ⟨(pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj,
          aE.integral.ordinary_mem K⟩) ≫
        aE.ordinaryComparison.hom.app K.obj ≫
        (rationalPullDerived l E g aE.rationalCoefficient).map
          (eqToHom (sYE.objects K).symm)) ≫
    m.zeta.hom.app (sYE.J.obj
      ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K))

private theorem mixed_scalar_map
    {W : Scheme.{u}} [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]
    {A B : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E)} (f : A ⟶ B) :
    (pbcRationalScalarExtension l E F i W Fact.out Fact.out).map
        ((pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) =
      (pbcRationalization W (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        ((pbcEmbeddingIntegralTensor l E F i W Fact.out Fact.out).map f) := by
  change pbcRationalScalarHom l E F i W Fact.out Fact.out A B
    ((pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) = _
  have h := (pbcRationalScalarHom_exists l E F i W Fact.out Fact.out A B).exists.choose_spec
    (1 : Localization.Away (pbcUniformizer l E)) f
  simpa only [map_one, one_smul, pbcRationalScalarHom] using h

private theorem mixed_raw_map
    {A B : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)} (f : A ⟶ B) :
    aE.rawPull.map
        ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) =
      eqToHom (aE.raw_objects A) ≫
        (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map
          ((aE.integral.completedFunctor l E).map f) ≫ eqToHom (aE.raw_objects B).symm := by
  simpa only [rationalPullFraction, pow_zero, one_smul] using aE.raw_fractions A B f 0

private theorem mixed_realization_map
    {W : Scheme.{u}} [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]
    (s : RationalModuleRealization l E W)
    {A B : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E)} (f : A ⟶ B) :
    s.J.map ((pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) =
      eqToHom (s.objects A) ≫ (pbcDerivedExtend (rationalPullScalar l E s)).map f.hom ≫
        eqToHom (s.objects B).symm := by
  simpa only [pow_zero, inv_one, map_one, one_smul] using s.fractions A B f 0

/-- Both routes become the same ordinary map after the specified isomorphism.
Source: BS 6.8.15; Stacks 0G7E, 0D6D
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof, following the seven steps of this node:
1. Ordinary pullback and finite scalar extension preserve the three integral
constructibility conditions. The actual quotient-completion units are invertible.
2. Precompose by scalar extension of that unit. Naturality of rationalBalancedTheta
and alpha_normalization cancel the E unit. The actual unit equation for
rationalScalarStrictBeta and alpha_normalization cancel the F unit on the other path.
3. On a simultaneous flat-term K-flat model the remaining normalized maps flatten
l' tensor b' tensor p to l' i(b') tensor p. The finite-projection coefficient square
makes this balanced. It commutes with restrictions and differentials, hence descends.
Cancel the invertible precomposition to obtain compatibility for the specified maps.
4. Multiply integral naturality by the reciprocal denominator. The annihilating-power
fraction criterion proves descent even when the integral Hom groups have torsion.
5. For two geometric maps use the canonical inverse-image compositor. Both remaining
ordinary routes send l'' tensor l' tensor p to l'' c_h(l') tensor p; identity is
multiplication. The derived computation counits retain these particular maps.
6. Substitute alpha as ordinary balancing after inverse completion unit. The reflected
unit and compositor equations cancel every adjacent inverse-unit/unit pair.
7. For successive fields the specified scalar associators flatten to multiplication;
three scalar factors have product nml independently of parentheses. Thus the four-field
pentagon, identity and both orders of mixed pasting agree. Reinsert the same outer
units, and descend all these equations to raw fractions as in step 4. -/
theorem rationalMixedUnitPrecomposition_eq
    (m : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :
    IsIso (rationalMixedUnitPrecomposition l E F i g sXE sYE sXF aE K) ∧
    (rationalMixedUnitPrecomposition l E F i g sXE sYE sXF aE K ≫
      rationalMixedLeft l E F i g sXE sYE sXF sYF aE aF m
        ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
      rationalMixedOrdinaryPath l E F i g sXE sYE sXF sYF aE aF m K) ∧
    (rationalMixedUnitPrecomposition l E F i g sXE sYE sXF aE K ≫
      rationalMixedRight l E F i g sXE sYE sXF sYF aE aF m
        ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
      rationalMixedOrdinaryPath l E F i g sXE sYE sXF sYF aE aF m K) := by
  let A : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E) :=
    ⟨(pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj,
      aE.integral.ordinary_mem K⟩
  let B := (aE.integral.completedFunctor l E).obj K
  let f : A ⟶ B := ObjectProperty.homMk
    ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj)
  have hf : IsIso f := (ObjectProperty.isIso_hom_iff f).mp (aE.integral.unit_isIso K)
  let n := (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map f ≫
    eqToHom (aE.raw_objects K).symm
  have hn : sXE.J.map n ≫ aE.alpha.hom.app
        ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
      eqToHom (sXE.objects A) ≫ aE.ordinaryComparison.hom.app K.obj ≫
        (rationalPullDerived l E g aE.rationalCoefficient).map
          (eqToHom (sYE.objects K).symm) := by
    dsimp only [n]
    rw [sXE.J.map_comp, mixed_realization_map]
    have h := congrArg (fun q ↦ eqToHom (sXE.objects A) ≫ q ≫
      (rationalPullDerived l E g aE.rationalCoefficient).map
        (eqToHom (sYE.objects K).symm)) (aE.alpha_normalization K)
    simp only [Category.assoc] at h
    rw [← Functor.map_comp, eqToHom_trans, eqToHom_refl,
      CategoryTheory.Functor.map_id] at h
    erw [Category.comp_id] at h
    dsimp only [f, ObjectProperty.homMk]
    simpa only [Category.assoc] using h
  have hleft : rationalMixedUnitPrecomposition l E F i g sXE sYE sXF aE K ≫
      rationalMixedLeft l E F i g sXE sYE sXF sYF aE aF m
        ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
      rationalMixedOrdinaryPath l E F i g sXE sYE sXF sYF aE aF m K := by
    unfold rationalMixedUnitPrecomposition rationalMixedLeft rationalMixedOrdinaryPath
    change sXF.J.map ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).map n) ≫
      (rationalBalancedTheta l E F i X sXE sXF).hom.app _ ≫ _ = _
    have ht := (rationalBalancedTheta l E F i X sXE sXF).hom.naturality n
    simp only [Functor.comp_map] at ht
    rw [← Category.assoc, ht]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hn]
  refine ⟨?_, hleft, ?_⟩
  · change IsIso (sXF.J.map
      ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).map n))
    dsimp only [n]
    infer_instance
  · simpa only [rationalMixedRight, rationalMixedLeft, m.compatibility] using hleft

private theorem mixed_tensor_smul {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : pbcModules W R) (U : W.ProEtᵒᵖ) (c : S.obj.obj U) (x : M.val.obj U) :
    pbcTensorSection φ M U c x = c • pbcTensorSection φ M U 1 x := by
  change completedAdicChangeTensor W φ M U c x =
    c • completedAdicChangeTensor W φ M U 1 x
  simpa only [mul_one] using completedTensor_smul W φ M U c 1 x

private theorem mixed_tensor_unit_smul {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : pbcModules W R) (U : W.ProEtᵒᵖ) (b : R.obj.obj U) (x : M.val.obj U) :
    pbcTensorSection φ M U 1 (b • x) =
      φ.hom.app U b • pbcTensorSection φ M U 1 x := by
  have hunit := (pbcScalarAdjunction_exists φ).exists.choose_spec
  conv_lhs => rw [← hunit M U (b • x)]
  conv_rhs => rw [← hunit M U x]
  change _ = b • ((pbcScalarAdjunction φ).unit.app M).val.app U x
  exact (((pbcScalarAdjunction φ).unit.app M).val.app U).hom.map_smul b x

/-- The ordinary zeta has the full local formula, before tensor flattening.
Source: BS 6.8.15, pp. 61--62; Stacks 0G7E, 0D6D and 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: precompose with scalar extension of the actual completion units. Substitute
the recorded alpha normalization and rationalScalarCompletionUnitSquare. Adjacent
inverse-unit/unit factors cancel. On the same flat-term K-flat representative all
remaining comparisons are the generator-normalized ordinary tensor maps. Geometric
composition uses the canonical inverse-image compositor and scalar insertion; coefficient
composition multiplies the scalar factors. Their associative product is independent of
parentheses. The normalized derived computation counits descend these maps, and the
annihilating-power fraction criterion extends the equations to raw rational morphisms. -/
theorem rationalMixedOrdinarySections
    (m : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
    (M : pbcModules Y (rationalCoefficientSheaf l Y E)) (V : Y.ProEt)
    (p : M.val.obj (op V))
    (b : (rationalCoefficientSheaf l X E).obj.obj (op ((proEtaleBaseChange g).obj V)))
    (c : (rationalCoefficientSheaf l X F).obj.obj (op ((proEtaleBaseChange g).obj V))) :
    (m.ordinary.inv.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (pbcTensorSection (rationalBalancedCoefficient l E F i X)
        ((rationalPullModule l E g aE.rationalCoefficient).obj M)
        (op ((proEtaleBaseChange g).obj V)) c
        (b • rationalCoherenceUnit l E g aE.rationalCoefficient M V p)) =
      (c * (rationalBalancedCoefficient l E F i X).hom.app
        (op ((proEtaleBaseChange g).obj V)) b) •
        rationalCoherenceUnit l F g aF.rationalCoefficient
          ((pbcExtend (rationalBalancedCoefficient l E F i Y)).obj M) V
          (pbcTensorSection (rationalBalancedCoefficient l E F i Y) M (op V) 1 p) := by
  let U := op ((proEtaleBaseChange g).obj V)
  let N := (rationalPullModule l E g aE.rationalCoefficient).obj M
  let φ := rationalBalancedCoefficient l E F i X
  let x := rationalCoherenceUnit l E g aE.rationalCoefficient M V p
  let y := rationalCoherenceUnit l F g aF.rationalCoefficient
    ((pbcExtend (rationalBalancedCoefficient l E F i Y)).obj M) V
    (pbcTensorSection (rationalBalancedCoefficient l E F i Y) M (op V) 1 p)
  have hunit : (m.ordinary.hom.app M).val.app U y =
      pbcTensorSection φ N U 1 x := by
    dsimp only [x, y]
    unfold rationalCoherenceUnit
    exact m.ordinary_units M V p
  have hinv : (m.ordinary.inv.app M).val.app U
      (pbcTensorSection φ N U 1 x) = y := by
    rw [← hunit]
    have h := congrArg (fun f ↦ f.val.app U y) (m.ordinary.hom_inv_id_app M)
    exact h
  change (m.ordinary.inv.app M).val.app U (pbcTensorSection φ N U c (b • x)) =
    (c * φ.hom.app U b) • y
  rw [mixed_tensor_smul, mixed_tensor_unit_smul, map_smul, map_smul, hinv, mul_smul]

section GeometricHelpers
variable {Z : Scheme.{u}} [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]
variable (h : Z ⟶ X) (sZE : RationalModuleRealization l E Z)
  (ahE : RationalRealizationPullbackComparison l E h sZE sXE)
  (acE : RationalRealizationPullbackComparison l E (h ≫ g) sZE sYE)

/-- The ambient compositor extracted from the full normalized dependency theorem.
Its tensor-generator, inverse-image-pasting, computation-counit and strict-unit equations
fix its maps; this does not select from an unnormalized endpoint-isomorphism existence.
Source: BS 6.8.15; Stacks 0D6D, 099N
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedGeometricCompositor :
    rationalPullDerived l E g aE.rationalCoefficient ⋙
      rationalPullDerived l E h ahE.rationalCoefficient ≅
    rationalPullDerived l E (h ≫ g) acE.rationalCoefficient := by
  have hc := rationalPullbackCompositionCoherence l E g h sYE sXE sZE aE ahE acE
  unfold HasRationalPullbackCompositionCoherence at hc
  exact hc.2.2.2.2.choose_spec.2.choose

/-- The raw compositor extracted from the full normalized dependency theorem.
Its tensor-generator, inverse-image-pasting, computation-counit and strict-unit equations
fix its maps; this does not select from an unnormalized endpoint-isomorphism existence.
Source: BS 6.8.15; Stacks 0D6D, 099N
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedRawCompositor :
    aE.rawPull ⋙ ahE.rawPull ≅ acE.rawPull := by
  have hc := rationalPullbackCompositionCoherence l E g h sYE sXE sZE aE ahE acE
  unfold HasRationalPullbackCompositionCoherence at hc
  exact hc.2.2.2.2.choose_spec.2.choose_spec.2.choose_spec.2.choose

end GeometricHelpers

section IdentityHelpers
variable (a : RationalRealizationPullbackComparison l E (𝟙 X) sXE sXE)

/-- The ambient identity extracted from the full normalized dependency theorem.
The tensor multiplication, canonical identity fiber product and strict-unit equations
specify this map, including the identity case, before any unit is cancelled.
Source: BS 6.8.15; Stacks 0D6D, 099N
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedGeometricUnitor :
    rationalPullDerived l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _ := by
  have hc := rationalPullbackIdentityCoherence l E sXE a
  unfold HasRationalPullbackIdentityCoherence at hc
  exact hc.2.2.2.choose_spec.2.choose

/-- The raw identity extracted from the full normalized dependency theorem.
The tensor multiplication, canonical identity fiber product and strict-unit equations
specify this map, including the identity case, before any unit is cancelled.
Source: BS 6.8.15; Stacks 0D6D, 099N
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedRawUnitor :
    a.rawPull ≅ 𝟭 _ := by
  have hc := rationalPullbackIdentityCoherence l E sXE a
  unfold HasRationalPullbackIdentityCoherence at hc
  exact hc.2.2.2.choose_spec.2.choose_spec.2.choose_spec.2.choose

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

private theorem mixed_replace_square {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) {U V : C} {W Z P : D} {a a' : U ⟶ V}
    {b b' : T.obj V ⟶ W} {c : W ⟶ Z} {d : T.obj U ⟶ P} {e e' : P ⟶ Z}
    (ha : a = a') (hb : b = b') (he : e = e')
    (h : T.map a' ≫ b' ≫ c = d ≫ e') : T.map a ≫ b ≫ c = d ≫ e := by
  subst a'
  subst b'
  subst e'
  exact h

/-- The same zeta comparisons commute with geometric composition.
Source: BS 6.8.15, pp. 61--62; Stacks 0G7E, 0D6D and 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: precompose with scalar extension of the actual completion units. Substitute
the recorded alpha normalization and rationalScalarCompletionUnitSquare. Adjacent
inverse-unit/unit factors cancel. On the same flat-term K-flat representative all
remaining comparisons are the generator-normalized ordinary tensor maps. Geometric
composition uses the canonical inverse-image compositor and scalar insertion; coefficient
composition multiplies the scalar factors. Their associative product is independent of
parentheses. The normalized derived computation counits descend these maps, and the
annihilating-power fraction criterion extends the equations to raw rational morphisms. -/
theorem rationalMixedGeometricComposition
    (K : DerivedCategory (pbcModules Y (rationalCoefficientSheaf l Y E))) :
    mh.zeta.hom.app ((rationalPullDerived l E g aE.rationalCoefficient).obj K) ≫
        (rationalPullDerived l F h ahF.rationalCoefficient).map (mg.zeta.hom.app K) =
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i Z)).map
          ((rationalMixedGeometricCompositor l E g sXE sYE aE h sZE ahE acE).hom.app K) ≫
        mc.zeta.hom.app K ≫
        (rationalMixedGeometricCompositor l F g sXF sYF aF h sZF ahF acF).inv.app
          ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj K) := by
  sorry

set_option maxHeartbeats 800000 in
-- The normalized compositor witnesses involve large dependent functor types.
/-- The actual strict-beta rationalizations obey the same geometric pasting.
Source: BS 6.8.15, pp. 61--62; Stacks 0G7E, 0D6D and 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: extract the integral compositors and their completion-unit equations from
rationalPullbackCompositionCoherence. Precompose the mixed integral square with
scalar extension of the two completion units. Naturality, the completion-unit
squares and the inverse of pbcScalarOrdinaryPull_comp identify the two routes;
cancel the invertible units. Apply rationalization to this integral square.
The beta normalizations and the raw compositor equations express all maps using
integral representatives. Naturality of beta moves the initial object transport,
and adjacent inverse transports cancel. -/
theorem rationalMixedRawGeometricComposition
    (K : PbcRationalDerivedCategory l E Y Fact.out Fact.out) :
    (pbcRationalScalarExtension l E F i Z Fact.out Fact.out).map
        ((rationalMixedRawCompositor l E g sXE sYE aE h sZE ahE acE).hom.app K) ≫
      mc.beta.hom.app K =
    mh.beta.hom.app (aE.rawPull.obj K) ≫
      ahF.rawPull.map (mg.beta.hom.app K) ≫
      (rationalMixedRawCompositor l F g sXF sYF aF h sZF ahF acF).hom.app
        ((pbcRationalScalarExtension l E F i Y Fact.out Fact.out).obj K) := by
  have hcE := rationalPullbackCompositionCoherence l E g h sYE sXE sZE aE ahE acE
  have hcF := rationalPullbackCompositionCoherence l F g h sYF sXF sZF aF ahF acF
  unfold HasRationalPullbackCompositionCoherence at hcE hcF
  let qE := hcE.2.2.2.2.choose_spec.2.choose_spec.2
  let qF := hcF.2.2.2.2.choose_spec.2.choose_spec.2
  have he := qE.choose_spec.2.choose_spec.1 K.obj
  have hf := qF.choose_spec.2.choose_spec.1
    ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K.obj)
  change (rationalMixedRawCompositor l E g sXE sYE aE h sZE ahE acE).hom.app K = _
    at he
  change (rationalMixedRawCompositor l F g sXF sYF aF h sZF ahF acF).hom.app
    ((pbcRationalScalarExtension l E F i Y Fact.out Fact.out).obj K) = _ at hf
  have hb := congrArg Iso.hom (mg.beta_normalization K)
  have hh := congrArg Iso.hom (mh.beta_normalization
    ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj
      ((aE.integral.completedFunctor l E).obj K.obj)))
  have hc := congrArg Iso.hom (mc.beta_normalization K)
  change mg.beta.hom.app K = _ at hb
  change mh.beta.hom.app _ = _ at hh
  change mc.beta.hom.app K = _ at hc
  let Q := pbcRationalization Z (pbcIntegralDatum l F) (pbcUniformizer l F)
  let βg := ObjectProperty.homMk
    (X := (pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj
      ((aE.integral.completedFunctor l E).obj K.obj))
    (Y := (aF.integral.completedFunctor l F).obj
      ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K.obj))
    ((rationalScalarStrictBeta l E F i g).hom.app K.obj.obj)
  let βc := ObjectProperty.homMk
    (X := (pbcEmbeddingIntegralTensor l E F i Z Fact.out Fact.out).obj
      ((acE.integral.completedFunctor l E).obj K.obj))
    (Y := (acF.integral.completedFunctor l F).obj
      ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K.obj))
    ((rationalScalarStrictBeta l E F i (h ≫ g)).hom.app K.obj.obj)
  let βh := ObjectProperty.homMk
    (X := (pbcEmbeddingIntegralTensor l E F i Z Fact.out Fact.out).obj
      ((ahE.integral.completedFunctor l E).obj
        ((aE.integral.completedFunctor l E).obj K.obj)))
    (Y := (ahF.integral.completedFunctor l F).obj
      ((pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj
        ((aE.integral.completedFunctor l E).obj K.obj)))
    ((rationalScalarStrictBeta l E F i h).hom.app
      ((aE.integral.completedFunctor l E).obj K.obj).obj)
  have hi := rationalMixedIntegralGeometricComposition l E F i g sXE sYE sXF sYF aE aF h sZE sZF
    ahE acE ahF acF qE.choose qF.choose qE.choose_spec.1 qF.choose_spec.1 K.obj
  have hi' :
      (pbcEmbeddingIntegralTensor l E F i Z Fact.out Fact.out).map
          (qE.choose.hom.app K.obj) ≫ βc =
        βh ≫ (ahF.integral.completedFunctor l F).map βg ≫
          qF.choose.hom.app
            ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K.obj) := by
    apply ObjectProperty.hom_ext
    exact hi
  have hQ := congrArg Q.map hi'
  simp only [Functor.map_comp] at hQ
  have hQ' := (congrArg (fun f ↦ f ≫ Q.map βc)
    (mixed_scalar_map l E F i (qE.choose.hom.app K.obj))).trans hQ
  exact mixed_raw_pasting ahE.rawPull ahF.rawPull
    (pbcRationalScalarExtension l E F i X Fact.out Fact.out)
    (pbcRationalScalarExtension l E F i Z Fact.out Fact.out) mh.beta
    (eqToIso (aE.raw_objects K.obj))
    (eqToIso (aF.raw_objects
      ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K.obj)))
    (eqToIso (ahE.raw_objects ((aE.integral.completedFunctor l E).obj K.obj)))
    (eqToIso (acE.raw_objects K.obj))
    (eqToIso (ahF.raw_objects
      ((pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj
        ((aE.integral.completedFunctor l E).obj K.obj))))
    (eqToIso (ahF.raw_objects ((aF.integral.completedFunctor l F).obj
      ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K.obj))))
    (eqToIso (acF.raw_objects
      ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K.obj)))
    _ _ _ _ _ _ _ _ _ _
    (by simpa only [eqToIso.hom, eqToIso.inv, eqToHom_map] using he)
    (by simpa only [eqToIso.hom, eqToIso.inv, eqToHom_map] using hf)
    (by simpa only [rationalMixedBetaComponent, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, eqToIso.hom, eqToIso.inv, ObjectProperty.isoMk, Iso.app_hom, βg] using hb)
    (by simpa only [rationalMixedBetaComponent, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, eqToIso.hom, eqToIso.inv, ObjectProperty.isoMk, Iso.app_hom, βc, Q] using hc)
    (by simpa only [rationalMixedBetaComponent, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, eqToIso.hom, eqToIso.inv, ObjectProperty.isoMk, Iso.app_hom,
      βh, Q, mixed_localization_obj] using hh)
    (mixed_raw_map l F h sZF sXF ahF βg) hQ'

end GeometricCoherence

private def mixed_complexCounit {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    DerivedCategory.Q ⋙ pbcDerivedExtend φ ⟶
      (pbcExtend φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv (pbcDerivedExtend φ) ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ _) (pbcExtensionCounit φ) ≫
    Functor.whiskerRight ((pbcExtend φ).mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerLeft ((pbcExtend φ).mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso _).hom

private def mixed_pullCounit {S T : Scheme.{u}} (f : S ⟶ T)
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E) :
    DerivedCategory.Q ⋙ rationalPullDerived l E f c ⟶
      (rationalPullModule l E f c).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (proEtaleRingDerivedPullbackFactors f (rationalCoefficientSheaf l T E)
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E)) (Iso.refl _)).hom (pbcDerivedExtend c) ≫
    Functor.whiskerLeft ((proEtaleRingModulePullback f (rationalCoefficientSheaf l T E)
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (rationalCoefficientSheaf l T E)) (Iso.refl _)).mapHomologicalComplex (.up ℤ))
      (mixed_complexCounit c)

private theorem mixed_natTrans_transport {C D : Type*} [Category C] [Category D]
    {A B : C ⥤ D} (f g : A ⟶ B) {K L : C} (e : K ≅ L) (h : f.app K = g.app K) :
    f.app L = g.app L := by
  apply (cancel_epi (A.map e.hom)).1
  rw [f.naturality, g.naturality, h]

private theorem mixed_scalar_unit_map {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (c : R ⟶ S)
    {M N : pbcModules W R} (f : M ⟶ N) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcExtend c).map f).val.app U (pbcTensorSection c M U 1 x) =
      pbcTensorSection c N U 1 (f.val.app U x) := by
  have h := congrArg (fun q ↦ q.val.app U x) ((pbcScalarAdjunction c).unit.naturality f)
  change ((pbcScalarAdjunction c).unit.app N).val.app U (f.val.app U x) =
    ((pbcExtend c).map f).val.app U
      (((pbcScalarAdjunction c).unit.app M).val.app U x) at h
  erw [(pbcScalarAdjunction_exists c).exists.choose_spec,
    (pbcScalarAdjunction_exists c).exists.choose_spec] at h
  exact h.symm

private theorem mixed_scalar_unit_restrict {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (c : R ⟶ S)
    (M : pbcModules W R) {U V : W.ProEtᵒᵖ} (f : U ⟶ V) (x : M.val.obj U) :
    ((pbcExtend c).obj M).val.map f (pbcTensorSection c M U 1 x) =
      pbcTensorSection c M V 1 (M.val.map f x) := by
  have h := congrArg (fun q ↦ q x) (((pbcScalarAdjunction c).unit.app M).val.naturality f)
  change ((pbcScalarAdjunction c).unit.app M).val.app V (M.val.map f x) =
    ((pbcExtend c).obj M).val.map f
      (((pbcScalarAdjunction c).unit.app M).val.app U x) at h
  erw [(pbcScalarAdjunction_exists c).exists.choose_spec,
    (pbcScalarAdjunction_exists c).exists.choose_spec] at h
  exact h.symm

private def mixed_identity_module (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (s : RationalModuleRealization l A X)
    (a : RationalRealizationPullbackComparison l A (𝟙 X) s s) :
    rationalPullModule l A (𝟙 X) a.rationalCoefficient ≅ 𝟭 _ := by
  have hc := rationalPullbackIdentityCoherence l A s a
  unfold HasRationalPullbackIdentityCoherence at hc
  exact hc.2.2.2.choose

set_option maxHeartbeats 800000 in
-- Adjunction generators involve nested dependent scalar and inverse-image functors.
private theorem mixed_geometric_identity_ordinary
    (aIE : RationalRealizationPullbackComparison l E (𝟙 X) sXE sXE)
    (aIF : RationalRealizationPullbackComparison l F (𝟙 X) sXF sXF)
    (m : RationalScalarMixedUnitCancellation l E F i (𝟙 X)
      sXE sXE sXF sXF aIE aIF)
    (M : pbcModules X (rationalCoefficientSheaf l X E)) :
    m.ordinary.hom.app M ≫
        (pbcExtend (rationalBalancedCoefficient l E F i X)).map
          ((mixed_identity_module l E sXE aIE).hom.app M) =
      (mixed_identity_module l F sXF aIF).hom.app
        ((pbcExtend (rationalBalancedCoefficient l E F i X)).obj M) := by
  let hcE := rationalPullbackIdentityCoherence l E sXE aIE
  let hcF := rationalPullbackIdentityCoherence l F sXF aIF
  unfold HasRationalPullbackIdentityCoherence at hcE hcF
  let oE := hcE.2.2.2.choose
  let oF := hcF.2.2.2.choose
  have he := hcE.2.2.2.choose_spec.1
  have hf := hcF.2.2.2.choose_spec.1
  let φ := rationalBalancedCoefficient l E F i X
  let R := rationalCoefficientSheaf l X F
  let RI := (proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1}).obj R
  let adj := (pbcScalarAdjunction φ).comp
    ((proEtaleRingModuleAdjunction (𝟙 X) R RI (Iso.refl _)).comp
      (pbcScalarAdjunction aIF.rationalCoefficient))
  apply (adj.homEquiv M ((pbcExtend φ).obj M)).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  obtain ⟨V⟩ := U
  simp only [Adjunction.homEquiv_unit, adj, Adjunction.comp_unit_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  change ((pbcExtend φ).map (oE.hom.app M)).val.app _
      ((m.ordinary.hom.app M).val.app _
        (((pbcScalarAdjunction aIF.rationalCoefficient).unit.app _).val.app _
          (((proEtaleRingModuleAdjunction (𝟙 X) R RI (Iso.refl _)).unit.app _).val.app
            (op V) (((pbcScalarAdjunction φ).unit.app M).val.app (op V) x)))) =
    (oF.hom.app ((pbcExtend φ).obj M)).val.app _
      (((pbcScalarAdjunction aIF.rationalCoefficient).unit.app _).val.app _
        (((proEtaleRingModuleAdjunction (𝟙 X) R RI (Iso.refl _)).unit.app _).val.app
          (op V) (((pbcScalarAdjunction φ).unit.app M).val.app (op V) x)))
  erw [(proEtaleRingModuleAdjunction_normalized (𝟙 X) R RI (Iso.refl _)),
    (pbcScalarAdjunction_exists aIF.rationalCoefficient).exists.choose_spec,
    (pbcScalarAdjunction_exists φ).exists.choose_spec]
  with_unfolding_all
    change ((pbcExtend φ).map (oE.hom.app M)).val.app _
        ((m.ordinary.hom.app M).val.app _
          (rationalCoherenceUnit l F (𝟙 X) aIF.rationalCoefficient
            ((pbcExtend φ).obj M) V (pbcTensorSection φ M (op V) 1 x))) =
      (oF.hom.app ((pbcExtend φ).obj M)).val.app _
        (rationalCoherenceUnit l F (𝟙 X) aIF.rationalCoefficient
          ((pbcExtend φ).obj M) V (pbcTensorSection φ M (op V) 1 x))
  have hm := m.ordinary_units M V x
  with_unfolding_all
    change (m.ordinary.hom.app M).val.app _
        (rationalCoherenceUnit l F (𝟙 X) aIF.rationalCoefficient
          ((pbcExtend φ).obj M) V (pbcTensorSection φ M (op V) 1 x)) =
      pbcTensorSection φ ((rationalPullModule l E (𝟙 X) aIE.rationalCoefficient).obj M)
        _ 1 (rationalCoherenceUnit l E (𝟙 X) aIE.rationalCoefficient M V x) at hm
  rw [hm, mixed_scalar_unit_map]
  have he' := he M V x 1
  have hf' := hf ((pbcExtend φ).obj M) V (pbcTensorSection φ M (op V) 1 x) 1
  simp only [rationalCoherenceSmul, one_smul] at he' hf'
  dsimp only [oE, oF]
  have hE := congrArg
    (fun z ↦ pbcTensorSection φ
      ((𝟭 (X.proEtaleRingModules (rationalCoefficientSheaf l X E))).obj M)
      (op ((proEtaleBaseChange (𝟙 X)).obj V)) 1 z) he'
  with_unfolding_all
    exact hE.trans ((mixed_scalar_unit_restrict φ M
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V).op x).symm.trans
        hf'.symm)

set_option maxHeartbeats 800000 in
-- Adjunction generators involve nested dependent scalar and inverse-image functors.
private theorem mixed_geometric_identity_derived
    (aIE : RationalRealizationPullbackComparison l E (𝟙 X) sXE sXE)
    (aIF : RationalRealizationPullbackComparison l F (𝟙 X) sXF sXF)
    (m : RationalScalarMixedUnitCancellation l E F i (𝟙 X)
      sXE sXE sXF sXF aIE aIF)
    (K : DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) :
    m.zeta.hom.app K ≫ (rationalMixedGeometricUnitor l F sXF aIF).hom.app
        ((pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).obj K) =
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
        ((rationalMixedGeometricUnitor l E sXE aIE).hom.app K) := by
  let hcE := rationalPullbackIdentityCoherence l E sXE aIE
  let hcF := rationalPullbackIdentityCoherence l F sXF aIF
  unfold HasRationalPullbackIdentityCoherence at hcE hcF
  let oE := hcE.2.2.2.choose
  let oF := hcF.2.2.2.choose
  let uE := rationalMixedGeometricUnitor l E sXE aIE
  let uF := rationalMixedGeometricUnitor l F sXF aIF
  have he := hcE.2.2.2.choose_spec.2.choose_spec.1
  have hf := hcF.2.2.2.choose_spec.2.choose_spec.1
  change ∀ P, uE.hom.app _ = _ at he
  change ∀ P, uF.hom.app _ = _ at hf
  let φ := rationalBalancedCoefficient l E F i X
  let D := pbcDerivedExtend φ
  let HE := rationalPullDerived l E (𝟙 X) aIE.rationalCoefficient
  let HEM := rationalPullModule l E (𝟙 X) aIE.rationalCoefficient
  let oEC := NatIso.mapHomologicalComplex oE (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)
  let oFC := NatIso.mapHomologicalComplex oF (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)
  let left : HE ⋙ D ⟶ D := m.zeta.hom ≫ Functor.whiskerLeft D uF.hom
  let right : HE ⋙ D ⟶ D := Functor.whiskerRight uE.hom D
  suffices ht : left = right by exact congrArg (fun t ↦ t.app K) ht
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (pbcModules X (rationalCoefficientSheaf l X E)) (.up ℤ))
  intro P
  obtain ⟨P', q, hp, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := rationalCoefficientSheaf l X E) P
  have := hq
  have ht : left.app (DerivedCategory.Q.obj P') = right.app (DerivedCategory.Q.obj P') := by
    have := pbcExtensionCounit_isIso φ P' hp
    let d := pbcComplexCounit φ P'
    have hd : IsIso d := by unfold d pbcComplexCounit; infer_instance
    have ho : (NatIso.mapHomologicalComplex m.ordinary (.up ℤ)).hom.app P' ≫
        ((pbcExtend φ).mapHomologicalComplex (.up ℤ)).map (oEC.hom.app P') =
      oFC.hom.app (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P') := by
      apply HomologicalComplex.hom_ext
      intro n
      exact mixed_geometric_identity_ordinary l E F i sXE sXF aIE aIF m (P'.X n)
    have hn := (mixed_complexCounit φ).naturality (oEC.hom.app P')
    change D.map (DerivedCategory.Q.map (oEC.hom.app P')) ≫ d =
      pbcComplexCounit φ ((HEM.mapHomologicalComplex (.up ℤ)).obj P') ≫
        DerivedCategory.Q.map
          (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).map (oEC.hom.app P')) at hn
    have hz := congrArg (fun f ↦ f ≫ DerivedCategory.Q.map
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).map (oEC.hom.app P')))
      (m.ambient_normalization P')
    simp only [Category.assoc] at hz
    erw [← hn, ← Functor.map_comp_assoc, ← he P', ← Functor.map_comp, ho, ← hf] at hz
    have hu := uF.hom.naturality d
    simp only [Functor.id_map] at hu
    have hh : m.zeta.inv.app (DerivedCategory.Q.obj P') ≫
        D.map (uE.hom.app (DerivedCategory.Q.obj P')) =
      uF.hom.app (D.obj (DerivedCategory.Q.obj P')) := by
      apply (cancel_mono d).1
      simpa only [Category.assoc] using hz.trans hu
    change m.zeta.hom.app _ ≫ uF.hom.app _ = D.map (uE.hom.app _)
    apply (cancel_epi (m.zeta.inv.app (DerivedCategory.Q.obj P'))).1
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using hh.symm
  exact mixed_natTrans_transport left right (asIso (DerivedCategory.Q.map q)) ht

/-- Identity geometric maps give the ambient tensor unitor and the actual raw unitor.
Source: BS 6.8.15, pp. 61--62; Stacks 0G7E, 0D6D and 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: precompose with scalar extension of the actual completion units. Substitute
the recorded alpha normalization and rationalScalarCompletionUnitSquare. Adjacent
inverse-unit/unit factors cancel. On the same flat-term K-flat representative all
remaining comparisons are the generator-normalized ordinary tensor maps. Geometric
composition uses the canonical inverse-image compositor and scalar insertion; coefficient
composition multiplies the scalar factors. Their associative product is independent of
parentheses. The normalized derived computation counits descend these maps, and the
annihilating-power fraction criterion extends the equations to raw rational morphisms. -/
theorem rationalMixedGeometricIdentity
    (aIE : RationalRealizationPullbackComparison l E (𝟙 X) sXE sXE)
    (aIF : RationalRealizationPullbackComparison l F (𝟙 X) sXF sXF)
    (m : RationalScalarMixedUnitCancellation l E F i (𝟙 X)
      sXE sXE sXF sXF aIE aIF) :
    (∀ K : DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E)),
      m.zeta.hom.app K ≫ (rationalMixedGeometricUnitor l F sXF aIF).hom.app
          ((pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).obj K) =
        (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
          ((rationalMixedGeometricUnitor l E sXE aIE).hom.app K)) ∧
    (∀ K : PbcRationalDerivedCategory l E X Fact.out Fact.out,
      m.beta.hom.app K ≫ (rationalMixedRawUnitor l F sXF aIF).hom.app
          ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).obj K) =
        (pbcRationalScalarExtension l E F i X Fact.out Fact.out).map
          ((rationalMixedRawUnitor l E sXE aIE).hom.app K)) := by
  refine ⟨mixed_geometric_identity_derived l E F i sXE sXF aIE aIF m, ?_⟩
  intro K
  have := ((constructibleRationalHomComparison l F X).2 sXF).2.2
  let D := pbcDerivedExtend (rationalBalancedCoefficient l E F i X)
  let T := pbcRationalScalarExtension l E F i X Fact.out Fact.out
  let θ := rationalBalancedTheta l E F i X sXE sXF
  let uE := rationalMixedGeometricUnitor l E sXE aIE
  let uF := rationalMixedGeometricUnitor l F sXF aIF
  let rE := rationalMixedRawUnitor l E sXE aIE
  let rF := rationalMixedRawUnitor l F sXF aIF
  have he := rationalPullbackIdentityCoherence l E sXE aIE
  have hf := rationalPullbackIdentityCoherence l F sXF aIF
  unfold HasRationalPullbackIdentityCoherence at he hf
  have he' := congr_app he.2.2.2.choose_spec.2.choose_spec.2.choose_spec.2.choose_spec.2 K
  have hf' := congr_app hf.2.2.2.choose_spec.2.choose_spec.2.choose_spec.2.choose_spec.2
    (T.obj K)
  change aIE.alpha.hom.app K ≫ uE.hom.app (sXE.J.obj K) = sXE.J.map (rE.hom.app K)
    at he'
  change aIF.alpha.hom.app (T.obj K) ≫ uF.hom.app (sXF.J.obj (T.obj K)) =
    sXF.J.map (rF.hom.app (T.obj K)) at hf'
  apply sXF.J.map_injective
  apply (cancel_mono (θ.hom.app K)).1
  simp only [Functor.map_comp, Category.assoc]
  have hn := uF.hom.naturality (θ.hom.app K)
  simp only [Functor.id_map] at hn
  have hc := congrArg (fun f ↦ f ≫ uF.hom.app (D.obj (sXE.J.obj K))) (m.compatibility K)
  simp only [Category.assoc] at hc
  erw [mixed_geometric_identity_derived l E F i sXE sXF aIE aIF m] at hc
  erw [← D.map_comp, he'] at hc
  erw [hn, reassoc_of% hf'] at hc
  have ht := θ.hom.naturality (rE.hom.app K)
  simp only [Functor.comp_map] at ht
  exact hc.symm.trans ht.symm

section CoefficientCoherence
variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)
  (sXG : RationalModuleRealization l G X) (sYG : RationalModuleRealization l G Y)
  (aG : RationalRealizationPullbackComparison l G g sXG sYG)
  (mEF : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
  (mFG : RationalScalarMixedUnitCancellation l F G j g sXF sYF sXG sYG aF aG)
  (mEG : RationalScalarMixedUnitCancellation l E G (j.comp i) g
    sXE sYE sXG sYG aE aG)

/-- The same zeta comparisons respect the specified coefficient associators.
Source: BS 6.8.15, pp. 61--62; Stacks 0G7E, 0D6D and 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: precompose with scalar extension of the actual completion units. Substitute
the recorded alpha normalization and rationalScalarCompletionUnitSquare. Adjacent
inverse-unit/unit factors cancel. On the same flat-term K-flat representative all
remaining comparisons are the generator-normalized ordinary tensor maps. Geometric
composition uses the canonical inverse-image compositor and scalar insertion; coefficient
composition multiplies the scalar factors. Their associative product is independent of
parentheses. The normalized derived computation counits descend these maps, and the
annihilating-power fraction criterion extends the equations to raw rational morphisms. -/
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
  sorry

/-- The beta comparisons respect precisely the published raw scalar associators.
Source: BS 6.8.15, pp. 61--62; Stacks 0A0E, 0A0G and 0D6D
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: invert the published reflected coefficient-tower equation. Conjugate it
by the quotient-unit-normalized ambient pullback isomorphisms. Naturality of
those isomorphisms and of the scalar associator cancels the intermediate pair
and proves the tower equation for rationalScalarStrictBeta. The denominator-one
formulas show that both raw scalar extension and raw pullback carry integral
maps to their prescribed integral images, retaining the recorded object transports.
Substitute beta_normalization and the published rational scalar associator. Its
naturality removes the initial raw-object transport; the remaining transports
cancel in pairs. Functoriality of rationalization now takes the strict integral
tower equation to exactly the required raw equation. -/
theorem rationalMixedRawCoefficientTower
    (K : PbcRationalDerivedCategory l E Y Fact.out Fact.out) :
    (pbcRationalScalarExtension l F G j X Fact.out Fact.out).map (mEF.beta.hom.app K) ≫
      mFG.beta.hom.app ((pbcRationalScalarExtension l E F i Y Fact.out Fact.out).obj K) ≫
      aG.rawPull.map ((pbcRationalScalarComp l E F G i j Y Fact.out Fact.out).hom.app K) =
    (pbcRationalScalarComp l E F G i j X Fact.out Fact.out).hom.app (aE.rawPull.obj K) ≫
      mEG.beta.hom.app K := by
  have hbEF := congrArg Iso.hom (mEF.beta_normalization K)
  have hbFG := congrArg Iso.hom (mFG.beta_normalization
    ((pbcRationalScalarExtension l E F i Y Fact.out Fact.out).obj K))
  have hbEG := congrArg Iso.hom (mEG.beta_normalization K)
  change mEF.beta.hom.app K = _ at hbEF
  change mFG.beta.hom.app _ = _ at hbFG
  change mEG.beta.hom.app K = _ at hbEG
  refine mixed_replace_square _ hbEF hbFG hbEG ?_
  simp only [rationalMixedBetaComponent, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, eqToIso.hom, eqToIso.inv, Functor.map_comp, Category.assoc]
  have hn := (pbcRationalScalarComp l E F G i j X Fact.out Fact.out).hom.naturality
    (eqToHom (aE.raw_objects K.obj))
  simp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  congr 1
  simp only [eqToHom_map, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp only [pbcRationalScalarComp, NatIso.ofComponents_hom_app,
    pbcRationalScalarCompComponent, Functor.mapIso_hom, ObjectProperty.isoMk]
  rw [mixed_raw_map]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [mixed_scalar_map]
  simp only [← Category.assoc]
  congr 1
  simp only [← Functor.map_comp]
  congr 1
  apply ObjectProperty.hom_ext
  simpa only [pbcEmbeddingIntegralTensor, RationalPullIntegral.completedFunctor,
    pbcConditionalIntegral, pbcRationalScalarExtension, pbcRationalization,
    ScalarLocalization.localization, ObjectProperty.lift, Functor.comp_obj,
    Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    Iso.app_hom, Category.assoc] using
    rationalMixedIntegralCoefficientTower l E F i g G j K.obj.obj

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

/-- The four-field pentagon and mixed pasting use the same zeta and scalar products.
Source: BS 6.8.15, pp. 61--62; Stacks 0G7E, 0D6D and 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: precompose with scalar extension of the actual completion units. Substitute
the recorded alpha normalization and rationalScalarCompletionUnitSquare. Adjacent
inverse-unit/unit factors cancel. On the same flat-term K-flat representative all
remaining comparisons are the generator-normalized ordinary tensor maps. Geometric
composition uses the canonical inverse-image compositor and scalar insertion; coefficient
composition multiplies the scalar factors. Their associative product is independent of
parentheses. The normalized derived computation counits descend these maps, and the
annihilating-power fraction criterion extends the equations to raw rational morphisms. -/
theorem rationalMixedPentagon
    (K : DerivedCategory (pbcModules Y (rationalCoefficientSheaf l Y E))) :
    (pbcDerivedExtend (rationalBalancedCoefficient l G H k X)).map
        ((pbcReductionNormalization (rationalBalancedCoefficient l E F i X)
          (rationalBalancedCoefficient l F G j X)
          (rationalBalancedCoefficient l E G (j.comp i) X)
          (rationalBalancedCoefficient_comp l E F i X G j)
          ((rationalPullDerived l E g aE.rationalCoefficient).obj K)).hom) ≫
      (pbcReductionNormalization (rationalBalancedCoefficient l E G (j.comp i) X)
        (rationalBalancedCoefficient l G H k X)
        (rationalBalancedCoefficient l E H (k.comp (j.comp i)) X)
        (rationalBalancedCoefficient_comp l E G (j.comp i) X H k)
        ((rationalPullDerived l E g aE.rationalCoefficient).obj K)).hom ≫
      mEH.zeta.hom.app K =
    (pbcReductionNormalization (rationalBalancedCoefficient l F G j X)
      (rationalBalancedCoefficient l G H k X)
      (rationalBalancedCoefficient l F H (k.comp j) X)
      (rationalBalancedCoefficient_comp l F G j X H k)
      ((pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).obj
        ((rationalPullDerived l E g aE.rationalCoefficient).obj K))).hom ≫
      (pbcReductionNormalization (rationalBalancedCoefficient l E F i X)
        (rationalBalancedCoefficient l F H (k.comp j) X)
        (rationalBalancedCoefficient l E H (k.comp (j.comp i)) X)
        (rationalBalancedCoefficient_comp l E F i X H (k.comp j))
        ((rationalPullDerived l E g aE.rationalCoefficient).obj K)).hom ≫
      mEH.zeta.hom.app K := by
  have h := rationalMixedReductionNormalizationAssoc
    (rationalBalancedCoefficient l E F i X) (rationalBalancedCoefficient l F G j X)
    (rationalBalancedCoefficient l G H k X)
    (rationalBalancedCoefficient l E G (j.comp i) X)
    (rationalBalancedCoefficient l F H (k.comp j) X)
    (rationalBalancedCoefficient l E H (k.comp (j.comp i)) X)
    (rationalBalancedCoefficient_comp l E F i X G j)
    (rationalBalancedCoefficient_comp l F G j X H k)
    (rationalBalancedCoefficient_comp l E G (j.comp i) X H k)
    (rationalBalancedCoefficient_comp l E F i X H (k.comp j))
    ((rationalPullDerived l E g aE.rationalCoefficient).obj K)
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ mEH.zeta.hom.app K) h

end Pentagon

/-- Naturality of both equal routes on all raw morphisms, including fractions with torsion.
Source: BS 6.8.15; Stacks 00CO and 0D6D
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: theta, alpha, zeta and the normalized raw beta are natural transformations.
Whiskering and composing their naturality equations proves the two formulas. For
f/t^n use the recorded realization and pullback fraction formulas. Multiplying the
integral equation by the reciprocal denominator yields precisely the same formula.
If a further power kills a numerator difference, its image is invertible on rational
coefficients; multiplying by that reciprocal proves independence without cancelling
any integral torsion. -/
theorem rationalMixedRawNaturality
    (m : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
    {K L : PbcRationalDerivedCategory l E Y Fact.out Fact.out} (f : K ⟶ L) :
    (sXF.J.map ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).map
        (aE.rawPull.map f)) ≫ rationalMixedLeft l E F i g sXE sYE sXF sYF aE aF m L =
      rationalMixedLeft l E F i g sXE sYE sXF sYF aE aF m K ≫
        (rationalPullDerived l F g aF.rationalCoefficient).map
          ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).map (sYE.J.map f))) ∧
    (sXF.J.map ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).map
        (aE.rawPull.map f)) ≫ rationalMixedRight l E F i g sXE sYE sXF sYF aE aF m L =
      rationalMixedRight l E F i g sXE sYE sXF sYF aE aF m K ≫
        (rationalPullDerived l F g aF.rationalCoefficient).map
          ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).map (sYE.J.map f))) := by
  let t := Functor.whiskerLeft aE.rawPull (rationalBalancedTheta l E F i X sXE sXF).hom ≫
    Functor.whiskerRight aE.alpha.hom (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)) ≫
      Functor.whiskerLeft sYE.J m.zeta.hom
  have hleft : sXF.J.map ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).map
        (aE.rawPull.map f)) ≫ rationalMixedLeft l E F i g sXE sYE sXF sYF aE aF m L =
      rationalMixedLeft l E F i g sXE sYE sXF sYF aE aF m K ≫
        (rationalPullDerived l F g aF.rationalCoefficient).map
          ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).map (sYE.J.map f)) := by
    simpa only [t, rationalMixedLeft, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_map] using t.naturality f
  refine ⟨hleft, ?_⟩
  simpa only [rationalMixedLeft, rationalMixedRight, m.compatibility] using hleft

/-- The derived coefficient unitor from the owning node's multiplication-normalized theorem.
Its section formula a tensor m maps to a*m, its derived computation and its raw theta
normalization determine the selected data. No new unit comparison is assumed.
Source: BS 6.8.14(2), 6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedCoefficientUnitor (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]
    (sW : RationalModuleRealization l E W) :
    pbcDerivedExtend (rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) W) ≅ 𝟭 _ :=
  (rationalBalancedIdentity l E W sW).2.choose_spec.choose

private theorem mixed_pull_unit_naturality {S T : Scheme.{u}} (f : S ⟶ T)
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
    {M N : pbcModules T (rationalCoefficientSheaf l T E)} (a : M ⟶ N)
    (V : T.ProEt) (x : M.val.obj (op V)) :
    ((rationalPullModule l E f c).map a).val.app (op ((proEtaleBaseChange f).obj V))
      (rationalCoherenceUnit l E f c M V x) =
    rationalCoherenceUnit l E f c N V (a.val.app (op V) x) := by
  let R := rationalCoefficientSheaf l T E
  let RI := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R
  let b := (proEtaleRingModuleAdjunction f R RI (Iso.refl _)).comp (pbcScalarAdjunction c)
  have hu (M : pbcModules T R) (x : M.val.obj (op V)) :
      (b.unit.app M).val.app (op V) x = rationalCoherenceUnit l E f c M V x := by
    change ((pbcScalarAdjunction c).unit.app
      ((proEtaleRingModulePullback f R RI (Iso.refl _)).obj M)).val.app
      (op ((proEtaleBaseChange f).obj V))
        (((proEtaleRingModuleAdjunction f R RI (Iso.refl _)).unit.app M).val.app
          (op V) x) = _
    erw [(proEtaleRingModuleAdjunction_normalized f R RI (Iso.refl _)) M V x]
    with_unfolding_all exact (pbcScalarAdjunction_exists c).exists.choose_spec _ _ _
  have hn := congrArg (fun t ↦ t.val.app (op V) x) (b.unit.naturality a)
  change (b.unit.app N).val.app (op V) (a.val.app (op V) x) =
    ((rationalPullModule l E f c).map a).val.app (op ((proEtaleBaseChange f).obj V))
      ((b.unit.app M).val.app (op V) x) at hn
  rw [hu, hu] at hn
  exact hn.symm

private theorem mixed_pull_hom_ext {S T : Scheme.{u}} (f : S ⟶ T)
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
    (M : pbcModules T (rationalCoefficientSheaf l T E))
    (N : pbcModules S (rationalCoefficientSheaf l S E))
    (a b : (rationalPullModule l E f c).obj M ⟶ N)
    (h : ∀ (V : T.ProEt) (x : M.val.obj (op V)),
      a.val.app (op ((proEtaleBaseChange f).obj V)) (rationalCoherenceUnit l E f c M V x) =
      b.val.app (op ((proEtaleBaseChange f).obj V)) (rationalCoherenceUnit l E f c M V x)) :
    a = b := by
  let R := rationalCoefficientSheaf l T E
  let RI := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R
  let adj := (proEtaleRingModuleAdjunction f R RI (Iso.refl _)).comp (pbcScalarAdjunction c)
  apply (adj.homEquiv M N).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  obtain ⟨V⟩ := U
  simp only [Adjunction.homEquiv_unit, adj, Adjunction.comp_unit_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  change a.val.app (op ((proEtaleBaseChange f).obj V))
      (((pbcScalarAdjunction c).unit.app
        ((proEtaleRingModulePullback f R RI (Iso.refl _)).obj M)).val.app
        (op ((proEtaleBaseChange f).obj V))
        (((proEtaleRingModuleAdjunction f R RI (Iso.refl _)).unit.app M).val.app
          (op V) x)) =
    b.val.app (op ((proEtaleBaseChange f).obj V))
      (((pbcScalarAdjunction c).unit.app
        ((proEtaleRingModulePullback f R RI (Iso.refl _)).obj M)).val.app
        (op ((proEtaleBaseChange f).obj V))
        (((proEtaleRingModuleAdjunction f R RI (Iso.refl _)).unit.app M).val.app
          (op V) x))
  rw [(proEtaleRingModuleAdjunction_normalized f R RI (Iso.refl _)) M V x]
  erw [(pbcScalarAdjunction_exists c).exists.choose_spec]
  with_unfolding_all exact h V x

private theorem mixed_coefficient_identity_ordinary
    (m : RationalScalarMixedUnitCancellation l E E (AlgHom.id ℚ_[l] E) g
      sXE sYE sXE sYE aE aE)
    (M : pbcModules Y (rationalCoefficientSheaf l Y E)) :
    m.ordinary.hom.app M ≫
        ((rationalBalancedIdentity l E X sXE).2.choose.hom.app
          ((rationalPullModule l E g aE.rationalCoefficient).obj M)) =
      (rationalPullModule l E g aE.rationalCoefficient).map
        ((rationalBalancedIdentity l E Y sYE).2.choose.hom.app M) := by
  let oX := (rationalBalancedIdentity l E X sXE).2.choose
  let oY := (rationalBalancedIdentity l E Y sYE).2.choose
  have hx := (rationalBalancedIdentity l E X sXE).2.choose_spec.choose_spec.1
  have hy := (rationalBalancedIdentity l E Y sYE).2.choose_spec.choose_spec.1
  let H := rationalPullModule l E g aE.rationalCoefficient
  apply (cancel_epi (H.map (oY.inv.app M))).1
  apply mixed_pull_hom_ext l E g aE.rationalCoefficient M _
  intro V x
  have hi : (oY.inv.app M).val.app (op V) x =
      pbcTensorSection (rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) Y)
        M (op V) 1 x := by
    have hh := hy M (op V) 1 x
    simp only [one_smul] at hh
    change (oY.hom.app M).val.app (op V) _ = x at hh
    have hhh := congrArg (fun z ↦ (oY.inv.app M).val.app (op V) z) hh
    simpa only [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app,
      ← SheafOfModules.comp_val, Iso.hom_inv_id_app, SheafOfModules.id_val,
      PresheafOfModules.id_app, ConcreteCategory.id_apply] using hhh.symm
  change (oX.hom.app (H.obj M)).val.app _
      ((m.ordinary.hom.app M).val.app _
        ((H.map (oY.inv.app M)).val.app _ (rationalCoherenceUnit l E g _ M V x))) =
    (H.map (oY.hom.app M)).val.app _
      ((H.map (oY.inv.app M)).val.app _ (rationalCoherenceUnit l E g _ M V x))
  dsimp only [H]
  erw [mixed_pull_unit_naturality l E g aE.rationalCoefficient (oY.inv.app M) V x]
  rw [hi]
  have hm : (m.ordinary.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (rationalCoherenceUnit l E g aE.rationalCoefficient
        ((pbcExtend (rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) Y)).obj M)
        V (pbcTensorSection (rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) Y)
          M (op V) 1 x)) =
      pbcTensorSection (rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) X)
        ((rationalPullModule l E g aE.rationalCoefficient).obj M)
        (op ((proEtaleBaseChange g).obj V)) 1
        (rationalCoherenceUnit l E g aE.rationalCoefficient M V x) := by
    with_unfolding_all exact m.ordinary_units M V x
  rw [hm]
  rw [hx]
  simp only [one_smul]
  erw [mixed_pull_unit_naturality l E g aE.rationalCoefficient (oY.hom.app M)]
  rw [hy]
  simp only [one_smul]
  with_unfolding_all rfl

set_option maxHeartbeats 800000 in
-- The normalization compares large dependent functor types.
private theorem mixed_coefficient_identity_derived
    (m : RationalScalarMixedUnitCancellation l E E (AlgHom.id ℚ_[l] E) g
      sXE sYE sXE sYE aE aE)
    (K : DerivedCategory (pbcModules Y (rationalCoefficientSheaf l Y E))) :
    m.zeta.hom.app K ≫ (rationalPullDerived l E g aE.rationalCoefficient).map
        ((rationalMixedCoefficientUnitor l E Y sYE).hom.app K) =
      (rationalMixedCoefficientUnitor l E X sXE).hom.app
        ((rationalPullDerived l E g aE.rationalCoefficient).obj K) := by
  let φX := rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) X
  let φY := rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) Y
  let H := rationalPullDerived l E g aE.rationalCoefficient
  let HM := rationalPullModule l E g aE.rationalCoefficient
  let DX := pbcDerivedExtend φX
  let DY := pbcDerivedExtend φY
  let oX := (rationalBalancedIdentity l E X sXE).2.choose
  let oY := (rationalBalancedIdentity l E Y sYE).2.choose
  let dX := rationalMixedCoefficientUnitor l E X sXE
  let dY := rationalMixedCoefficientUnitor l E Y sYE
  have hx := (rationalBalancedIdentity l E X sXE).2.choose_spec.choose_spec.2.1
  have hy := (rationalBalancedIdentity l E Y sYE).2.choose_spec.choose_spec.2.1
  let left : H ⋙ DX ⟶ H := m.zeta.hom ≫ Functor.whiskerRight dY.hom H
  let right : H ⋙ DX ⟶ H := Functor.whiskerLeft H dX.hom
  suffices he : left = right by exact congrArg (fun t ↦ t.app K) he
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (pbcModules Y (rationalCoefficientSheaf l Y E)) (.up ℤ))
  intro P
  obtain ⟨P', q, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := rationalCoefficientSheaf l Y E) P
  have := hq
  have hf' (n : ℤ) : SheafOfModules.IsFlatOnSite (J := ProEt.topology Y)
      (R := rationalCoefficientSheaf l Y E) (P'.X n) := by
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (rationalCoefficientSheaf l Y E)
        (P'.X n)).symm (hf n)
  have he : left.app (DerivedCategory.Q.obj P') = right.app (DerivedCategory.Q.obj P') := by
    have := rationalPullComplexCounit_isIso_of_flatTerms l E g aE.rationalCoefficient
      P' hp hf'
    let h := rationalPullComplexCounit l E g aE.rationalCoefficient P'
    have hn := dX.hom.naturality h
    simp only [Functor.id_map] at hn
    have ho : (NatIso.mapHomologicalComplex m.ordinary (.up ℤ)).hom.app P' ≫
        (NatIso.mapHomologicalComplex oX (.up ℤ)).hom.app
          ((HM.mapHomologicalComplex (.up ℤ)).obj P') =
      (HM.mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex oY (.up ℤ)).hom.app P') := by
      apply HomologicalComplex.hom_ext
      intro n
      exact mixed_coefficient_identity_ordinary l E g sXE sYE aE m (P'.X n)
    have hnat := (mixed_pullCounit l E g aE.rationalCoefficient).naturality
      ((NatIso.mapHomologicalComplex oY (.up ℤ)).hom.app P')
    change H.map (DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex oY (.up ℤ)).hom.app P')) ≫ h =
      rationalPullComplexCounit l E g aE.rationalCoefficient
          (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P') ≫
        DerivedCategory.Q.map ((HM.mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex oY (.up ℤ)).hom.app P')) at hnat
    have hz := congrArg (fun z ↦ z ≫ DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex oX (.up ℤ)).hom.app
        ((HM.mapHomologicalComplex (.up ℤ)).obj P'))) (m.ambient_normalization P')
    simp only [Category.assoc] at hz
    rw [← hx] at hz
    erw [hn] at hz
    erw [← Functor.map_comp, ho, ← Category.assoc, ← hnat] at hz
    erw [← Functor.map_comp_assoc, ← hy] at hz
    have hh : m.zeta.inv.app (DerivedCategory.Q.obj P') ≫
        dX.hom.app (H.obj (DerivedCategory.Q.obj P')) =
      H.map (dY.hom.app (DerivedCategory.Q.obj P')) := (cancel_mono h).1 hz
    change m.zeta.hom.app _ ≫ H.map (dY.hom.app _) = dX.hom.app _
    apply (cancel_epi (m.zeta.inv.app (DerivedCategory.Q.obj P'))).1
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using hh.symm
  exact mixed_natTrans_transport left right (asIso (DerivedCategory.Q.map q)) he

/-- Equal coefficient fields give the very same multiplication and raw tensor unitors.
Source: BS 6.8.14(2), 6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: specialize the balanced coefficient map to the identity. Its ordinary tensor
unitor is multiplication, and the derived computation retains this normalization.
On tensor generators both routes remove the same unit factor. Thus zeta has the
first equation. Precompose strict beta by the actual completion unit, apply its
unit equation and cancel that unit. This gives the raw equation after scalar
localization, including the annihilating-power relation. The specified stage
normalization identifies this raw tensor unit with the literal identity functor. -/
theorem rationalMixedCoefficientIdentity
    (m : RationalScalarMixedUnitCancellation l E E (AlgHom.id ℚ_[l] E) g
      sXE sYE sXE sYE aE aE) :
    (∀ K : DerivedCategory (pbcModules Y (rationalCoefficientSheaf l Y E)),
      m.zeta.hom.app K ≫ (rationalPullDerived l E g aE.rationalCoefficient).map
          ((rationalMixedCoefficientUnitor l E Y sYE).hom.app K) =
        (rationalMixedCoefficientUnitor l E X sXE).hom.app
          ((rationalPullDerived l E g aE.rationalCoefficient).obj K)) ∧
    (∀ K : PbcRationalDerivedCategory l E Y Fact.out Fact.out,
      m.beta.hom.app K ≫ aE.rawPull.map
          ((pbcRationalScalarUnit l E Y Fact.out Fact.out).hom.app K) =
        (pbcRationalScalarUnit l E X Fact.out Fact.out).hom.app (aE.rawPull.obj K)) := by
  constructor
  · intro K
    exact mixed_coefficient_identity_derived l E g sXE sYE aE m K
  · intro K
    have := ((constructibleRationalHomComparison l E X).2 sXE).2.2
    let H := rationalPullDerived l E g aE.rationalCoefficient
    let dX := rationalMixedCoefficientUnitor l E X sXE
    let dY := rationalMixedCoefficientUnitor l E Y sYE
    have hx := (rationalBalancedIdentity l E X sXE).2.choose_spec.choose_spec.2.2
    have hy := (rationalBalancedIdentity l E Y sYE).2.choose_spec.choose_spec.2.2
    change ∀ K, _ ≫ dX.hom.app _ = _ at hx
    change ∀ K, _ ≫ dY.hom.app _ = _ at hy
    have hn := aE.alpha.hom.naturality
      ((pbcRationalScalarUnit l E Y Fact.out Fact.out).hom.app K)
    simp only [Functor.comp_map] at hn
    apply sXE.J.map_injective
    simp only [Functor.map_comp]
    apply (cancel_mono (aE.alpha.hom.app K)).1
    simp only [Category.assoc]
    erw [hn]
    erw [← hy K, H.map_comp]
    have hc := congrArg (fun f ↦ f ≫ H.map (dY.hom.app (sYE.J.obj K)))
      (m.compatibility K)
    simp only [Category.assoc] at hc
    erw [← hc]
    erw [mixed_coefficient_identity_derived l E g sXE sYE aE m (sYE.J.obj K)]
    have hnX := dX.hom.naturality (aE.alpha.hom.app K)
    simp only [Functor.id_map] at hnX
    erw [hnX]
    erw [← Category.assoc, hx]


/-- Flatten the common target to F_X tensor over g-inverse B_E,Y of g-inverse K.
Every arrow is an existing normalized comparison; in particular the inverse zeta
and ordinary alpha comparison use the same localized coefficient square.
Source: BS 6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation). -/
def rationalMixedTargetFlatten
    (m : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :=
  (rationalPullDerived l F g aF.rationalCoefficient).map
      ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).map
        (eqToHom (sYE.objects K))) ≫
    m.zeta.inv.app ((pbcDerivedExtend (rationalPullScalar l E sYE)).obj K.obj) ≫
    (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
      (aE.ordinaryComparison.inv.app K.obj) ≫
    (rationalBalancedT l E F i X sXE
      ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj)).hom

/-- After the actual unit precomposition, both maps flatten by s to the same single tensor.
This identifies their common ordinary value, rather than only comparing endpoints.
Source: BS 6.8.15; Stacks 0G7E, 0D6D, 07A4
(blueprint: lem-per-rational-scalar-mixed-unit-cancellation).

Proof: substitute the two precomposition equations. In the target flattening the
recorded object transports, zeta and ordinary alpha cancel with their inverses.
The remaining theta followed by t is s, by the definition of rationalBalancedTheta.
The recorded realization object equation supplies exactly the initial transport.
The balanced tensor-model theorem computes s by multiplying the adjacent coefficient
factors. Its finite-projection coefficient square makes this l' i(b') tensor p on
simultaneous flat-term K-flat models; all maps commute with site restrictions.
The computation counits identify that chain formula in the unbounded derived category. -/
theorem rationalMixedCommonTensor
    (m : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :
    (rationalMixedUnitPrecomposition l E F i g sXE sYE sXF aE K ≫
      rationalMixedLeft l E F i g sXE sYE sXF sYF aE aF m
        ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ≫
      rationalMixedTargetFlatten l E F i g sXE sYE sXF sYF aE aF m K =
      eqToHom (sXF.objects
        ((pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj
          ⟨(pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj,
            aE.integral.ordinary_mem K⟩)) ≫
        (rationalBalancedS l E F i X sXE sXF
          ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj)).hom) ∧
    (rationalMixedUnitPrecomposition l E F i g sXE sYE sXF aE K ≫
      rationalMixedRight l E F i g sXE sYE sXF sYF aE aF m
        ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ≫
      rationalMixedTargetFlatten l E F i g sXE sYE sXF sYF aE aF m K =
      eqToHom (sXF.objects
        ((pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj
          ⟨(pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj,
            aE.integral.ordinary_mem K⟩)) ≫
        (rationalBalancedS l E F i X sXE sXF
          ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj)).hom) := by
  obtain ⟨_, hleft, hright⟩ :=
    rationalMixedUnitPrecomposition_eq l E F i g sXE sYE sXF sYF aE aF m K
  have hcommon : rationalMixedOrdinaryPath l E F i g sXE sYE sXF sYF aE aF m K ≫
      rationalMixedTargetFlatten l E F i g sXE sYE sXF sYF aE aF m K =
      eqToHom (sXF.objects
        ((pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj
          ⟨(pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj,
            aE.integral.ordinary_mem K⟩)) ≫
        (rationalBalancedS l E F i X sXE sXF
          ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj)).hom := by
    unfold rationalMixedOrdinaryPath rationalMixedTargetFlatten
    simp only [Functor.map_comp, Category.assoc]
    have hz := m.zeta.hom.naturality (eqToHom (sYE.objects K))
    simp only [Functor.comp_map] at hz
    rw [← reassoc_of% hz]
    simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
      eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.hom_inv_id_app]
    change (rationalBalancedComponent l E F i X sXE sXF _).hom ≫ _ = _
    dsimp only [rationalBalancedComponent]
    simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
      Functor.mapIso_hom, Category.assoc, ← Functor.map_comp_assoc]
    erw [Category.comp_id, eqToHom_trans, eqToHom_refl,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
    rfl
  constructor
  · rw [← Category.assoc, hleft]
    exact hcommon
  · rw [← Category.assoc, hright]
    exact hcommon

end AlgebraicGeometry.Scheme
