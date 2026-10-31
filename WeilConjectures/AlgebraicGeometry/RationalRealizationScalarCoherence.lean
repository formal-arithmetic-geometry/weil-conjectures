/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalRealizationPullbackComparison
public import WeilConjectures.AlgebraicGeometry.PbcScalarExtension
import WeilConjectures.AlgebraicGeometry.RationalScalarBalancedLocalization
import WeilConjectures.AlgebraicGeometry.RationalPullbackCompositionCoherence
import WeilConjectures.AlgebraicGeometry.RationalScalarMixedUnitCancellation
import WeilConjectures.AlgebraicGeometry.ProEtaleCanonicalAdjunctionUnit
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import WeilConjectures.AlgebraicGeometry.RationalPullbackFlatComputationCounit

/-!
# Finite coefficient extension and mixed rational-realization coherence

Source: Bhatt--Scholze, Lemma 6.8.2, Proposition 6.8.14 and Remark 6.8.15;
Stacks Tags 0G7E, 0D6D, 0A0E and 0A0G
(blueprint: lem-per-rational-realization-scalar-coherence).

The comparisons use the actual raw rationalizations, coefficient inclusions and
strict quotient-tower units. The scalar, tower and mixed records retain the
normalizations that specify the comparisons, rather than just their isomorphism classes.
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

attribute [local irreducible] HasDerivedCategory.standard
  Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime]
variable (E F : Type u) [Field E] [Field F]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
variable (i : E →ₐ[ℚ_[l]] F)
variable (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- Finite-extension balancing with its actual continuous and completed coefficient maps.
The component equation is the identification through `F_X ⊗^L_{B_E,X} K`.
The existing `pbcReductionNormalization` is the adjunction-normalized flattening
on K-flat representatives, with inverse inserting one.
Source: BS 6.8.2, 6.8.14(2), 6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-realization-scalar-coherence). -/
structure RationalRealizationScalarComparison
    (sE : RationalModuleRealization l E X) (sF : RationalModuleRealization l F X) where
  /-- Postcomposition of continuous functions by the field inclusion. -/
  coefficient : rationalCoefficientSheaf l X E ⟶ rationalCoefficientSheaf l X F
  /-- This equation specifies that postcomposition on all sections. -/
  coefficient_normalization : ∀ (U : X.ProEtᵒᵖ)
      (b : (rationalCoefficientSheaf l X E).obj.obj U) (x : U.unop.left),
    rationalCoefficientValue l F X U (coefficient.hom.app U b) x =
      i (rationalCoefficientValue l E X U b x)
  /-- The integral inclusion is the recorded finite-quotient-normalized inclusion. -/
  coefficient_square : pbcScalarCoefficientMap l E F i X ≫ rationalPullScalar l F sF =
    rationalPullScalar l E sE ≫ coefficient
  /-- The required isomorphism, natural on every raw fraction morphism. -/
  theta : pbcRationalScalarExtension l E F i X Fact.out Fact.out ⋙ sF.J ≅
    sE.J ⋙ pbcDerivedExtend coefficient
  /-- Both routes flatten to the same actual single derived tensor on an integral object. -/
  integral_normalization : ∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
    theta.hom.app ((pbcRationalization X (pbcIntegralDatum l E)
        (pbcUniformizer l E)).obj K) ≫
      (pbcDerivedExtend coefficient).map (eqToHom (sE.objects K)) ≫
      (pbcReductionNormalization (rationalPullScalar l E sE) coefficient
        (rationalPullScalar l E sE ≫ coefficient) rfl K.obj).hom =
    eqToHom (sF.objects
        ((pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj K)) ≫
      (pbcReductionNormalization (pbcScalarCoefficientMap l E F i X)
        (rationalPullScalar l F sF) (rationalPullScalar l E sE ≫ coefficient)
        coefficient_square K.obj).hom

private theorem rationalScalarCoefficient_eq
    (sE : RationalModuleRealization l E X) (sF : RationalModuleRealization l F X)
    (b : RationalRealizationScalarComparison l E F i X sE sF) :
    b.coefficient = rationalBalancedCoefficient l E F i X := by
  let := coefficientExtensionNormedField l F
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  ext a : 1
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  change rationalCoefficientValue l F X U (b.coefficient.hom.app U a) x =
    rationalCoefficientValue l F X U
      ((rationalBalancedCoefficient l E F i X).hom.app U a) x
  rw [b.coefficient_normalization, (rationalBalancedCoefficient_sections l E F i X).1]

private theorem rationalScalarComparison_unique
    (sE : RationalModuleRealization l E X) (sF : RationalModuleRealization l F X)
    (b₁ b₂ : RationalRealizationScalarComparison l E F i X sE sF) : b₁ = b₂ := by
  have hc := (rationalScalarCoefficient_eq l E F i X sE sF b₁).trans
    (rationalScalarCoefficient_eq l E F i X sE sF b₂).symm
  cases b₁ with
  | mk c₁ cn₁ cs₁ t₁ n₁ =>
    cases b₂ with
    | mk c₂ cn₂ cs₂ t₂ n₂ =>
      dsimp only at hc
      subst c₂
      have ht : t₁ = t₂ := by
        apply Iso.ext
        apply NatTrans.ext
        funext K
        cases K with
        | mk K =>
          change t₁.hom.app
              ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
            t₂.hom.app
              ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K)
          apply (cancel_mono
            ((pbcDerivedExtend c₁).map (eqToHom (sE.objects K)) ≫
              (pbcReductionNormalization (rationalPullScalar l E sE) c₁
                (rationalPullScalar l E sE ≫ c₁) rfl K.obj).hom)).1
          simpa only [Category.assoc] using (n₁ K).trans (n₂ K).symm
      subst t₂
      rfl

private def rationalScalarCanonical
    (sE : RationalModuleRealization l E X) (sF : RationalModuleRealization l F X) :
    RationalRealizationScalarComparison l E F i X sE sF := by
  refine {
    coefficient := rationalBalancedCoefficient l E F i X
    coefficient_normalization := (rationalBalancedCoefficient_sections l E F i X).1
    coefficient_square := rationalBalancedCoefficient_square l E F i X sE sF
    theta := rationalBalancedTheta l E F i X sE sF
    integral_normalization := ?_ }
  intro K
  simp only [rationalBalancedTheta, NatIso.ofComponents_hom_app,
    rationalBalancedComponent, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    eqToIso.hom, eqToIso.inv, rationalBalancedS, rationalBalancedT]
  simp only [Category.assoc]
  change eqToHom (sF.objects
      ((pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj K)) ≫
      (rationalBalancedS l E F i X sE sF K.obj).hom ≫
      (rationalBalancedT l E F i X sE K.obj).inv ≫
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
        (eqToHom (sE.objects K).symm) ≫
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
        (eqToHom (sE.objects K)) ≫
      (rationalBalancedT l E F i X sE K.obj).hom = _
  rw [← Functor.map_comp_assoc, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Finite extension commutes with the raw rational realization.
Source: BS 6.8.2, 6.8.14(2), 6.8.15
(blueprint: lem-per-rational-realization-scalar-coherence).

Proof (node steps 1--3): finite quotient projections define the integral coefficient
inclusion and its square with the continuous coefficient inclusion, by
lem-weil-pbc-continuous-coefficient-realizations. Localize that square. Apply the
normalized K-flat composition maps of lem-sfb-ringed-derived-monoidal-comparisons
to the two factorizations through F_X tensor over B_E,X. They flatten the two
scalar factors to their product, with inverse inserting one. Their quotient is theta.
Use prop-weil-pbc-scalar-extension for the actual integral representative. Naturality
on integral derived maps extends to f/varpi^n by the fraction formula of
lem-per-rational-module-realization-functor: multiply by the inverse image of varpi^n.
The common-denominator annihilating-power criterion proves independence of fractions.
All nonzero E-scalars have their constant reciprocal in F_X. -/
theorem rationalRealizationScalarCoherence
    (sE : RationalModuleRealization l E X) (sF : RationalModuleRealization l F X) :
    Nonempty (RationalRealizationScalarComparison l E F i X sE sF) := by
  exact ⟨rationalScalarCanonical l E F i X sE sF⟩

variable {X}
variable {Y : Scheme.{u}} [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- Transport of the specified scalar/completed-pull comparison to the strict tower.
Only the published unit-compatible strict/intrinsic comparisons are used.
Source: BS 6.8.15; Stacks 0A0E, 0A0G
(blueprint: lem-per-rational-realization-scalar-coherence). -/
def rationalScalarStrictPullComparison (g : X ⟶ Y)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :
    (pbcActualStrictCompletedPull (pbcIntegralDatum l F) g).obj
        ((pbcEmbeddingAmbientTensor l E F i Y).obj K.obj) ≅
      (pbcEmbeddingAmbientTensor l E F i X).obj
        ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K.obj) :=
  (pbcActualCompletedPullback_tower (pbcIntegralDatum l F) g).exists.choose.app
      ⟨(pbcEmbeddingAmbientTensor l E F i Y).obj K.obj,
        (pbcEmbeddingAmbientTensor_preserves l E F i Y Fact.out Fact.out K).1⟩ ≪≫
    (pbcScalarCompletedPullIso l E F i g).app K.obj ≪≫
    (pbcEmbeddingAmbientTensor l E F i X).mapIso
      ((pbcActualCompletedPullback_tower (pbcIntegralDatum l E) g).exists.choose.app
        ⟨K.obj, K.property.1⟩).symm

private theorem rationalScalarAmbientTower_app
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {S T : Scheme.{u}} (g : S ⟶ T)
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete T d)) :
    (pbcActualAmbientCompletedPullbackIso d g).app K.obj =
      (pbcActualCompletedPullback_tower d g).exists.choose.app K := by
  have he : Functor.isoWhiskerLeft
      (ObjectProperty.ι (PbcIsIntrinsicallyComplete T d))
      (pbcActualAmbientCompletedPullbackIso d g) =
        (pbcActualCompletedPullback_tower d g).exists.choose := by
    apply (pbcActualCompletedPullback_tower d g).unique
    · intro N
      exact (pbcActualAmbientCompletedPullback_tower d g).exists.choose_spec N.obj
    · exact (pbcActualCompletedPullback_tower d g).exists.choose_spec
  exact congrArg (fun e ↦ e.app K) he

set_option linter.unusedSectionVars false in
private theorem rationalScalarStrictComparison_eq (g : X ⟶ Y)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :
    (rationalScalarStrictBeta l E F i g).inv.app K.obj =
      (rationalScalarStrictPullComparison l E F i g K).hom := by
  have hE := rationalScalarAmbientTower_app (pbcIntegralDatum l E) g
    ⟨K.obj, K.property.1⟩
  have hF := rationalScalarAmbientTower_app (pbcIntegralDatum l F) g
    ⟨(pbcEmbeddingAmbientTensor l E F i Y).obj K.obj,
      (pbcEmbeddingAmbientTensor_preserves l E F i Y Fact.out Fact.out K).1⟩
  simp only [rationalScalarStrictBeta, Iso.trans_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Iso.symm_inv, rationalScalarReflectedBeta,
    ← Iso.app_inv, ← Iso.app_hom, hE, hF, rationalScalarStrictPullComparison,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]

private theorem rationalScalarStrictComparison_units (g : X ⟶ Y)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :
    (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l F) g).app
        ((pbcEmbeddingAmbientTensor l E F i Y).obj K.obj) ≫
      (rationalScalarStrictPullComparison l E F i g K).hom =
    (pbcScalarOrdinaryPullIso l E F i g).hom.app K.obj ≫
      (pbcEmbeddingAmbientTensor l E F i X).map
        ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj) := by
  rw [← rationalScalarStrictComparison_eq l E F i g K]
  apply (cancel_mono ((rationalScalarStrictBeta l E F i g).hom.app K.obj)).1
  rw [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [Category.assoc, (rationalScalarCompletionUnitSquare l E F i g K.obj).1]
  simp only [rationalScalarOrdinaryBeta, Iso.symm_hom, ← Category.assoc,
    Iso.hom_inv_id_app]
  erw [Category.id_comp]

/-- The mixed square for the specific alpha and the specified scalar/pullback comparison.
The ordinary comparison is fixed on tensor units and on derived computation counits;
its section formula determines the balanced map, including all coefficient factors.
Source: BS 6.8.15; Stacks 0D6D, 0A0E and 0A0G
(blueprint: lem-per-rational-realization-scalar-coherence). -/
structure RationalRealizationScalarMixed (g : X ⟶ Y)
    (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
    (sXF : RationalModuleRealization l F X) (sYF : RationalModuleRealization l F Y)
    (aE : RationalRealizationPullbackComparison l E g sXE sYE)
    (aF : RationalRealizationPullbackComparison l F g sXF sYF)
    (bX : RationalRealizationScalarComparison l E F i X sXE sXF)
    (bY : RationalRealizationScalarComparison l E F i Y sYE sYF) where
  /-- The localized finite-quotient coefficient square. -/
  coefficient_square : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
      bY.coefficient ≫ aF.rationalCoefficient = aE.rationalCoefficient ≫ bX.coefficient
  /-- The ordinary scalar/pullback comparison. -/
  ordinary : pbcExtend bY.coefficient ⋙ rationalPullModule l F g aF.rationalCoefficient ≅
    rationalPullModule l E g aE.rationalCoefficient ⋙ pbcExtend bX.coefficient
  /-- Inserting tensor units gives the same pulled-back generator on both sides.
  Scalar linearity then gives l' tensor b' tensor k ↦ l'b' tensor g⁻¹k. -/
  ordinary_units : ∀ (M : pbcModules Y (rationalCoefficientSheaf l Y E))
      (V : Y.ProEt) (m : M.val.obj (op V)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (pbcTensorSection aF.rationalCoefficient
        ((proEtaleRingModulePullback g (rationalCoefficientSheaf l Y F)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y F)) (Iso.refl _)).obj
              ((pbcExtend bY.coefficient).obj M))
        (op ((proEtaleBaseChange g).obj V)) 1
        (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l Y F)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y F)) (Iso.refl _)
          ((pbcExtend bY.coefficient).obj M) V
          (pbcTensorSection bY.coefficient M (op V) 1 m))) =
    pbcTensorSection bX.coefficient
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
  ambient : pbcDerivedExtend bY.coefficient ⋙ rationalPullDerived l F g aF.rationalCoefficient ≅
    rationalPullDerived l E g aE.rationalCoefficient ⋙ pbcDerivedExtend bX.coefficient
  /-- The ordinary balanced map is the computation of that derived comparison. -/
  ambient_normalization : ∀ P : CochainComplex
      (pbcModules Y (rationalCoefficientSheaf l Y E)) ℤ,
    ambient.hom.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedExtend bX.coefficient).map
          (rationalPullComplexCounit l E g aE.rationalCoefficient P) ≫
        pbcComplexCounit bX.coefficient
          (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex
            (.up ℤ)).obj P) =
      (rationalPullDerived l F g aF.rationalCoefficient).map
          (pbcComplexCounit bY.coefficient P) ≫
        rationalPullComplexCounit l F g aF.rationalCoefficient
          (((pbcExtend bY.coefficient).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)
  /-- The actual completed comparison retains the strict quotient-tower completion units. -/
  completion_units : ∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
    (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l F) g).app
        ((pbcEmbeddingAmbientTensor l E F i Y).obj K.obj) ≫
      (rationalScalarStrictPullComparison l E F i g K).hom =
    (pbcScalarOrdinaryPullIso l E F i g).hom.app K.obj ≫
      (pbcEmbeddingAmbientTensor l E F i X).map
        ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj)
  /-- Descent of precisely this strict-tower scalar/pullback comparison. -/
  raw : pbcRationalScalarExtension l E F i Y Fact.out Fact.out ⋙ aF.rawPull ≅
    aE.rawPull ⋙ pbcRationalScalarExtension l E F i X Fact.out Fact.out
  /-- Integral component normalization, with only the published object transports. -/
  raw_normalization : ∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
    raw.hom.app ((pbcRationalization Y (pbcIntegralDatum l E)
        (pbcUniformizer l E)).obj K) =
      eqToHom (aF.raw_objects
        ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K)) ≫
      (pbcRationalization X (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        (ObjectProperty.homMk
          (X := (aF.integral.completedFunctor l F).obj
            ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K))
          (Y := (pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj
            ((aE.integral.completedFunctor l E).obj K))
          ((rationalScalarStrictPullComparison l E F i g K).hom)) ≫
      (pbcRationalScalarExtension l E F i X Fact.out Fact.out).map
        (eqToHom (aE.raw_objects K).symm)
  /-- The mixed square for the specific alpha_g, on every raw rational object and arrow. -/
  compatibility : ∀ K,
    sXF.J.map (raw.hom.app K) ≫ bX.theta.hom.app (aE.rawPull.obj K) ≫
        (pbcDerivedExtend bX.coefficient).map (aE.alpha.hom.app K) =
      aF.alpha.hom.app
          ((pbcRationalScalarExtension l E F i Y Fact.out Fact.out).obj K) ≫
        (rationalPullDerived l F g aF.rationalCoefficient).map (bY.theta.hom.app K) ≫
        ambient.hom.app (sYE.J.obj K)

/-- The mixed square retains the specified alpha, scalar comparison and completion units.
Source: BS 6.8.15; Stacks 0D6D, 0A0E and 0A0G
(blueprint: lem-per-rational-realization-scalar-coherence).

Proof (node steps 5--8): use lem-weil-finite-free-completed-scalar-comparison and
lem-weil-pbc-finite-free-completion-transport to commute scalar tensor with the
completion reflectors, retaining their unit equation. Arbitrary ramification is
allowed: varpi_E is a unit times a positive power of varpi_F. Identify these units
with the strict quotient-tower units by lem-weil-pbc-constant-completion-equivalence.
Apply lem-weil-pbc-reflected-adjunction-coefficient-squares and
lem-weil-pbc-ringed-pushforward-completion to the ordinary scalar/pullback square.
It gives precisely pbcScalarCompletedPullIso with its completion-unit equation.
Transport through the published strict/intrinsic comparisons. The integral
preservation in lem-per-rational-realization-pullback-comparison permits restriction
and the raw fraction formula permits rationalization. Precompose the two mixed
routes by scalar extension of the specified invertible pullback unit. Its unit
square and alpha_normalization cancel both completion units. The remaining maps
on K-flat representatives both send l' tensor b' tensor p to l'b' tensor g inverse p.
Use lem-weil-pbc-localization-inverse-image-coherence for the same localization
unit on both routes, then cancel the invertible precomposition. -/
theorem rationalRealizationScalarMixed (g : X ⟶ Y)
    (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
    (sXF : RationalModuleRealization l F X) (sYF : RationalModuleRealization l F Y)
    (aE : RationalRealizationPullbackComparison l E g sXE sYE)
    (aF : RationalRealizationPullbackComparison l F g sXF sYF)
    (bX : RationalRealizationScalarComparison l E F i X sXE sXF)
    (bY : RationalRealizationScalarComparison l E F i Y sYE sYF) :
    Nonempty (RationalRealizationScalarMixed l E F i g sXE sYE sXF sYF aE aF bX bY) := by
  rw [rationalScalarComparison_unique l E F i X sXE sXF bX
    (rationalScalarCanonical l E F i X sXE sXF),
    rationalScalarComparison_unique l E F i Y sYE sYF bY
      (rationalScalarCanonical l E F i Y sYE sYF)]
  obtain ⟨m⟩ := rationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF
  refine ⟨{
    coefficient_square := m.coefficient_square
    ordinary := m.ordinary
    ordinary_units := m.ordinary_units
    ambient := m.zeta.symm
    ambient_normalization := m.ambient_normalization
    completion_units := rationalScalarStrictComparison_units l E F i g
    raw := m.beta.symm
    raw_normalization := ?_
    compatibility := ?_ }⟩
  · intro K
    have hi := congrArg Iso.inv
      (m.beta_normalization ((pbcRationalization Y (pbcIntegralDatum l E)
        (pbcUniformizer l E)).obj K))
    simp only [Iso.app_inv, rationalMixedBetaComponent, Iso.trans_inv,
      Functor.mapIso_inv, Iso.symm_inv, eqToIso.hom, eqToIso.inv,
      ObjectProperty.isoMk_inv, eqToHom_map] at hi
    change m.beta.inv.app _ =
      (eqToHom (aF.raw_objects
        ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K)) ≫
        (pbcRationalization X (pbcIntegralDatum l F) (pbcUniformizer l F)).map
          (ObjectProperty.homMk
            (X := (aF.integral.completedFunctor l F).obj
              ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K))
            (Y := (pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj
              ((aE.integral.completedFunctor l E).obj K))
            ((rationalScalarStrictBeta l E F i g).inv.app K.obj))) ≫
        eqToHom (congrArg
          (pbcRationalScalarExtension l E F i X Fact.out Fact.out).obj
          (aE.raw_objects K)).symm at hi
    erw [rationalScalarStrictComparison_eq l E F i g K] at hi
    simp only [eqToHom_map, Category.assoc] at hi ⊢
    exact hi
  · intro K
    have hn := m.compatibility K
    change sXF.J.map (m.beta.inv.app K) ≫
      (rationalBalancedTheta l E F i X sXE sXF).hom.app (aE.rawPull.obj K) ≫
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
        (aE.alpha.hom.app K) =
      aF.alpha.hom.app _ ≫
        (rationalPullDerived l F g aF.rationalCoefficient).map
          ((rationalBalancedTheta l E F i Y sYE sYF).hom.app K) ≫
        m.zeta.inv.app (sYE.J.obj K)
    apply (cancel_epi (sXF.J.map (m.beta.hom.app K))).1
    apply (cancel_mono (m.zeta.hom.app (sYE.J.obj K))).1
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    exact hn

private theorem rationalScalarReverseSquare
    {C : Type*} [Category C] {A B P Q : C}
    (a : A ≅ B) (b : P ≅ Q) (f : B ⟶ Q) (g : A ⟶ P)
    (h : a.hom ≫ f = g ≫ b.hom) : f ≫ b.inv = a.inv ≫ g := by
  apply (cancel_epi a.hom).1
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [Iso.hom_inv_id_assoc]

private def rationalScalarMixedToCancellation (g : X ⟶ Y)
    (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
    (sXF : RationalModuleRealization l F X) (sYF : RationalModuleRealization l F Y)
    (aE : RationalRealizationPullbackComparison l E g sXE sYE)
    (aF : RationalRealizationPullbackComparison l F g sXF sYF)
    (m : RationalRealizationScalarMixed l E F i g sXE sYE sXF sYF aE aF
      (rationalScalarCanonical l E F i X sXE sXF)
      (rationalScalarCanonical l E F i Y sYE sYF)) :
    RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF := by
  refine {
    coefficient_square := m.coefficient_square
    ordinary := m.ordinary
    ordinary_units := m.ordinary_units
    zeta := m.ambient.symm
    ambient_normalization := m.ambient_normalization
    beta := m.raw.symm
    beta_normalization := ?_
    compatibility := ?_ }
  · intro K
    have he : m.raw.app K =
        (rationalMixedBetaComponent l E F i g sXE sYE sXF sYF aE aF K).symm := by
      apply Iso.ext
      have hn := m.raw_normalization K.obj
      simp only [Iso.app_hom, Iso.symm_hom, rationalMixedBetaComponent,
        Iso.trans_inv, Functor.mapIso_inv, eqToIso.inv, eqToIso.hom, Iso.symm_inv,
        ObjectProperty.isoMk_inv, Iso.app_inv, eqToHom_map, Category.assoc] at hn ⊢
      erw [rationalScalarStrictComparison_eq l E F i g K.obj]
      exact hn
    have hi := congrArg Iso.symm he
    simp only [Iso.symm_symm_eq] at hi
    exact hi
  · intro K
    have hn := m.compatibility K
    have hs := rationalScalarReverseSquare (sXF.J.mapIso (m.raw.app K))
      (m.ambient.app (sYE.J.obj K))
      ((rationalBalancedTheta l E F i X sXE sXF).hom.app (aE.rawPull.obj K) ≫
        (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map (aE.alpha.hom.app K))
      (aF.alpha.hom.app _ ≫ (rationalPullDerived l F g aF.rationalCoefficient).map
        ((rationalBalancedTheta l E F i Y sYE sYF).hom.app K))
      (by simpa only [Functor.mapIso_hom, Iso.app_hom, rationalScalarCanonical,
        Category.assoc] using hn)
    simp only [Functor.mapIso_inv, Iso.app_inv, Category.assoc] at hs ⊢
    exact hs


variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
variable (j : F →ₐ[ℚ_[l]] G)

/-- The successive-extension diagram with exactly the published raw tensor associators.
Source: BS 6.8.14--6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-realization-scalar-coherence). -/
structure RationalRealizationScalarTower
    (sE : RationalModuleRealization l E X) (sF : RationalModuleRealization l F X)
    (sG : RationalModuleRealization l G X)
    (bEF : RationalRealizationScalarComparison l E F i X sE sF)
    (bFG : RationalRealizationScalarComparison l F G j X sF sG)
    (bEG : RationalRealizationScalarComparison l E G (j.comp i) X sE sG) : Prop where
  /-- The continuous coefficient maps compose as the field inclusions. -/
  coefficient : bEF.coefficient ≫ bFG.coefficient = bEG.coefficient
  /-- Flattening the two scalar factors agrees with direct extension. -/
  compatibility : ∀ K,
    sG.J.map ((pbcRationalScalarComp l E F G i j X Fact.out Fact.out).hom.app K) ≫
        bEG.theta.hom.app K =
      bFG.theta.hom.app
          ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).obj K) ≫
        (pbcDerivedExtend bFG.coefficient).map (bEF.theta.hom.app K) ≫
        (pbcReductionNormalization bEF.coefficient bFG.coefficient bEG.coefficient
          coefficient (sE.J.obj K)).hom

/-- The successive-extension comparison is coherent, including repeated fields.
Source: BS 6.8.14--6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-realization-scalar-coherence).

Proof (node steps 4 and 9): substitute integral_normalization for the three theta
components. The intermediate inverse balancing maps cancel. On a common flat-term
K-flat representative the two remaining maps multiply m tensor l tensor p to ml tensor p.
The ringed derived monoidal composition comparison identifies the derived maps;
prop-weil-pbc-scalar-extension supplies precisely the displayed raw associator.
Its fraction formula and invertibility of all denominators descend the equation
to every raw object and arrow. -/
theorem rationalRealizationScalarTower
    (sE : RationalModuleRealization l E X) (sF : RationalModuleRealization l F X)
    (sG : RationalModuleRealization l G X)
    (bEF : RationalRealizationScalarComparison l E F i X sE sF)
    (bFG : RationalRealizationScalarComparison l F G j X sF sG)
    (bEG : RationalRealizationScalarComparison l E G (j.comp i) X sE sG) :
    RationalRealizationScalarTower l E F i G j sE sF sG bEF bFG bEG := by
  rw [rationalScalarComparison_unique l E F i X sE sF bEF
    (rationalScalarCanonical l E F i X sE sF),
    rationalScalarComparison_unique l F G j X sF sG bFG
      (rationalScalarCanonical l F G j X sF sG),
    rationalScalarComparison_unique l E G (j.comp i) X sE sG bEG
      (rationalScalarCanonical l E G (j.comp i) X sE sG)]
  exact ⟨rationalBalancedCoefficient_comp l E F i X G j,
    rationalBalancedTower l E F i X sE sF G j sG⟩

/-- Tensor multiplication is the identity-field comparison, on ordinary modules,
complexes, derived objects and raw rationalizations.
Source: BS 6.8.14--6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-realization-scalar-coherence). -/
structure RationalRealizationScalarUnit (s : RationalModuleRealization l E X)
    (b : RationalRealizationScalarComparison l E E (AlgHom.id ℚ_[l] E) X s s) where
  /-- Identity field inclusion induces the identity continuous coefficient map. -/
  coefficient : b.coefficient = 𝟙 _
  /-- The ordinary multiplication unitor. -/
  ordinary : pbcExtend b.coefficient ≅ 𝟭 _
  /-- It multiplies the coefficient into the module section. -/
  sections : ∀ (M : pbcModules X (rationalCoefficientSheaf l X E))
      (U : X.ProEtᵒᵖ) (a : (rationalCoefficientSheaf l X E).obj.obj U) (m : M.val.obj U),
    (ordinary.hom.app M).val.app U (pbcTensorSection b.coefficient M U a m) = a • m
  /-- The corresponding derived unitor. -/
  ambient : pbcDerivedExtend b.coefficient ≅ 𝟭 _
  /-- Its computation is that ordinary multiplication, degree by degree. -/
  normalization : ∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
    ambient.hom.app (DerivedCategory.Q.obj P) =
      pbcComplexCounit b.coefficient P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)
  /-- Theta for the identity is exactly the specified raw tensor unitor. -/
  compatibility : ∀ K,
    b.theta.hom.app K ≫ ambient.hom.app (s.J.obj K) =
      s.J.map ((pbcRationalScalarUnit l E X Fact.out Fact.out).hom.app K)

/-- Identity coefficients give the multiplication unitors.
Source: BS 6.8.14--6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-realization-scalar-coherence).

Proof (node step 4): the normalized continuous map is the identity. The tensor unit
and derived comparison are multiplication, characterized by a tensor m ↦ a m.
Substitute integral_normalization. Both sides then remove the same unit tensor
factor, since 1a = a = a1. The raw tensor unit of prop-weil-pbc-scalar-extension is
its specified localization; naturality extends the equality to fraction morphisms. -/
theorem rationalRealizationScalarUnit (s : RationalModuleRealization l E X)
    (b : RationalRealizationScalarComparison l E E (AlgHom.id ℚ_[l] E) X s s) :
    Nonempty (RationalRealizationScalarUnit l E s b) := by
  rw [rationalScalarComparison_unique l E E (AlgHom.id ℚ_[l] E) X s s b
    (rationalScalarCanonical l E E (AlgHom.id ℚ_[l] E) X s s)]
  obtain ⟨hc, o, d, hs, hn, ht⟩ := rationalBalancedIdentity l E X s
  exact ⟨⟨hc, o, hs, d, hn, ht⟩⟩

private def rationalScalarNormalizationIso {T : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c) :
    pbcDerivedExtend a ⋙ pbcDerivedExtend b ≅ pbcDerivedExtend c :=
  Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
    (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction c)
    (pbcDerivedRestrictComp a b c h)

private theorem rationalScalarNormalizationIso_hom {T : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c)
    (K : DerivedCategory (pbcModules T R)) :
    (rationalScalarNormalizationIso a b c h).hom.app K =
      (pbcReductionNormalization a b c h K).hom := by
  dsimp only [rationalScalarNormalizationIso, pbcReductionNormalization, asIso_hom,
    pbcReductionNormalizationHom, pbcReductionTransition]
  simp only [Adjunction.leftAdjointCompIso_hom_app, Adjunction.homEquiv_counit,
    Functor.map_comp, Category.assoc]

private theorem rationalScalarNatTrans_transport
    {C D : Type*} [Category C] [Category D] {A B : C ⥤ D}
    (f g : A ⟶ B) {K L : C} (e : K ≅ L) (h : f.app K = g.app K) :
    f.app L = g.app L := by
  apply (cancel_epi (A.map e.hom)).1
  rw [f.naturality, g.naturality, h]

/-- Both four-field routes multiply the same three coefficient factors. The first
formula is the ambient balanced pentagon, and the second retains the specified raw
associators followed by theta. Repeated fields are permitted in both formulas.
Source: BS 6.8.14--6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-realization-scalar-coherence).

Proof (node steps 4 and 9): resolve the input by a flat-term K-flat complex.
The two ambient paths send n tensor m tensor l tensor p to nml tensor p.
Associativity proves equality of chain maps, and the normalized monoidal comparisons
of lem-sfb-ringed-derived-monoidal-comparisons give the derived equation.
The actual raw associators of prop-weil-pbc-scalar-extension are these balancing maps
localized and hence satisfy the same pentagon. Apply J and append theta. Fraction
naturality follows by multiplying the integral equations by their invertible scalars.
For repeated fields the same argument removes units, without excluding identity cases. -/
theorem rationalRealizationScalarPentagon
    (H : Type u) [Field H] [Algebra ℚ_[l] H] [FiniteDimensional ℚ_[l] H]
    (k : G →ₐ[ℚ_[l]] H)
    (sE : RationalModuleRealization l E X) (sF : RationalModuleRealization l F X)
    (sG : RationalModuleRealization l G X) (sH : RationalModuleRealization l H X)
    (bEF : RationalRealizationScalarComparison l E F i X sE sF)
    (bFG : RationalRealizationScalarComparison l F G j X sF sG)
    (bGH : RationalRealizationScalarComparison l G H k X sG sH)
    (bEG : RationalRealizationScalarComparison l E G (j.comp i) X sE sG)
    (bFH : RationalRealizationScalarComparison l F H (k.comp j) X sF sH)
    (bEH : RationalRealizationScalarComparison l E H (k.comp (j.comp i)) X sE sH)
    (tEFG : RationalRealizationScalarTower l E F i G j sE sF sG bEF bFG bEG)
    (tFGH : RationalRealizationScalarTower l F G j H k sF sG sH bFG bGH bFH)
    (tEGH : RationalRealizationScalarTower l E G (j.comp i) H k sE sG sH bEG bGH bEH)
    (tEFH : RationalRealizationScalarTower l E F i H (k.comp j) sE sF sH bEF bFH bEH) :
    (∀ K : DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E)),
      (pbcDerivedExtend bGH.coefficient).map
          (pbcReductionNormalization bEF.coefficient bFG.coefficient bEG.coefficient
            tEFG.coefficient K).hom ≫
        (pbcReductionNormalization bEG.coefficient bGH.coefficient bEH.coefficient
          tEGH.coefficient K).hom =
      (pbcReductionNormalization bFG.coefficient bGH.coefficient bFH.coefficient
        tFGH.coefficient ((pbcDerivedExtend bEF.coefficient).obj K)).hom ≫
        (pbcReductionNormalization bEF.coefficient bFH.coefficient bEH.coefficient
          tEFH.coefficient K).hom) ∧
    (∀ K : PbcRationalCategory X (pbcIntegralDatum l E) (pbcUniformizer l E),
      sH.J.map ((pbcRationalScalarExtension l G H k X Fact.out Fact.out).map
          ((pbcRationalScalarComp l E F G i j X Fact.out Fact.out).hom.app K)) ≫
        sH.J.map ((pbcRationalScalarComp l E G H (j.comp i) k X
          Fact.out Fact.out).hom.app K) ≫ bEH.theta.hom.app K =
      sH.J.map ((pbcRationalScalarComp l F G H j k X Fact.out Fact.out).hom.app
          ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).obj K)) ≫
        sH.J.map ((pbcRationalScalarComp l E F H i (k.comp j) X
          Fact.out Fact.out).hom.app K) ≫ bEH.theta.hom.app K) := by
  have hEF := rationalScalarComparison_unique l E F i X sE sF bEF
    (rationalScalarCanonical l E F i X sE sF)
  have hFG := rationalScalarComparison_unique l F G j X sF sG bFG
    (rationalScalarCanonical l F G j X sF sG)
  have hGH := rationalScalarComparison_unique l G H k X sG sH bGH
    (rationalScalarCanonical l G H k X sG sH)
  have hEG := rationalScalarComparison_unique l E G (j.comp i) X sE sG bEG
    (rationalScalarCanonical l E G (j.comp i) X sE sG)
  have hFH := rationalScalarComparison_unique l F H (k.comp j) X sF sH bFH
    (rationalScalarCanonical l F H (k.comp j) X sF sH)
  have hEH := rationalScalarComparison_unique l E H (k.comp (j.comp i)) X sE sH bEH
    (rationalScalarCanonical l E H (k.comp (j.comp i)) X sE sH)
  subst bEF
  subst bFG
  subst bGH
  subst bEG
  subst bFH
  subst bEH
  constructor
  · intro K
    obtain ⟨aE⟩ := rationalRealizationPullbackComparison l E (𝟙 X) sE sE
    obtain ⟨aH⟩ := rationalRealizationPullbackComparison l H (𝟙 X) sH sH
    obtain ⟨m⟩ := rationalScalarMixedUnitCancellation l E H (k.comp (j.comp i))
      (𝟙 X) sE sE sH sH aE aH
    let nEFG := rationalScalarNormalizationIso
      (rationalBalancedCoefficient l E F i X) (rationalBalancedCoefficient l F G j X)
      (rationalBalancedCoefficient l E G (j.comp i) X)
      (rationalBalancedCoefficient_comp l E F i X G j)
    let nFGH := rationalScalarNormalizationIso
      (rationalBalancedCoefficient l F G j X) (rationalBalancedCoefficient l G H k X)
      (rationalBalancedCoefficient l F H (k.comp j) X)
      (rationalBalancedCoefficient_comp l F G j X H k)
    let nEGH := rationalScalarNormalizationIso
      (rationalBalancedCoefficient l E G (j.comp i) X)
      (rationalBalancedCoefficient l G H k X)
      (rationalBalancedCoefficient l E H (k.comp (j.comp i)) X)
      (rationalBalancedCoefficient_comp l E G (j.comp i) X H k)
    let nEFH := rationalScalarNormalizationIso
      (rationalBalancedCoefficient l E F i X)
      (rationalBalancedCoefficient l F H (k.comp j) X)
      (rationalBalancedCoefficient l E H (k.comp (j.comp i)) X)
      (rationalBalancedCoefficient_comp l E F i X H (k.comp j))
    let left := Functor.isoWhiskerRight nEFG
      (pbcDerivedExtend (rationalBalancedCoefficient l G H k X)) ≪≫ nEGH
    let right := Functor.isoWhiskerLeft
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)) nFGH ≪≫ nEFH
    have he : left.hom.app
        ((rationalPullDerived l E (𝟙 X) aE.rationalCoefficient).obj K) =
        right.hom.app
          ((rationalPullDerived l E (𝟙 X) aE.rationalCoefficient).obj K) := by
      apply (cancel_mono (m.zeta.hom.app K)).1
      simpa only [left, right, nEFG, nFGH, nEGH, nEFH, Iso.trans_hom,
        NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app,
        rationalScalarNormalizationIso_hom, Category.assoc] using
        rationalMixedPentagon l E F i (𝟙 X) sE sE aE G H j k sH sH aH m K
    have hn := rationalScalarNatTrans_transport left.hom right.hom
      ((rationalMixedGeometricUnitor l E sE aE).app K) he
    simpa only [rationalScalarCanonical, Functor.id_obj, left, right, nEFG, nFGH,
      nEGH, nEFH, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      rationalScalarNormalizationIso_hom] using hn
  · intro K
    have hp := rationalBalancedPentagon l E F i X sE G j H k sH K
    simp only [rationalScalarCanonical, Functor.map_comp, Category.assoc] at hp ⊢
    with_unfolding_all exact hp

/-- The mixed ambient square respects every successive coefficient associator.
Together with `compatibility` for each mixed square and the scalar tower equation,
this is the successive-coefficient pasting equation for theta and the specific alpha.
Source: BS 6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-realization-scalar-coherence).

Proof (node step 9): use lem-weil-pbc-reflected-adjunction-coefficient-squares for
pasting of the unit-normalized integral coefficient squares. Its scalar completion
comparison has the same tower law by lem-weil-pbc-finite-free-completion-transport.
Substitute the three completion-unit equations, then alpha_normalization. Adjacent
completion-unit inverses cancel. Both ordinary paths multiply the same coefficient
factors on a common K-flat model. The normalized derived comparison descends that
equality, and the raw fraction formula extends it to every rational morphism. -/
theorem rationalRealizationScalarMixedTower (g : X ⟶ Y)
    (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
    (sXF : RationalModuleRealization l F X) (sYF : RationalModuleRealization l F Y)
    (sXG : RationalModuleRealization l G X) (sYG : RationalModuleRealization l G Y)
    (aE : RationalRealizationPullbackComparison l E g sXE sYE)
    (aF : RationalRealizationPullbackComparison l F g sXF sYF)
    (aG : RationalRealizationPullbackComparison l G g sXG sYG)
    (bXEF : RationalRealizationScalarComparison l E F i X sXE sXF)
    (bYEF : RationalRealizationScalarComparison l E F i Y sYE sYF)
    (bXFG : RationalRealizationScalarComparison l F G j X sXF sXG)
    (bYFG : RationalRealizationScalarComparison l F G j Y sYF sYG)
    (bXEG : RationalRealizationScalarComparison l E G (j.comp i) X sXE sXG)
    (bYEG : RationalRealizationScalarComparison l E G (j.comp i) Y sYE sYG)
    (tX : RationalRealizationScalarTower l E F i G j sXE sXF sXG bXEF bXFG bXEG)
    (tY : RationalRealizationScalarTower l E F i G j sYE sYF sYG bYEF bYFG bYEG)
    (mEF : RationalRealizationScalarMixed l E F i g sXE sYE sXF sYF aE aF bXEF bYEF)
    (mFG : RationalRealizationScalarMixed l F G j g sXF sYF sXG sYG aF aG bXFG bYFG)
    (mEG : RationalRealizationScalarMixed l E G (j.comp i) g
      sXE sYE sXG sYG aE aG bXEG bYEG)
    (K : DerivedCategory (pbcModules Y (rationalCoefficientSheaf l Y E))) :
    mFG.ambient.hom.app ((pbcDerivedExtend bYEF.coefficient).obj K) ≫
        (pbcDerivedExtend bXFG.coefficient).map (mEF.ambient.hom.app K) ≫
        (pbcReductionNormalization bXEF.coefficient bXFG.coefficient bXEG.coefficient
          tX.coefficient ((rationalPullDerived l E g aE.rationalCoefficient).obj K)).hom =
      (rationalPullDerived l G g aG.rationalCoefficient).map
          (pbcReductionNormalization bYEF.coefficient bYFG.coefficient bYEG.coefficient
            tY.coefficient K).hom ≫ mEG.ambient.hom.app K := by
  have hXEF := rationalScalarComparison_unique l E F i X sXE sXF bXEF
    (rationalScalarCanonical l E F i X sXE sXF)
  have hYEF := rationalScalarComparison_unique l E F i Y sYE sYF bYEF
    (rationalScalarCanonical l E F i Y sYE sYF)
  have hXFG := rationalScalarComparison_unique l F G j X sXF sXG bXFG
    (rationalScalarCanonical l F G j X sXF sXG)
  have hYFG := rationalScalarComparison_unique l F G j Y sYF sYG bYFG
    (rationalScalarCanonical l F G j Y sYF sYG)
  have hXEG := rationalScalarComparison_unique l E G (j.comp i) X sXE sXG bXEG
    (rationalScalarCanonical l E G (j.comp i) X sXE sXG)
  have hYEG := rationalScalarComparison_unique l E G (j.comp i) Y sYE sYG bYEG
    (rationalScalarCanonical l E G (j.comp i) Y sYE sYG)
  subst bXEF
  subst bYEF
  subst bXFG
  subst bYFG
  subst bXEG
  subst bYEG
  let nEF := rationalScalarMixedToCancellation l E F i g sXE sYE sXF sYF aE aF mEF
  let nFG := rationalScalarMixedToCancellation l F G j g sXF sYF sXG sYG aF aG mFG
  let nEG := rationalScalarMixedToCancellation l E G (j.comp i) g
    sXE sYE sXG sYG aE aG mEG
  have hn := rationalMixedCoefficientTower l E F i g sXE sYE sXF sYF aE aF
    G j sXG sYG aG nEF nFG nEG K
  have hh := rationalScalarReverseSquare
    ((pbcDerivedExtend (rationalBalancedCoefficient l F G j X)).mapIso (nEF.zeta.app K) ≪≫
      nFG.zeta.app ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj K))
    (nEG.zeta.app K)
    ((rationalPullDerived l G g aG.rationalCoefficient).map
      ((pbcReductionNormalization (rationalBalancedCoefficient l E F i Y)
        (rationalBalancedCoefficient l F G j Y)
        (rationalBalancedCoefficient l E G (j.comp i) Y)
        (rationalBalancedCoefficient_comp l E F i Y G j) K).hom))
    ((pbcReductionNormalization (rationalBalancedCoefficient l E F i X)
      (rationalBalancedCoefficient l F G j X)
      (rationalBalancedCoefficient l E G (j.comp i) X)
      (rationalBalancedCoefficient_comp l E F i X G j)
      ((rationalPullDerived l E g aE.rationalCoefficient).obj K)).hom)
    (by simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Category.assoc] using hn)
  have he := hh.symm
  simp only [nEF, nFG, nEG, rationalScalarMixedToCancellation, rationalScalarCanonical,
    Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv, Category.assoc] at he ⊢
  exact he

/-- The published ordinary-to-strict completion unit as an isomorphism on an integral object.
Source: BS 6.6.11, 6.8.15
(blueprint: lem-per-rational-realization-scalar-coherence). -/
def rationalScalarStrictUnitIso (g : X ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y)
    (a : RationalRealizationPullbackComparison l E g sX sY)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :
    (pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj ≅
      (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K.obj :=
  letI := a.integral.unit_isIso K
  asIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj)

variable {Z : Scheme.{u}} [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]

/-- Strict completed composition is ordinary composition conjugated by its specified units.
Source: BS 6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-realization-scalar-coherence). -/
def rationalScalarStrictPullComp (g : X ⟶ Y) (h : Z ⟶ X)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y)
    (sZ : RationalModuleRealization l E Z)
    (ag : RationalRealizationPullbackComparison l E g sX sY)
    (ah : RationalRealizationPullbackComparison l E h sZ sX)
    (ahg : RationalRealizationPullbackComparison l E (h ≫ g) sZ sY)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :
    (pbcActualStrictCompletedPull (pbcIntegralDatum l E) (h ≫ g)).obj K.obj ≅
      (pbcActualStrictCompletedPull (pbcIntegralDatum l E) h).obj
        ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K.obj) :=
  (rationalScalarStrictUnitIso l E (h ≫ g) sZ sY ahg K).symm ≪≫
    (pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).app K.obj ≪≫
    (pbcActualDerivedPull h (pbcIntegralDatum l E)).mapIso
      (rationalScalarStrictUnitIso l E g sX sY ag K) ≪≫
    rationalScalarStrictUnitIso l E h sZ sX ah ((ag.integral.completedFunctor l E).obj K)

/-- The ordinary module tensor-unit section for the recorded rational pullback.
This is only a composition of the published ringed inverse-image unit and tensor section.
Source: BS 6.8.15; Stacks 03EL
(blueprint: lem-per-rational-realization-scalar-coherence). -/
def rationalScalarPullModuleUnit {S T : Scheme.{u}} (g : S ⟶ T)
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
    (M : pbcModules T (rationalCoefficientSheaf l T E)) (V : T.ProEt)
    (m : M.val.obj (op V)) :
    ((rationalPullModule l E g c).obj M).val.obj (op ((proEtaleBaseChange g).obj V)) :=
  pbcTensorSection c
    ((proEtaleRingModulePullback g (rationalCoefficientSheaf l T E)
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (rationalCoefficientSheaf l T E)) (Iso.refl _)).obj M)
    (op ((proEtaleBaseChange g).obj V)) 1
    (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l T E)
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (rationalCoefficientSheaf l T E)) (Iso.refl _) M V m)

/-- The ambient pullback compositor and its raw strict-completion transport.
Its ordinary section equation specifies the canonical fiber-product pasting;
the derived equation fixes the compositor on the K-flat model and all derived maps.
Source: BS 6.8.15; Stacks 03D8, 0D6D
(blueprint: lem-per-rational-realization-scalar-coherence). -/
structure RationalScalarPullComposition (g : X ⟶ Y) (h : Z ⟶ X)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y)
    (sZ : RationalModuleRealization l E Z)
    (ag : RationalRealizationPullbackComparison l E g sX sY)
    (ah : RationalRealizationPullbackComparison l E h sZ sX)
    (ahg : RationalRealizationPullbackComparison l E (h ≫ g) sZ sY) where
  /-- The coefficient map respects the canonical inverse-image compositor. -/
  coefficient : ahg.rationalCoefficient =
    (proEtaleRingInverseImageComp h g).hom.app (rationalCoefficientSheaf l Y E) ≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map ag.rationalCoefficient ≫
        ah.rationalCoefficient
  /-- Ordinary module pullback composition. -/
  ordinary : rationalPullModule l E (h ≫ g) ahg.rationalCoefficient ≅
    rationalPullModule l E g ag.rationalCoefficient ⋙
      rationalPullModule l E h ah.rationalCoefficient
  /-- Fiber-product pasting and tensor units specify this ordinary comparison. -/
  ordinary_units : ∀ (M : pbcModules Y (rationalCoefficientSheaf l Y E))
      (V : Y.ProEt) (m : M.val.obj (op V)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (h ≫ g)).obj V))
        (rationalScalarPullModuleUnit l E (h ≫ g) ahg.rationalCoefficient M V m) =
      (((rationalPullModule l E h ah.rationalCoefficient).obj
        ((rationalPullModule l E g ag.rationalCoefficient).obj M)).val.map
          ((MorphismProperty.Over.pullbackComp h g).hom.app V).op)
        (rationalScalarPullModuleUnit l E h ah.rationalCoefficient
          ((rationalPullModule l E g ag.rationalCoefficient).obj M)
          ((proEtaleBaseChange g).obj V)
          (rationalScalarPullModuleUnit l E g ag.rationalCoefficient M V m))
  /-- The corresponding ambient derived compositor. -/
  ambient : rationalPullDerived l E (h ≫ g) ahg.rationalCoefficient ≅
    rationalPullDerived l E g ag.rationalCoefficient ⋙
      rationalPullDerived l E h ah.rationalCoefficient
  /-- Its actual derived computation on cochain representatives. -/
  normalization : ∀ P : CochainComplex (pbcModules Y (rationalCoefficientSheaf l Y E)) ℤ,
    ambient.hom.app (DerivedCategory.Q.obj P) ≫
        (rationalPullDerived l E h ah.rationalCoefficient).map
          (rationalPullComplexCounit l E g ag.rationalCoefficient P) ≫
        rationalPullComplexCounit l E h ah.rationalCoefficient
          (((rationalPullModule l E g ag.rationalCoefficient).mapHomologicalComplex
            (.up ℤ)).obj P) =
      rationalPullComplexCounit l E (h ≫ g) ahg.rationalCoefficient P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)
  /-- Raw composition uses exactly the conjugated strict completion units. -/
  raw : ahg.rawPull ≅ ag.rawPull ⋙ ah.rawPull
  /-- Its component on an integral representative, with all object transports visible. -/
  raw_normalization : ∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
    raw.hom.app ((pbcRationalization Y (pbcIntegralDatum l E)
        (pbcUniformizer l E)).obj K) =
      eqToHom (ahg.raw_objects K) ≫
      (pbcRationalization Z (pbcIntegralDatum l E) (pbcUniformizer l E)).map
        (ObjectProperty.homMk
          (X := (ahg.integral.completedFunctor l E).obj K)
          (Y := (ah.integral.completedFunctor l E).obj
            ((ag.integral.completedFunctor l E).obj K))
          ((rationalScalarStrictPullComp l E g h sX sY sZ ag ah ahg K).hom)) ≫
      eqToHom (ah.raw_objects ((ag.integral.completedFunctor l E).obj K)).symm ≫
      ah.rawPull.map (eqToHom (ag.raw_objects K).symm)
  /-- The specific alpha comparisons respect these compositors. -/
  compatibility : ∀ K,
    ahg.alpha.hom.app K ≫ ambient.hom.app (sY.J.obj K) =
      sZ.J.map (raw.hom.app K) ≫ ah.alpha.hom.app (ag.rawPull.obj K) ≫
        (rationalPullDerived l E h ah.rationalCoefficient).map (ag.alpha.hom.app K)

private theorem rationalScalarPresheafIso_cancel
    {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat}
    (M : _root_.PresheafOfModules R) {V W : Cᵒᵖ} (e : V ≅ W) (x : M.obj V) :
    M.map e.inv (M.map e.hom x) = x := by
  rw [← PresheafOfModules.map_comp_apply, Iso.hom_inv_id]
  simp only [PresheafOfModules.map_id]
  rfl

private theorem rationalScalarPresheafIso_inverse_naturality
    {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat}
    {M N : _root_.PresheafOfModules R} (o : M ≅ N)
    {V W : Cᵒᵖ} (e : V ≅ W) (x : M.obj V) (y : N.obj W)
    (h : o.hom.app V x = N.map e.inv y) :
    o.inv.app W y = M.map e.hom x := by
  have hn := PresheafOfModules.naturality_apply o.hom e.hom x
  rw [h] at hn
  erw [rationalScalarPresheafIso_cancel N e.symm y] at hn
  have hi := congrArg (o.inv.app W) hn
  simpa only [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app,
    Iso.hom_inv_id, PresheafOfModules.id_app, ConcreteCategory.id_apply] using hi.symm

/-- Pullback composition retains the same ambient compositor and the strict completion units.
Source: BS 6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-realization-scalar-coherence).

Proof (node step 9): the integral structural maps compose by equality after every finite
quotient projection. Localization preserves that coefficient equation, including its units,
by lem-weil-pbc-localization-inverse-image-coherence. The ordinary composition is the
adjoint of fiber-product pasting, normalized by its tensor units. Its derived descent on
flat-term K-flat complexes is the compositor of lem-sfb-ringed-derived-monoidal-comparisons.
Conjugate this by the actual invertible strict units, as in rationalScalarStrictPullComp.
It preserves the integral subcategories by the recorded pullback comparisons, and its
linearity descends on fractions. Substitute alpha_normalization: adjacent unit pairs
cancel and the remaining equation is exactly ordinary balanced composition. -/
theorem rationalScalarPullComposition (g : X ⟶ Y) (h : Z ⟶ X)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y)
    (sZ : RationalModuleRealization l E Z)
    (ag : RationalRealizationPullbackComparison l E g sX sY)
    (ah : RationalRealizationPullbackComparison l E h sZ sX)
    (ahg : RationalRealizationPullbackComparison l E (h ≫ g) sZ sY) :
    Nonempty (RationalScalarPullComposition l E g h sX sY sZ ag ah ahg) := by
  have hc := rationalPullbackCompositionCoherence l E g h sY sX sZ ag ah ahg
  unfold HasRationalPullbackCompositionCoherence at hc
  obtain ⟨_, _, _, hcoeff, o, ho, d, hd, c, hu, r, hr, hα⟩ := hc
  have hc (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :
      (c.inv.app K).hom =
        (rationalScalarStrictPullComp l E g h sX sY sZ ag ah ahg K).hom := by
    let := ag.integral.unit_isIso K
    let := ah.integral.unit_isIso ((ag.integral.completedFunctor l E).obj K)
    let := ahg.integral.unit_isIso K
    have hunit := hu K
    dsimp only [rationalScalarStrictPullComp, rationalScalarStrictUnitIso,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom, asIso_inv]
    apply (cancel_epi ((pbcActualStrictCompletedPullUnit
      (pbcIntegralDatum l E) (h ≫ g)).app K.obj)).1
    simp only [IsIso.hom_inv_id_assoc]
    apply (cancel_mono (c.hom.app K).hom).1
    have hi := congrArg (fun f ↦ f.hom) (c.inv_hom_id_app K)
    simp only [ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.FullSubcategory.id_hom] at hi
    rw [Category.assoc, hi]
    erw [Category.comp_id]
    rw [Category.assoc, Category.assoc, hu K]
    erw [Iso.hom_inv_id_app_assoc]
  refine ⟨{
    coefficient := hcoeff
    ordinary := o.symm
    ordinary_units := ?_
    ambient := d.symm
    normalization := ?_
    raw := r.symm
    raw_normalization := ?_
    compatibility := ?_ }⟩
  · intro M V m
    have hunit := ho M V m 1 1
    simp only [rationalCoherenceSmul, one_smul, rationalCoherenceScalar,
      map_one, mul_one] at hunit
    have hi := rationalScalarPresheafIso_inverse_naturality
      ((SheafOfModules.forget _).mapIso (o.app M))
      ((MorphismProperty.Over.pullbackComp h g).app V).op
      (rationalCoherenceUnit l E h ah.rationalCoefficient
        ((rationalPullModule l E g ag.rationalCoefficient).obj M)
        ((proEtaleBaseChange g).obj V)
        (rationalCoherenceUnit l E g ag.rationalCoefficient M V m))
      (rationalCoherenceUnit l E (h ≫ g) ahg.rationalCoefficient M V m) hunit
    simp only [Functor.mapIso_inv, SheafOfModules.forget_map, Iso.app_inv,
      rationalScalarPullModuleUnit, rationalCoherenceUnit] at hi ⊢
    exact hi
  · intro P
    change d.inv.app _ ≫ _ ≫ _ = _ ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ)).inv.app P)
    apply (cancel_epi (d.hom.app (DerivedCategory.Q.obj P))).1
    rw [Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc, hd P]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  · intro K
    change r.inv.app _ = _
    rw [← hc K]
    have he : r.app ((pbcRationalization Y (pbcIntegralDatum l E)
        (pbcUniformizer l E)).obj K) =
        eqToIso (congrArg ah.rawPull.obj (ag.raw_objects K)) ≪≫
          eqToIso (ah.raw_objects ((ag.integral.completedFunctor l E).obj K)) ≪≫
          (pbcRationalization Z (pbcIntegralDatum l E) (pbcUniformizer l E)).mapIso
            (c.app K) ≪≫ (eqToIso (ahg.raw_objects K)).symm := by
      apply Iso.ext
      exact hr K
    have hi := congrArg Iso.inv he
    have hm : ObjectProperty.homMk (c.inv.app K).hom = c.inv.app K := rfl
    rw [hm]
    simpa only [Iso.app_inv, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      eqToIso.hom, Functor.mapIso_inv, eqToHom_map, Category.assoc] using hi
  · intro K
    have hn := congrArg (fun t ↦ t.app K) hα
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hn
    change ahg.alpha.hom.app K ≫ d.inv.app _ = sZ.J.map (r.inv.app K) ≫ _
    apply (cancel_epi (sZ.J.map (r.hom.app K))).1
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← Category.assoc, hn]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]


private theorem rationalScalarPull_hom_ext {S T : Scheme.{u}} (g : S ⟶ T)
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
    (M : pbcModules T (rationalCoefficientSheaf l T E))
    (N : pbcModules S (rationalCoefficientSheaf l S E))
    (f k : (rationalPullModule l E g c).obj M ⟶ N)
    (h : ∀ (V : T.ProEt) (m : M.val.obj (op V)),
      f.val.app (op ((proEtaleBaseChange g).obj V))
          (rationalScalarPullModuleUnit l E g c M V m) =
        k.val.app (op ((proEtaleBaseChange g).obj V))
          (rationalScalarPullModuleUnit l E g c M V m)) : f = k := by
  let R := rationalCoefficientSheaf l T E
  let S' := (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R
  let a := (proEtaleRingModuleAdjunction g R S' (Iso.refl _)).comp
    (pbcScalarAdjunction c)
  apply (a.homEquiv M N).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  obtain ⟨V⟩ := U
  simp only [Adjunction.homEquiv_unit, a, Adjunction.comp_unit_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  change f.val.app (op ((proEtaleBaseChange g).obj V))
      (((pbcScalarAdjunction c).unit.app
        ((proEtaleRingModulePullback g R S' (Iso.refl _)).obj M)).val.app
        (op ((proEtaleBaseChange g).obj V))
        (((proEtaleRingModuleAdjunction g R S' (Iso.refl _)).unit.app M).val.app
          (op V) m)) =
    k.val.app (op ((proEtaleBaseChange g).obj V))
      (((pbcScalarAdjunction c).unit.app
        ((proEtaleRingModulePullback g R S' (Iso.refl _)).obj M)).val.app
        (op ((proEtaleBaseChange g).obj V))
        (((proEtaleRingModuleAdjunction g R S' (Iso.refl _)).unit.app M).val.app
          (op V) m))
  rw [(proEtaleRingModuleAdjunction_normalized g R S' (Iso.refl _)) M V m]
  erw [(pbcScalarAdjunction_exists c).exists.choose_spec]
  exact h V m

private theorem rationalScalarPullComposition_ambient (g : X ⟶ Y) (h : Z ⟶ X)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y)
    (sZ : RationalModuleRealization l E Z)
    (ag : RationalRealizationPullbackComparison l E g sX sY)
    (ah : RationalRealizationPullbackComparison l E h sZ sX)
    (ahg : RationalRealizationPullbackComparison l E (h ≫ g) sZ sY)
    (c : RationalScalarPullComposition l E g h sX sY sZ ag ah ahg) :
    c.ambient = (rationalMixedGeometricCompositor l E g sX sY ag h sZ ah ahg).symm := by
  have hc := rationalPullbackCompositionCoherence l E g h sY sX sZ ag ah ahg
  unfold HasRationalPullbackCompositionCoherence at hc
  let o := hc.2.2.2.2.choose
  have ho := hc.2.2.2.2.choose_spec.1
  let d := hc.2.2.2.2.choose_spec.2.choose
  have hd := hc.2.2.2.2.choose_spec.2.choose_spec.1
  have hordinary : c.ordinary = o.symm := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply rationalScalarPull_hom_ext l E (h ≫ g) ahg.rationalCoefficient M _
    intro V m
    have hunit := ho M V m 1 1
    simp only [rationalCoherenceSmul, one_smul, rationalCoherenceScalar,
      map_one, mul_one] at hunit
    have hi := rationalScalarPresheafIso_inverse_naturality
      ((SheafOfModules.forget _).mapIso (o.app M))
      ((MorphismProperty.Over.pullbackComp h g).app V).op
      (rationalCoherenceUnit l E h ah.rationalCoefficient
        ((rationalPullModule l E g ag.rationalCoefficient).obj M)
        ((proEtaleBaseChange g).obj V)
        (rationalCoherenceUnit l E g ag.rationalCoefficient M V m))
      (rationalCoherenceUnit l E (h ≫ g) ahg.rationalCoefficient M V m)
      (by with_unfolding_all exact hunit)
    simp only [Functor.mapIso_inv, SheafOfModules.forget_map, Iso.app_inv,
      rationalScalarPullModuleUnit, rationalCoherenceUnit] at hi ⊢
    have hu := c.ordinary_units M V m
    simp only [rationalScalarPullModuleUnit] at hu
    with_unfolding_all exact hu.trans hi.symm
  suffices he : c.ambient.symm = d by
    exact congrArg Iso.symm he
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (pbcModules Y (rationalCoefficientSheaf l Y E)) (.up ℤ))
  intro P
  obtain ⟨P', q, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := rationalCoefficientSheaf l Y E) P
  have := hq
  have hf' (n : ℤ) : SheafOfModules.IsFlatOnSite (J := ProEt.topology Y)
      (R := rationalCoefficientSheaf l Y E) (P'.X n) := by
    let R := rationalCoefficientSheaf l Y E
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P'.X n)).symm (hf n)
  have he : c.ambient.inv.app (DerivedCategory.Q.obj P') =
      d.hom.app (DerivedCategory.Q.obj P') := by
    have := rationalPullComplexCounit_isIso_of_flatTerms l E (h ≫ g)
      ahg.rationalCoefficient P' hp hf'
    apply (cancel_mono (rationalPullComplexCounit l E (h ≫ g)
      ahg.rationalCoefficient P')).1
    apply (cancel_epi (c.ambient.hom.app (DerivedCategory.Q.obj P'))).1
    rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rw [hd P']
    have hn := c.normalization P'
    rw [hordinary] at hn
    have hn' := congrArg (fun f ↦ f ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P')) hn
    have hcancel :
        (NatIso.mapHomologicalComplex o.symm (.up ℤ)).hom.app P' ≫
          (NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P' = 𝟙 _ :=
      (NatIso.mapHomologicalComplex o (.up ℤ)).inv_hom_id_app P'
    simp only [Category.assoc, ← Functor.map_comp] at hn'
    erw [hcancel, CategoryTheory.Functor.map_id, Category.comp_id] at hn'
    exact hn'.symm
  exact rationalScalarNatTrans_transport c.ambient.inv d.hom
    (asIso (DerivedCategory.Q.map q)) he

/-- Mixed coefficient squares commute with ambient pullback composition.
This equation, the strict-unit equations and alpha compatibility give precisely
pasting of the mixed raw-realization square for two scheme maps.
Source: BS 6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-realization-scalar-coherence).

Proof (node step 9): on the common flat-term K-flat model, fiber-product pasting
identifies both maps with scalar multiplication after inverse image. The normalized
ordinary and derived computation equations therefore give the displayed equality.
Reflection preserves the pasting by lem-weil-pbc-reflected-adjunction-coefficient-squares;
the specified strict units identify it with the strict completion comparison.
Substitute the three mixed compatibility equations and the two alpha composition
equations to obtain its raw realization form. Inverse completion units cancel.
The fraction formulas extend every resulting equality to all raw morphisms. -/
theorem rationalRealizationScalarMixedComp (g : X ⟶ Y) (h : Z ⟶ X)
    (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
    (sZE : RationalModuleRealization l E Z)
    (sXF : RationalModuleRealization l F X) (sYF : RationalModuleRealization l F Y)
    (sZF : RationalModuleRealization l F Z)
    (agE : RationalRealizationPullbackComparison l E g sXE sYE)
    (ahE : RationalRealizationPullbackComparison l E h sZE sXE)
    (ahgE : RationalRealizationPullbackComparison l E (h ≫ g) sZE sYE)
    (agF : RationalRealizationPullbackComparison l F g sXF sYF)
    (ahF : RationalRealizationPullbackComparison l F h sZF sXF)
    (ahgF : RationalRealizationPullbackComparison l F (h ≫ g) sZF sYF)
    (bX : RationalRealizationScalarComparison l E F i X sXE sXF)
    (bY : RationalRealizationScalarComparison l E F i Y sYE sYF)
    (bZ : RationalRealizationScalarComparison l E F i Z sZE sZF)
    (mg : RationalRealizationScalarMixed l E F i g sXE sYE sXF sYF agE agF bX bY)
    (mh : RationalRealizationScalarMixed l E F i h sZE sXE sZF sXF ahE ahF bZ bX)
    (mhg : RationalRealizationScalarMixed l E F i (h ≫ g)
      sZE sYE sZF sYF ahgE ahgF bZ bY)
    (cE : RationalScalarPullComposition l E g h sXE sYE sZE agE ahE ahgE)
    (cF : RationalScalarPullComposition l F g h sXF sYF sZF agF ahF ahgF)
    (K : DerivedCategory (pbcModules Y (rationalCoefficientSheaf l Y E))) :
    (rationalPullDerived l F h ahF.rationalCoefficient).map (mg.ambient.hom.app K) ≫
        mh.ambient.hom.app ((rationalPullDerived l E g agE.rationalCoefficient).obj K) =
      cF.ambient.inv.app ((pbcDerivedExtend bY.coefficient).obj K) ≫
        mhg.ambient.hom.app K ≫
        (pbcDerivedExtend bZ.coefficient).map (cE.ambient.hom.app K) := by
  have hX := rationalScalarComparison_unique l E F i X sXE sXF bX
    (rationalScalarCanonical l E F i X sXE sXF)
  have hY := rationalScalarComparison_unique l E F i Y sYE sYF bY
    (rationalScalarCanonical l E F i Y sYE sYF)
  have hZ := rationalScalarComparison_unique l E F i Z sZE sZF bZ
    (rationalScalarCanonical l E F i Z sZE sZF)
  subst bX
  subst bY
  subst bZ
  let ng := rationalScalarMixedToCancellation l E F i g sXE sYE sXF sYF agE agF mg
  let nh := rationalScalarMixedToCancellation l E F i h sZE sXE sZF sXF ahE ahF mh
  let nhg := rationalScalarMixedToCancellation l E F i (h ≫ g)
    sZE sYE sZF sYF ahgE ahgF mhg
  have hn := rationalMixedGeometricComposition l E F i g sXE sYE sXF sYF agE agF
    h sZE sZF ahE ahgE ahF ahgF ng nh nhg K
  rw [rationalScalarPullComposition_ambient l E g h sXE sYE sZE agE ahE ahgE cE,
    rationalScalarPullComposition_ambient l F g h sXF sYF sZF agF ahF ahgF cF]
  let L := (rationalPullDerived l F h ahF.rationalCoefficient).mapIso (mg.ambient.app K) ≪≫
    mh.ambient.app ((rationalPullDerived l E g agE.rationalCoefficient).obj K)
  let R :=
    (rationalMixedGeometricCompositor l F g sXF sYF agF h sZF ahF ahgF).app
        ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj K) ≪≫
      mhg.ambient.app K ≪≫
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i Z)).mapIso
        ((rationalMixedGeometricCompositor l E g sXE sYE agE h sZE ahE ahgE).symm.app K)
  have he : L.inv = R.inv := by
    simpa only [L, R, ng, nh, nhg, rationalScalarMixedToCancellation,
      Iso.symm_hom, Iso.trans_inv, Iso.app_inv, Iso.symm_inv, Functor.mapIso_inv,
      Category.assoc] using hn
  exact (Iso.inv_eq_inv L R).mp he

/-- Identity scheme pullback uses the canonical identity fiber product and tensor unitor.
The raw identity is specified by alpha and that ambient unitor.
Source: BS 6.8.15; Stacks 03D8, 0D6D
(blueprint: lem-per-rational-realization-scalar-coherence). -/
structure RationalScalarPullIdentity (s : RationalModuleRealization l E X)
    (a : RationalRealizationPullbackComparison l E (𝟙 X) s s) where
  /-- The canonical identity fiber-product isomorphism. -/
  site : proEtaleBaseChange (𝟙 X) ≅ 𝟭 X.ProEt
  /-- Its underlying arrow is the specified first projection. -/
  site_normalization : ∀ V, (site.hom.app V).left = pullback.fst V.hom (𝟙 X)
  /-- The ordinary tensor multiplication unitor for identity scheme pullback. -/
  ordinary : rationalPullModule l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _
  /-- It removes the identity fiber product, using its canonical first projection. -/
  ordinary_units : ∀ (M : pbcModules X (rationalCoefficientSheaf l X E))
      (V : X.ProEt) (m : M.val.obj (op V)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 X)).obj V))
        (rationalScalarPullModuleUnit l E (𝟙 X) a.rationalCoefficient M V m) =
      M.val.map (site.hom.app V).op m
  /-- Its ambient derived unitor. -/
  ambient : rationalPullDerived l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _
  /-- On representatives the unitor is ordinary multiplication after the computation counit. -/
  normalization : ∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
    ambient.hom.app (DerivedCategory.Q.obj P) =
      rationalPullComplexCounit l E (𝟙 X) a.rationalCoefficient P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)
  /-- The strict completed raw pullback is identified using the specific alpha. -/
  raw : a.rawPull ≅ 𝟭 _
  /-- This is the identity equation for the specified alpha. -/
  compatibility : ∀ K,
    a.alpha.hom.app K ≫ ambient.hom.app (s.J.obj K) = s.J.map (raw.hom.app K)

/-- The canonical identity pullback comparisons retain the completion-unit normalization.
Source: BS 6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-realization-scalar-coherence).

Proof (node step 9): ordinary inverse image for the identity is identified through
the first projection of the identity fiber product; tensor multiplication removes
the identity scalar factor. The normalized derived comparison is its descent.
The strict completion unit is invertible on the integral objects, so conjugating
by it gives the strict raw identity. Substitute alpha_normalization to cancel that
unit; the remaining map is the identity tensor multiplication. Raw fractions retain
this equation by their prescribed numerator and denominator formulas. -/
theorem rationalScalarPullIdentity (s : RationalModuleRealization l E X)
    (a : RationalRealizationPullbackComparison l E (𝟙 X) s s) :
    Nonempty (RationalScalarPullIdentity l E s a) := by
  have hc := rationalPullbackIdentityCoherence l E s a
  unfold HasRationalPullbackIdentityCoherence at hc
  obtain ⟨_, _, _, o, ho, d, hd, _, _, r, _, hα⟩ := hc
  refine ⟨{
    site := MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X
    site_normalization := fun V ↦ MorphismProperty.Over.pullbackId_hom_app_left _ _ _ V
    ordinary := o
    ordinary_units := ?_
    ambient := d
    normalization := ?_
    raw := r
    compatibility := ?_ }⟩
  · intro M V m
    have hunit := ho M V m 1
    simp only [rationalCoherenceSmul, one_smul] at hunit
    unfold rationalCoherenceUnit at hunit
    exact hunit
  · intro P
    have hi : (Functor.mapHomologicalComplexIdIso
        (proEtaleRingModules X (rationalCoefficientSheaf l X E)) (.up ℤ)).hom.app P = 𝟙 _ := by
      ext n
      rfl
    have hn := hd P
    simp only [Iso.trans_hom, NatTrans.comp_app, hi] at hn
    simpa only [hi, Functor.map_id, Category.comp_id] using hn
  · intro K
    exact congrArg (fun t ↦ t.app K) hα

private theorem rationalScalarPullIdentity_ambient
    (s : RationalModuleRealization l E X)
    (a : RationalRealizationPullbackComparison l E (𝟙 X) s s)
    (u : RationalScalarPullIdentity l E s a) :
    u.ambient = rationalMixedGeometricUnitor l E s a := by
  have hsite : u.site = MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X := by
    apply Iso.ext
    apply NatTrans.ext
    funext V
    apply MorphismProperty.Comma.Hom.ext
    · exact (u.site_normalization V).trans
        (MorphismProperty.Over.pullbackId_hom_app_left _ _ _ V).symm
    · subsingleton
  have hc := rationalPullbackIdentityCoherence l E s a
  unfold HasRationalPullbackIdentityCoherence at hc
  let o := hc.2.2.2.choose
  have ho := hc.2.2.2.choose_spec.1
  let d := hc.2.2.2.choose_spec.2.choose
  have hd := hc.2.2.2.choose_spec.2.choose_spec.1
  have hordinary : u.ordinary = o := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply rationalScalarPull_hom_ext l E (𝟙 X) a.rationalCoefficient M _
    intro V m
    have hu := u.ordinary_units M V m
    have hv := ho M V m 1
    simp only [rationalCoherenceSmul, one_smul] at hv
    unfold rationalCoherenceUnit at hv
    unfold rationalScalarPullModuleUnit at hu
    rw [hsite] at hu
    have he := hu.trans hv.symm
    simp only [o, rationalScalarPullModuleUnit] at he ⊢
    with_unfolding_all exact he
  change u.ambient = d
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (pbcModules X (rationalCoefficientSheaf l X E)) (.up ℤ))
  intro P
  have hi : (Functor.mapHomologicalComplexIdIso
      (proEtaleRingModules X (rationalCoefficientSheaf l X E)) (.up ℤ)).hom.app P = 𝟙 _ := by
    ext n
    rfl
  change u.ambient.hom.app (DerivedCategory.Q.obj P) = d.hom.app (DerivedCategory.Q.obj P)
  rw [u.normalization P, hordinary]
  have hn := hd P
  simp only [Iso.trans_hom, NatTrans.comp_app, hi] at hn
  simpa only [hi, CategoryTheory.Functor.map_id, Category.comp_id] using hn.symm

/-- The mixed square respects the ambient identity pullback unitors.
Source: BS 6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-realization-scalar-coherence).

Proof (node steps 4 and 9): on ordinary tensors the two paths both remove the
identity scheme pullback and apply the same coefficient map. The tensor units and
fiber-product identity comparisons fix these maps. Their derived normalization
descends the equality. The completion-unit equations and alpha normalizations
then give the identical raw equation by cancellation, including all fractions. -/
theorem rationalRealizationScalarMixedIdentity
    (sE : RationalModuleRealization l E X) (sF : RationalModuleRealization l F X)
    (aE : RationalRealizationPullbackComparison l E (𝟙 X) sE sE)
    (aF : RationalRealizationPullbackComparison l F (𝟙 X) sF sF)
    (b : RationalRealizationScalarComparison l E F i X sE sF)
    (m : RationalRealizationScalarMixed l E F i (𝟙 X) sE sE sF sF aE aF b b)
    (uE : RationalScalarPullIdentity l E sE aE)
    (uF : RationalScalarPullIdentity l F sF aF)
    (K : DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) :
    m.ambient.hom.app K ≫
        (pbcDerivedExtend b.coefficient).map (uE.ambient.hom.app K) =
      uF.ambient.hom.app ((pbcDerivedExtend b.coefficient).obj K) := by
  have hb := rationalScalarComparison_unique l E F i X sE sF b
    (rationalScalarCanonical l E F i X sE sF)
  subst b
  let n := rationalScalarMixedToCancellation l E F i (𝟙 X) sE sE sF sF aE aF m
  have hn := (rationalMixedGeometricIdentity l E F i sE sF aE aF n).1 K
  rw [rationalScalarPullIdentity_ambient l E sE aE uE,
    rationalScalarPullIdentity_ambient l F sF aF uF]
  apply (cancel_epi (m.ambient.inv.app K)).1
  simp only [← Category.assoc, Iso.inv_hom_id_app]
  erw [Category.id_comp]
  exact hn.symm

/-- Theta for the literally identity-normalized raw scalar system, obtained by
conjugating with its published tensor normalization. No pair-category descent occurs.
Source: BS 6.8.14--6.8.15; blueprint scalar extension, order 1307
(blueprint: lem-per-rational-realization-scalar-coherence). -/
def rationalRealizationStageTheta
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
    {A B : Padic.FiniteCoefficientFields l Ω} (h : A ≤ B)
    (sA : RationalModuleRealization l A.val X) (sB : RationalModuleRealization l B.val X)
    (b : RationalRealizationScalarComparison l A.val B.val
      (pbcSubfieldInclusion l Ω h) X sA sB) :
    pbcStageTransition l Ω X h ⋙ sB.J ≅ sA.J ⋙ pbcDerivedExtend b.coefficient :=
  Functor.isoWhiskerRight (pbcStageNormalization l Ω X h).symm sB.J ≪≫ b.theta

/-- The successive-extension diagram uses also the literally normalized raw associators.
Thus the stated field tower includes the scalar system whose identity is literally id.
Source: BS 6.8.14--6.8.15; blueprint scalar extension, order 1307
(blueprint: lem-per-rational-realization-scalar-coherence).

Proof (node step 4): conjugate rationalRealizationScalarTower by the three published
pbcStageNormalization maps. The definition of pbcStageAssociator is precisely the
same conjugation of pbcRationalScalarComp. The normalization maps and their inverses
cancel, giving the displayed equation. The unit and four-field laws follow by the
same cancellation from rationalRealizationScalarUnit and the balanced pentagon,
and agree with pbcStageAssociator_laws, including equal adjacent fields. -/
theorem rationalRealizationStageTower
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
    {A B C : Padic.FiniteCoefficientFields l Ω} (h : A ≤ B) (h' : B ≤ C)
    (sA : RationalModuleRealization l A.val X) (sB : RationalModuleRealization l B.val X)
    (sC : RationalModuleRealization l C.val X)
    (bAB : RationalRealizationScalarComparison l A.val B.val
      (pbcSubfieldInclusion l Ω h) X sA sB)
    (bBC : RationalRealizationScalarComparison l B.val C.val
      (pbcSubfieldInclusion l Ω h') X sB sC)
    (bAC : RationalRealizationScalarComparison l A.val C.val
      (pbcSubfieldInclusion l Ω (h.trans h')) X sA sC)
    (t : RationalRealizationScalarTower l A.val B.val (pbcSubfieldInclusion l Ω h)
      C.val (pbcSubfieldInclusion l Ω h') sA sB sC bAB bBC bAC)
    (K : pbcCoefficientStage l Ω X A) :
    sC.J.map ((pbcStageAssociator l Ω X h h').hom.app K) ≫
        (rationalRealizationStageTheta l Ω (h.trans h') sA sC bAC).hom.app K =
      (rationalRealizationStageTheta l Ω h' sB sC bBC).hom.app
          ((pbcStageTransition l Ω X h).obj K) ≫
        (pbcDerivedExtend bBC.coefficient).map
          ((rationalRealizationStageTheta l Ω h sA sB bAB).hom.app K) ≫
        (pbcReductionNormalization bAB.coefficient bBC.coefficient bAC.coefficient
          t.coefficient (sA.J.obj K)).hom := by
  have hAB := rationalScalarComparison_unique l A.val B.val
    (pbcSubfieldInclusion l Ω h) X sA sB bAB
    (rationalScalarCanonical l A.val B.val (pbcSubfieldInclusion l Ω h) X sA sB)
  have hBC := rationalScalarComparison_unique l B.val C.val
    (pbcSubfieldInclusion l Ω h') X sB sC bBC
    (rationalScalarCanonical l B.val C.val (pbcSubfieldInclusion l Ω h') X sB sC)
  have hAC := rationalScalarComparison_unique l A.val C.val
    (pbcSubfieldInclusion l Ω (h.trans h')) X sA sC bAC
    (rationalScalarCanonical l A.val C.val
      (pbcSubfieldInclusion l Ω (h.trans h')) X sA sC)
  subst bAB
  subst bBC
  subst bAC
  exact rationalBalancedNormalizedTower l X Ω h h' sA sB sC K

end AlgebraicGeometry.Scheme
