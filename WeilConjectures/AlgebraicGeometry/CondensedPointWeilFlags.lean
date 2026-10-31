/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.ConstantExtensionPunctualWeights
public import WeilConjectures.AlgebraicGeometry.AdicLocalCharacteristicFactor
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.FiberRank
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPoint
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import all WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import all Mathlib.Algebra.Field.ULift
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.SiteInverseImageTensor
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import all WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import all WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Full flags in the condensed Weil heart of a point

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real/
thm-zl-real-mixed-by-curves.proof.md, paragraph 7
(blueprint: lem-zl-condensed-point-weil-flags).

## Main definitions

- `matrix`: the actual point-evaluation matrix of a finite free sheaf map.
- `frobeniusMatrix`: the matrix of the given sheaf Weil isomorphism.

## Main statements

- `matrix_bijective`, `matrix_comp`, `matrix_id`, `matrix_add`: the matrix identification.
- `exists_full_flag`: finite free flags and scalar pure quotients in the Weil heart.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeil.PointFlags

/-- The ground-field point as a scheme over the ground field.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags). -/
abbrev model (D : FiniteFieldDatum.{u}) : Over (Spec (.of D.k₀)) where
  left := Spec (.of D.k₀)
  right := ⟨⟨⟩⟩
  hom := 𝟙 _

/-- The point's structural morphism has the existing finite-type property of an identity.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags). -/
instance modelLocallyOfFiniteType (D : FiniteFieldDatum.{u}) :
    LocallyOfFiniteType (model D).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k₀))))

/-- The point's structural morphism has the existing quasi-compactness of an identity.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags). -/
instance modelQuasiCompact (D : FiniteFieldDatum.{u}) : QuasiCompact (model D).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k₀))))

/-- Its geometric base change, canonically isomorphic to Spec(k).
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags). -/
abbrev space (D : FiniteFieldDatum.{u}) := pullback (𝟙 (Spec (.of D.k₀)))
  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- The canonical identification from Spec(k), inverse to the second projection.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags). -/
def pointLift (D : FiniteFieldDatum.{u}) : Spec (.of D.k) ⟶ space D :=
  inv (pullback.snd (𝟙 (Spec (.of D.k₀)))
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))

/-- Finite free modules over the specified pulled-back condensed coefficient ring.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags). -/
abbrev free (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (n : ℕ) :=
  Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj l) (space D)) n

attribute [local irreducible] CondensedQbarGeometricEvaluation.fieldFiber
  CondensedQbarGeometricEvaluation.fieldRegularCoordinates CondensedRing.upperStar

/-- Evaluate the entries of a finite free sheaf map on the unique geometric point.
The regular-module entries are pulled back to Spec(k), evaluated on its final object,
and read in the existing canonical regular-module scalar coordinates.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags). -/
def matrix (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] {a b : ℕ}
    (f : free D l a ⟶ free D l b) : Matrix (Fin b) (Fin a) (PadicAlgCl l) :=
  fun i j ↦ regularScalarValue
    (CondensedQbarGeometricEvaluation.fieldFiber D.k l)
    (CondensedQbarGeometricEvaluation.fieldRegularCoordinates D.k l)
    (CondensedRing.restrictEnd (Profinite.padicAlgClRingObj l) (pointLift D)
      (Mod.finFreeEntry f i j))

/-- The Weil matrix in a chosen global basis, using the canonical coefficient pullback.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags). -/
def frobeniusMatrix (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (M : WeilModule D l (model D)) {n : ℕ} (e : M.carrier ≅ free D l n) :
    Matrix (Fin n) (Fin n) (PadicAlgCl l) :=
  matrix D l ((CondensedRing.upperStarFiniteFreeIso (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius (model D)).hom n).inv ≫
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius (model D)).hom).map e.inv ≫ M.str.hom ≫ e.hom)

private lemma scalar_apply {R : Type*} [CommRing R] {C : Type*} [Category* C]
    (F : C ⥤ ModuleCat R) {X : C} (e : F.obj X ≃ₗ[R] R) (f : X ⟶ X)
    (x : F.obj X) :
    e (F.map f x) = e x * e (F.map f (e.symm 1)) := by
  have hx : x = e x • e.symm 1 := by apply e.injective; simp
  conv_lhs => rw [hx]
  rw [map_smul, e.map_smul]
  rfl

private def scalarHom {R : Type*} [CommRing R] {C : Type*} [Category* C]
    [Preadditive C] (F : C ⥤ ModuleCat R) [F.Additive] {X : C}
    (e : F.obj X ≃ₗ[R] R) : End X →+* R where
  toFun f := e (F.map f (e.symm 1))
  map_zero' := by simp
  map_one' := by simp
  map_add' f g := by simp only [F.map_add, ModuleCat.hom_add, LinearMap.add_apply, e.map_add]
  map_mul' f g := by
    change e (F.map (g ≫ f) (e.symm 1)) = _
    rw [F.map_comp, ModuleCat.comp_apply, scalar_apply]
    exact mul_comm _ _

private def entryMatrix {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] (X : C) {R : Type*} [CommRing R]
    (v : End X →+* R) {a b : ℕ}
    (f : (⨁ fun _ : Fin a ↦ X) ⟶ (⨁ fun _ : Fin b ↦ X)) :
    Matrix (Fin b) (Fin a) R := fun i j ↦ v (biproduct.components f j i)

private lemma entry_comp {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] (X : C) {a b c : ℕ}
    (f : (⨁ fun _ : Fin a ↦ X) ⟶ (⨁ fun _ : Fin b ↦ X))
    (g : (⨁ fun _ : Fin b ↦ X) ⟶ (⨁ fun _ : Fin c ↦ X))
    (i : Fin c) (j : Fin a) :
    biproduct.components (f ≫ g) j i =
      ∑ k : Fin b, biproduct.components f j k ≫ biproduct.components g k i := by
  simp only [biproduct.components, Category.assoc]
  calc
    _ = (biproduct.ι _ j ≫ f) ≫ (𝟙 _) ≫ (g ≫ biproduct.π _ i) := by
      simp only [Category.id_comp, Category.assoc]
    _ = (biproduct.ι _ j ≫ f) ≫
        (∑ k : Fin b, biproduct.π (fun _ : Fin b ↦ X) k ≫
          biproduct.ι (fun _ : Fin b ↦ X) k) ≫
          (g ≫ biproduct.π _ i) := by rw [biproduct.total]
    _ = _ := by
      simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]

private lemma entryMatrix_bijective {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] (X : C) {R : Type*} [CommRing R]
    (v : End X →+* R) (hv : Function.Bijective v) (a b : ℕ) :
    Function.Bijective (entryMatrix X v (a := a) (b := b)) := by
  constructor
  · intro f g h
    apply (biproduct.matrixEquiv (f := fun _ : Fin a ↦ X)
      (g := fun _ : Fin b ↦ X)).injective
    funext j i
    exact hv.1 (congrFun (congrFun h i) j)
  · intro A
    classical
    choose t ht using fun i j ↦ hv.2 (A i j)
    refine ⟨biproduct.matrix (fun j i ↦ t i j), ?_⟩
    ext i j
    change v (biproduct.components (biproduct.matrix (fun j i ↦ t i j)) j i) = A i j
    rw [biproduct.matrix_components]
    exact ht i j

private lemma entryMatrix_comp {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] (X : C) {R : Type*} [CommRing R]
    (v : End X →+* R) {a b c : ℕ}
    (f : (⨁ fun _ : Fin a ↦ X) ⟶ (⨁ fun _ : Fin b ↦ X))
    (g : (⨁ fun _ : Fin b ↦ X) ⟶ (⨁ fun _ : Fin c ↦ X)) :
    entryMatrix X v (f ≫ g) = entryMatrix X v g * entryMatrix X v f := by
  classical
  ext i j
  change v (biproduct.components (f ≫ g) j i) =
    ∑ k, v (biproduct.components g k i) * v (biproduct.components f j k)
  rw [entry_comp X f g i j, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact v.map_mul (End.of (biproduct.components g k i))
    (End.of (biproduct.components f j k))

private lemma entryMatrix_id {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] (X : C) {R : Type*} [CommRing R]
    (v : End X →+* R) (a : ℕ) :
    entryMatrix X v (𝟙 (⨁ fun _ : Fin a ↦ X)) = 1 := by
  classical
  ext i j
  simp only [entryMatrix, biproduct.components, Category.id_comp, Matrix.one_apply]
  by_cases h : j = i
  · subst j
    rw [biproduct.ι_π_self, if_pos rfl]
    exact v.map_one
  · rw [biproduct.ι_π_ne _ h, if_neg (Ne.symm h)]
    exact v.map_zero

private lemma entryMatrix_add {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] (X : C) {R : Type*} [CommRing R]
    (v : End X →+* R) {a b : ℕ}
    (f g : (⨁ fun _ : Fin a ↦ X) ⟶ (⨁ fun _ : Fin b ↦ X)) :
    entryMatrix X v (f + g) = entryMatrix X v f + entryMatrix X v g := by
  ext i j
  simp only [entryMatrix, Matrix.add_apply, biproduct.components,
    Preadditive.add_comp, Preadditive.comp_add, map_add]

section ModuleMatrices

variable {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C]
  [MonoidalPreadditive C] (B : C) [MonObj B]
  {S : Type*} [CommRing S]

private def modMatrix (v : End (Mod.regular B) →+* S) {a b : ℕ}
    (f : Mod.finiteFree B a ⟶ Mod.finiteFree B b) : Matrix (Fin b) (Fin a) S :=
  fun i j ↦ v (Mod.finFreeEntry f i j)

private lemma modMatrix_bijective (v : End (Mod.regular B) →+* S)
    (hv : Function.Bijective v) (a b : ℕ) :
    Function.Bijective (modMatrix B v (a := a) (b := b)) := by
  exact entryMatrix_bijective _ v hv a b

private lemma modMatrix_comp (v : End (Mod.regular B) →+* S) {a b c : ℕ}
    (f : Mod.finiteFree B a ⟶ Mod.finiteFree B b)
    (g : Mod.finiteFree B b ⟶ Mod.finiteFree B c) :
    modMatrix B v (f ≫ g) = modMatrix B v g * modMatrix B v f := by
  exact entryMatrix_comp _ v f g

private lemma modMatrix_id (v : End (Mod.regular B) →+* S) (a : ℕ) :
    modMatrix B v (𝟙 (Mod.finiteFree B a)) = 1 := by
  exact entryMatrix_id _ v a

private lemma modMatrix_add (v : End (Mod.regular B) →+* S) {a b : ℕ}
    (f g : Mod.finiteFree B a ⟶ Mod.finiteFree B b) :
    modMatrix B v (f + g) = modMatrix B v f + modMatrix B v g := by
  exact entryMatrix_add _ v f g

variable {E : Type*} [Category* E] [Preadditive E]
  (F : E ⥤ ModuleCat S) [F.Additive] {X : E} (e : F.obj X ≃ₗ[S] S)
  (r : End (Mod.regular B) →+* End X)

private def evaluatedModMatrix {a b : ℕ}
    (f : Mod.finiteFree B a ⟶ Mod.finiteFree B b) : Matrix (Fin b) (Fin a) S :=
  fun i j ↦ regularScalarValue F e (r (Mod.finFreeEntry f i j))

private lemma evaluatedModMatrix_bijective
    (he : Function.Bijective (scalarHom F e)) (hr : Function.Bijective r) (a b : ℕ) :
    Function.Bijective (evaluatedModMatrix B F e r (a := a) (b := b)) := by
  exact modMatrix_bijective B ((scalarHom F e).comp r) (he.comp hr) a b

private lemma evaluatedModMatrix_comp {a b c : ℕ}
    (f : Mod.finiteFree B a ⟶ Mod.finiteFree B b)
    (g : Mod.finiteFree B b ⟶ Mod.finiteFree B c) :
    evaluatedModMatrix B F e r (f ≫ g) =
      evaluatedModMatrix B F e r g * evaluatedModMatrix B F e r f := by
  exact modMatrix_comp B ((scalarHom F e).comp r) f g

private lemma evaluatedModMatrix_id (a : ℕ) :
    evaluatedModMatrix B F e r (𝟙 (Mod.finiteFree B a)) = 1 := by
  exact modMatrix_id B ((scalarHom F e).comp r) a

private lemma evaluatedModMatrix_add {a b : ℕ}
    (f g : Mod.finiteFree B a ⟶ Mod.finiteFree B b) :
    evaluatedModMatrix B F e r (f + g) =
      evaluatedModMatrix B F e r f + evaluatedModMatrix B F e r g := by
  exact modMatrix_add B ((scalarHom F e).comp r) f g

end ModuleMatrices

private lemma point_scalar_bijective (K : Type u) [Field K] [IsAlgClosed K]
    (l : ℕ) [Fact l.Prime] :
    Function.Bijective (scalarHom (CondensedQbarGeometricEvaluation.fieldFiber K l)
      (CondensedQbarGeometricEvaluation.fieldRegularCoordinates K l)) := by
  classical
  have hw : PointLanWeaklyContractible (Spec (.of K))
      (Scheme.ProEt.mk (𝟙 (Spec (.of K)))) := by
    intro F G f hf s
    have : Sheaf.IsLocallySurjective f := (Sheaf.isLocallySurjective_iff_epi f).mpr hf
    obtain ⟨t, ht⟩ := CondensedQbarGeometricEvaluation.cover_id K _
      (Presheaf.imageSieve_mem _ f.hom s)
    have hid := ConcreteCategory.congr_hom (G.obj.map_id
      (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))) s
    exact ⟨t, ht.trans hid⟩
  have hs := AlgebraicGeometry.ProEtale.condensedQbarScalar_surjective l (Spec (.of K)) hw
  constructor
  · intro f g h
    obtain ⟨a, rfl⟩ := hs f
    obtain ⟨b, rfl⟩ := hs g
    change CondensedQbarGeometricEvaluation.fieldRegularCoordinates K l
      ((CondensedQbarGeometricEvaluation.fieldFiber K l).map
        (condensedQbarScalar l (Spec (.of K)) a)
        ((CondensedQbarGeometricEvaluation.fieldRegularCoordinates K l).symm 1)) =
      CondensedQbarGeometricEvaluation.fieldRegularCoordinates K l
      ((CondensedQbarGeometricEvaluation.fieldFiber K l).map
        (condensedQbarScalar l (Spec (.of K)) b)
        ((CondensedQbarGeometricEvaluation.fieldRegularCoordinates K l).symm 1)) at h
    rw [AlgebraicGeometry.ProEtale.field_scalar,
      AlgebraicGeometry.ProEtale.field_scalar] at h
    congr 1
    apply Subtype.ext
    ext x
    simpa only [Subsingleton.elim x default] using h
  · intro x
    let a : PadicAlgCl.finiteIntermediateFieldValued l (Spec (.of K)) :=
      ⟨ContinuousMap.const _ x, ⟨IntermediateField.adjoin ℚ_[l] {x},
        IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x),
        fun _ ↦ IntermediateField.mem_adjoin_simple_self ℚ_[l] x⟩⟩
    refine ⟨condensedQbarScalar l (Spec (.of K)) a, ?_⟩
    exact AlgebraicGeometry.ProEtale.field_scalar K l a

private lemma restrictEnd_bijective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y Z : Scheme.{u}} (g : Z ⟶ Y) [IsIso g] :
    Function.Bijective (CondensedRing.restrictEnd Λ g) := by
  unfold CondensedRing.restrictEnd
  exact (CondensedRing.upperStarObjRegularIso Λ g).conjRingEquiv.bijective.comp
    ((Functor.FullyFaithful.ofFullyFaithful _).map_bijective _ _)

/-- Evaluation identifies all finite free sheaf maps with matrices over Omega.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags).
Proof: pullback along the point identification is fully faithful. The bounded
coefficient-function scalar theorem identifies regular endomorphisms on Spec(k)
with their value at the unique point; every scalar occurs as a constant bounded
function. Apply this in each coordinate of the finite biproducts, using the
biproduct matrix equivalence; this also handles either rank being zero. -/
theorem matrix_bijective (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p) (a b : ℕ) :
    Function.Bijective (matrix D l (a := a) (b := b)) := by
  classical
  have : IsIso (pointLift D) := by unfold pointLift; infer_instance
  exact evaluatedModMatrix_bijective
    (condensedRingObj (Profinite.padicAlgClRingObj l) (space D))
    (CondensedQbarGeometricEvaluation.fieldFiber D.k l)
    (CondensedQbarGeometricEvaluation.fieldRegularCoordinates D.k l)
    (CondensedRing.restrictEnd (Profinite.padicAlgClRingObj l) (pointLift D))
    (point_scalar_bijective D.k l)
    (restrictEnd_bijective (Profinite.padicAlgClRingObj l) (pointLift D)) a b

/-- Evaluation respects composition of actual finite free sheaf maps.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags).
Proof: expand the biproduct identity between the two maps. Evaluation of the
regular-module entries respects addition and multiplication, giving matrix product. -/
theorem matrix_comp (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {a b c : ℕ} (f : free D l a ⟶ free D l b) (g : free D l b ⟶ free D l c) :
    matrix D l (f ≫ g) = matrix D l g * matrix D l f := by
  exact evaluatedModMatrix_comp
    (condensedRingObj (Profinite.padicAlgClRingObj l) (space D))
    (CondensedQbarGeometricEvaluation.fieldFiber D.k l)
    (CondensedQbarGeometricEvaluation.fieldRegularCoordinates D.k l)
    (CondensedRing.restrictEnd (Profinite.padicAlgClRingObj l) (pointLift D)) f g

/-- Evaluation respects identities of actual finite free sheaves.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags).
Proof: the composite of coordinate inclusion and projection is identity on the
matching coordinate and zero otherwise, and evaluation preserves both. -/
theorem matrix_id (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (a : ℕ) :
    matrix D l (𝟙 (free D l a)) = 1 := by
  exact evaluatedModMatrix_id
    (condensedRingObj (Profinite.padicAlgClRingObj l) (space D))
    (CondensedQbarGeometricEvaluation.fieldFiber D.k l)
    (CondensedQbarGeometricEvaluation.fieldRegularCoordinates D.k l)
    (CondensedRing.restrictEnd (Profinite.padicAlgClRingObj l) (pointLift D)) a

/-- Evaluation respects addition of finite free sheaf maps.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags).
Proof: composition with each inclusion and projection is additive and scalar evaluation
is a ring homomorphism, so each entry is the sum of the corresponding entries. -/
theorem matrix_add (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {a b : ℕ} (f g : free D l a ⟶ free D l b) :
    matrix D l (f + g) = matrix D l f + matrix D l g := by
  exact evaluatedModMatrix_add
    (condensedRingObj (Profinite.padicAlgClRingObj l) (space D))
    (CondensedQbarGeometricEvaluation.fieldFiber D.k l)
    (CondensedQbarGeometricEvaluation.fieldRegularCoordinates D.k l)
    (CondensedRing.restrictEnd (Profinite.padicAlgClRingObj l) (pointLift D)) f g

/-- The constructible point carrier is finite free over the condensed coefficient ring.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags).
Proof: put s = Spec k, canonically isomorphic to the geometric point, and B the
pulled-back coefficient ring. The field k is strictly henselian and |s| is one point,
so s is w-local with extremally disconnected component space; the geometric criterion
and affine weak contractibility make evaluation at s send epimorphisms of sheaves of
sets to surjections. On the one-stratum scheme s, constructibility with finite constant
models makes M pro-etale locally free of finite rank (finitely presented modules over
the field Omega are free). The sheaf of local trivializations of all finite ranks maps
epimorphically to the terminal sheaf; lift its unique section at s. This is a global
isomorphism of M with B^d for some d, possibly 0.
(blueprint: lem-zl-condensed-point-weil-flags-finite-free)
-/
theorem finite_free_carrier (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p) (M : WeilModule D l (model D))
    (_hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (space D)
      M.carrier) :
    ∃ d : ℕ, Nonempty (M.carrier ≅ free D l d) := by
  sorry

/-- Given a finite-free basis, the Frobenius module admits the required full flag.
Source: latest blueprint, paragraph 7 (blueprint: lem-zl-condensed-point-weil-flags).
Proof:
1. Write g for Frobenius and c_a for the natural comparison of g-pullback of B^a with
B^a. Conjugating the Weil isomorphism by e and c_d gives the sheaf map whose matrix is
`frobeniusMatrix`; by `matrix_bijective`, `matrix_comp`, `matrix_id` it is an invertible
matrix, i.e. an Omega-linear automorphism A of Omega^d (linear, the scalars are fixed).
2. Induct on d: for d > 0 an eigenvector v of A exists (Omega algebraically closed),
its eigenvalue is nonzero, the line through v is A- and A^{-1}-stable, and the flag of
the induced automorphism of the quotient pulls back. This gives an A-stable full flag
without diagonalizing A (Jordan blocks allowed).
3. In an adapted basis P the matrix C = P^{-1} A P is upper triangular with nonzero
diagonal alpha_j. Give B^j the Weil structure of the top-left j-block of C; the
coordinate inclusions B^j -> B^{j+1}, composed with e and P, are monic Weil maps, and
the last-coordinate projection is their cokernel, with scalar Frobenius alpha_j.
Finite free sheaves are constructible and the coefficient heart is exact, so these are
the actual subobjects and cokernels.
4. The local Frobenius at the unique closed point acts on each quotient by alpha_j;
since q > 1 and alpha_j is nonzero, q^(w/2) = norm(iota(alpha_j)) for
w = 2 log_q norm(iota(alpha_j)), which is punctual purity of weight w. For d = 0 the
flag is the zero object and there are no quotients.
(blueprint: lem-zl-condensed-point-weil-flags-flag-data)
-/
theorem flag_data_of_finite_free (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p) (iota : PadicAlgCl l ≃+* ℂ)
    (M : WeilModule D l (model D)) (d : ℕ)
    (e : M.carrier ≅ free D l d) :
    ∃ (A : (Fin d → PadicAlgCl l) ≃ₗ[PadicAlgCl l] (Fin d → PadicAlgCl l)),
      A.toLinearMap = (frobeniusMatrix D l M e).mulVecLin ∧
      ∃ (G : Fin (d + 1) → WeilModule D l (model D))
        (f : ∀ j : Fin d, G j.castSucc ⟶ G j.succ),
        IsZero (G 0) ∧ Nonempty (G (Fin.last d) ≅ M) ∧
        (∀ j, IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
          (space D) (G j).carrier) ∧
        (∀ j, Nonempty ((G j).carrier ≅ free D l j.val)) ∧
        (∀ j : Fin d, Mono (f j)) ∧
        ∀ j : Fin d,
          IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
            (space D) (cokernel (f j)).carrier ∧
          ∃ (alpha : (PadicAlgCl l)ˣ)
            (b : (cokernel (f j)).carrier ≅ free D l 1),
            frobeniusMatrix D l (cokernel (f j)) b =
              (fun _ _ ↦ (alpha : PadicAlgCl l)) ∧
            Pure D l (model D) (cokernel (f j)) iota.toRingHom
              (2 * Real.logb (D.q : ℝ) ‖iota (alpha : PadicAlgCl l)‖) := by
  sorry

/-- A full flag by actual constructible Weil subobjects with rank-one pure quotients.
Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, paragraph 7
(blueprint: lem-zl-condensed-point-weil-flags).
Proof:
1. The geometric point is strictly henselian, w-local, with extremally disconnected
component space. The geometric criterion and affine weak-contractibility theorem
split a cover of local trivializations. The coefficient-heart lisse criterion
therefore gives a global finite free basis of M, of some rank d including zero.
2. The finite-coefficient-point adjunction identifies B(s) with Omega; maps from
B are determined by the image of 1. Thus actual sheaf maps between finite powers
are matrices, with their usual composition, addition and identity formulas.
3. The natural module comparison for Frobenius pullback identifies its pullback
of each constant free module with itself, naturally in constant matrix maps.
Conjugate the given Weil isomorphism by a basis and this comparison to obtain
an invertible Omega-linear matrix on Omega^d, with no action on the scalars.
4. Induct on d. For positive d choose an eigenline using eigenvalue existence
over the algebraically closed field. Invertibility makes its eigenvalue nonzero
and preserves the line under the inverse as well. Induct on the quotient and
pull back its flag. This handles Jordan blocks without diagonalizing anything.
5. Choose an adapted basis. Its upper triangular Frobenius matrix gives the
Weil structures on the first j summands. Coordinate inclusions are monic and
Weil-equivariant; the last-coordinate projection is their actual cokernel,
with scalar Frobenius alpha_j. The coefficient heart is exact, so these are
subobjects and quotients in the constructible sheaf heart, not unrelated stalks.
6. The local return at the unique closed point acts on each quotient by alpha_j.
Its nonzero modulus and q > 1 give q^(w_j/2) = norm(iota(alpha_j)) for
w_j = 2 log_q norm(iota(alpha_j)), proving punctual purity. There is no reality
hypothesis; for d=0 there are no quotients. The datum D is arbitrary, so the
same construction applies over any finite extension with its own cardinality. -/
theorem exists_full_flag (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p) (iota : PadicAlgCl l ≃+* ℂ)
    (M : WeilModule D l (model D))
    (_hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (space D)
      M.carrier) :
    ∃ (d : ℕ) (e : M.carrier ≅ free D l d)
      (A : (Fin d → PadicAlgCl l) ≃ₗ[PadicAlgCl l] (Fin d → PadicAlgCl l)),
      A.toLinearMap = (frobeniusMatrix D l M e).mulVecLin ∧
      ∃ (G : Fin (d + 1) → WeilModule D l (model D))
        (f : ∀ j : Fin d, G j.castSucc ⟶ G j.succ),
        IsZero (G 0) ∧ Nonempty (G (Fin.last d) ≅ M) ∧
        (∀ j, IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
          (space D) (G j).carrier) ∧
        (∀ j, Nonempty ((G j).carrier ≅ free D l j.val)) ∧
        (∀ j : Fin d, Mono (f j)) ∧
        ∀ j : Fin d,
          IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (space D)
            (cokernel (f j)).carrier ∧
          ∃ (alpha : (PadicAlgCl l)ˣ)
            (b : (cokernel (f j)).carrier ≅ free D l 1),
            frobeniusMatrix D l (cokernel (f j)) b =
              (fun _ _ ↦ (alpha : PadicAlgCl l)) ∧
            Pure D l (model D) (cokernel (f j)) iota.toRingHom
              (2 * Real.logb (D.q : ℝ) ‖iota (alpha : PadicAlgCl l)‖) := by
  obtain ⟨d, ⟨e⟩⟩ := finite_free_carrier D l _hl M _hM
  obtain ⟨A, hA, hflag⟩ := flag_data_of_finite_free D l _hl iota M d e
  exact ⟨d, e, A, hA, hflag⟩

end WeilConjectures.CondensedWeil.PointFlags
