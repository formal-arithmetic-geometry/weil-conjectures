/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
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
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.AlgebraicGeometry.CoefficientHeartCommonStratification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.AlgebraicGeometry.FieldPointFactorsThroughImmersion
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.AlgebraicGeometry.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-! # Geometric fibre detection for constructible condensed coefficients

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definitions 6.8.3 and 6.8.6,
Proposition 6.8.4, Corollary 6.8.5 and Lemma 6.8.7; current blueprint,
sec-deligne-laumon-a1/sk-p-dl-a1-exact/p-dl-a1-exact.proof.md, Steps 1 and 5
(blueprint: lem-dl-a1-condensed-fibres-exact).

Fibres are terminal sections of actual condensed module pullback. The scalar transport
in fieldFiber identifies the terminal coefficient ring with PadicAlgCl ell. Constructibility
is the recorded finite-constant-model predicate, locally on affine opens on arbitrary schemes.
The two applications of Assertions below are ordinary modules and degree-zero fixed pairs.

## Main declarations

- `fibre` and `affineRestriction`: the actual geometric fibre and patch restriction.
- `Assertions` and `AffineAssertions`: the clauses of the geometric and local criteria.
- `condensed_fibres_exact`: those criteria for ordinary modules and degree-zero Weil pairs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.DeligneLaumonFibres

/-- The fibre functor x^* followed by evaluation at Spec K, with its canonical scalar action.
Source: Bhatt--Scholze, Definition 6.8.3; current blueprint p-dl-a1-exact.proof.md, Step 1
(blueprint: lem-dl-a1-condensed-fibres-exact). -/
abbrev fibre (ell : ℕ) [Fact ell.Prime] {T : Scheme.{u}}
    {K : Type u} [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ T) :=
  CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) x ⋙
    CondensedQbarGeometricEvaluation.fieldFiber K ell

/-- The geometric affine patch is the inverse image of U under T → T₀; its restriction
is the existing module inverse image along that open immersion.
Source: Bhatt--Scholze, Definition 6.8.6, affine-local condition
(blueprint: lem-dl-a1-condensed-fibres-exact). -/
abbrev affineRestriction (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (T₀ : Over (Spec (.of D.k₀))) (U : T₀.left.Opens) :=
  CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
    ((pullback.fst T₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ⁻¹ᵁ U).ι)

/-- The fibre assertions for a category of modules, or fixed pairs with carrier functor F.
All tests are restricted to constructible carriers. Exactness includes finite limits and
colimits in that full subcategory; the explicit sequence test uses ordinary vector spaces.
Source: Bhatt--Scholze, Lemma 6.8.7; current blueprint p-dl-a1-exact.proof.md, Steps 1 and 5
(blueprint: lem-dl-a1-condensed-fibres-exact). -/
structure Assertions (ell : ℕ) [Fact ell.Prime] (T : Scheme.{u})
    {C : Type v} [Category.{w} C] [Preadditive C]
    (F : C ⥤ Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T)) [F.Additive] : Prop where
  finite_dimension : ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ T) (M : C),
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T (F.obj M) →
    FiniteDimensional (PadicAlgCl ell) ((F ⋙ fibre ell x).obj M)
  exact : ∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ T),
    PreservesFiniteLimits
      ((ObjectProperty.ι (fun M : C ↦
        IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T (F.obj M))) ⋙
          F ⋙ fibre ell x) ∧
    PreservesFiniteColimits
      ((ObjectProperty.ι (fun M : C ↦
        IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T (F.obj M))) ⋙
          F ⋙ fibre ell x) ∧
    ((ObjectProperty.ι (fun M : C ↦
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T (F.obj M))) ⋙
        F ⋙ fibre ell x).Additive
  conservative : ∀ (M N : C) (f : M ⟶ N),
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T (F.obj M) →
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T (F.obj N) →
    (∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ T),
      IsIso ((F ⋙ fibre ell x).map f)) → IsIso f
  zero_test : ∀ (M N : C) (f : M ⟶ N),
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T (F.obj M) →
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T (F.obj N) →
    (f = 0 ↔ ∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ T),
      (F ⋙ fibre ell x).map f = 0)
  short_exact_test : ∀ S : ShortComplex C,
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T (F.obj S.X₁) →
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T (F.obj S.X₂) →
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T (F.obj S.X₃) →
    (S.ShortExact ↔ ∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ T),
      Function.Injective ((F ⋙ fibre ell x).map S.f).hom ∧
      Function.Exact ((F ⋙ fibre ell x).map S.f).hom ((F ⋙ fibre ell x).map S.g).hom ∧
      Function.Surjective ((F ⋙ fibre ell x).map S.g).hom)

/-- Zero and short-exactness tests on every affine covering of the finite-field model.
No finite global cover, separation of T₀, constant rank or Weil descent is assumed.
Source: Bhatt--Scholze, Definition 6.8.6, affine-local condition
(blueprint: lem-dl-a1-condensed-fibres-exact). -/
structure AffineAssertions (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (T₀ : Over (Spec (.of D.k₀)))
    {C : Type v} [Category.{w} C] [Preadditive C]
    (F : C ⥤ Mod (Sheaf (Scheme.ProEt.topology
      (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell)
        (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))))
    [F.Additive] : Prop where
  zero_test : ∀ (I : Type u) (U : I → T₀.left.Opens),
    (∀ i : I, IsAffineOpen (U i)) → (⨆ i, U i) = ⊤ →
    ∀ (M N : C) (f : M ⟶ N),
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) _ (F.obj M) →
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) _ (F.obj N) →
      (f = 0 ↔ ∀ i : I, (F ⋙ affineRestriction D ell T₀ (U i)).map f = 0)
  short_exact_test : ∀ (I : Type u) (U : I → T₀.left.Opens),
    (∀ i : I, IsAffineOpen (U i)) → (⨆ i, U i) = ⊤ →
    ∀ S : ShortComplex C,
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) _ (F.obj S.X₁) →
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) _ (F.obj S.X₂) →
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) _ (F.obj S.X₃) →
      (S.ShortExact ↔ ∀ i : I, (S.map (F ⋙ affineRestriction D ell T₀ (U i))).ShortExact)

-- Keep inverse-image implementations folded while elaborating dependent restrictions.
attribute [local irreducible] CondensedRing.upperStar CondensedRing.upperStarComp

private instance fieldFiber_limits (ell : ℕ) [Fact ell.Prime]
    (K : Type u) [Field K] [IsAlgClosed K] :
    PreservesFiniteLimits (CondensedQbarGeometricEvaluation.fieldFiber K ell) := by
  unfold CondensedQbarGeometricEvaluation.fieldFiber
  infer_instance

private theorem noetherian_closure (ell : ℕ) [Fact ell.Prime]
    (T : Scheme.{u}) [IsNoetherian T] (J : Type) [SmallCategory J] [FinCategory J] :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T) J ∧
    ObjectProperty.IsClosedUnderColimitsOfShape
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T) J := by
  let P : ObjectProperty _ := IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T
  have h := (coefficientHeart_closure ell (Profinite.padicAlgClCondensedRing ell)
    (Or.inr rfl)).2 T
  let : Abelian P.FullSubcategory := h.2.2.2.1.some
  have : PreservesFiniteLimits P.ι := h.2.2.2.2.1
  have : PreservesFiniteColimits P.ι := h.2.2.2.2.2.1
  have : P.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined
      (Profinite.padicAlgClRingObj ell) T).1
  exact ⟨P.isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι J,
    P.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι J⟩

private theorem noetherian_constructible_iff (ell : ℕ) [Fact ell.Prime]
    (T : Scheme.{u}) [IsNoetherian T]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T)) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T M ↔
      IsFiniteConstantStratified (Profinite.padicAlgClRingObj ell) T M := by
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]

private theorem constructible_affine (ell : ℕ) [Fact ell.Prime]
    (T : Scheme.{u}) (hT : ¬(CompactSpace T ∧ QuasiSeparatedSpace T))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T M)
    (U : T.Opens) (hU : IsAffineOpen U) :
    IsFiniteConstantStratified (Profinite.padicAlgClRingObj ell) U.toScheme
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) U.ι).obj M) := by
  rw [IsConstantModelConstructible, if_neg hT] at hM
  exact hM U hU

private theorem local_closure (ell : ℕ) [Fact ell.Prime]
    (T : Scheme.{u}) [IsLocallyNoetherian T]
    (J : Type) [SmallCategory J] [FinCategory J] :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T) J ∧
    ObjectProperty.IsClosedUnderColimitsOfShape
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T) J := by
  classical
  by_cases hT : CompactSpace T ∧ QuasiSeparatedSpace T
  · have : CompactSpace T := hT.1
    have : IsNoetherian T := {}
    exact noetherian_closure ell T J
  constructor
  · refine ⟨?_⟩
    rintro M ⟨p⟩
    rw [IsConstantModelConstructible, if_neg hT]
    intro U hU
    have : IsAffine U.toScheme := hU
    have : IsNoetherian U.toScheme := {}
    let Q : ObjectProperty _ :=
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) U.toScheme
    let R := CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) U.ι
    have : Q.IsClosedUnderLimitsOfShape J := (noetherian_closure ell U.toScheme J).1
    have hd (j : J) : (Q.inverseImage R) (p.diag.obj j) :=
      (noetherian_constructible_iff ell U.toScheme _).mpr
        (constructible_affine ell T hT _ (p.prop_diag_obj j) U hU)
    have hm : (Q.inverseImage R) M :=
      (Q.inverseImage R).prop_of_isLimit (c := { pt := M, π := p.π }) p.isLimit hd
    exact (noetherian_constructible_iff ell U.toScheme _).mp hm
  · refine ⟨?_⟩
    rintro M ⟨p⟩
    rw [IsConstantModelConstructible, if_neg hT]
    intro U hU
    have : IsAffine U.toScheme := hU
    have : IsNoetherian U.toScheme := {}
    let Q : ObjectProperty _ :=
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) U.toScheme
    let R := CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) U.ι
    have : Q.IsClosedUnderColimitsOfShape J := (noetherian_closure ell U.toScheme J).2
    have hd (j : J) : (Q.inverseImage R) (p.diag.obj j) :=
      (noetherian_constructible_iff ell U.toScheme _).mpr
        (constructible_affine ell T hT _ (p.prop_diag_obj j) U hU)
    have hm : (Q.inverseImage R) M :=
      (Q.inverseImage R).prop_of_isColimit (c := { pt := M, ι := p.ι }) p.isColimit hd
    exact (noetherian_constructible_iff ell U.toScheme _).mp hm

private theorem constructible_inclusion_exact (ell : ℕ) [Fact ell.Prime]
    (T : Scheme.{u}) [IsLocallyNoetherian T]
    {C : Type v} [Category.{w} C] [Abelian C]
    (F : C ⥤ Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    PreservesFiniteLimits
      (ObjectProperty.ι (fun M : C ↦
        IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T (F.obj M))) ∧
    PreservesFiniteColimits
      (ObjectProperty.ι (fun M : C ↦
        IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T (F.obj M))) := by
  let P : ObjectProperty _ := IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T
  constructor
  · refine ⟨fun J _ _ ↦ ?_⟩
    have : P.IsClosedUnderLimitsOfShape J := (local_closure ell T J).1
    change PreservesLimitsOfShape J (P.inverseImage F).ι
    infer_instance
  · refine ⟨fun J _ _ ↦ ?_⟩
    have : P.IsClosedUnderColimitsOfShape J := (local_closure ell T J).2
    change PreservesColimitsOfShape J (P.inverseImage F).ι
    infer_instance

private noncomputable def fibre_regular_coordinates (ell : ℕ) [Fact ell.Prime]
    {T : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ T) :
    (fibre ell x).obj (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
      ≃ₗ[PadicAlgCl ell] PadicAlgCl ell :=
  ((CondensedQbarGeometricEvaluation.fieldFiber K ell).mapIso
    (condensedQbarRegularPullbackIso ell x)).toLinearEquiv |>.trans
      (CondensedQbarGeometricEvaluation.fieldRegularCoordinates K ell)

private noncomputable def fibre_free_coordinates (ell : ℕ) [Fact ell.Prime]
    {T : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ T) (n : ℕ) :
    (fibre ell x).obj (Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ell) T) n)
      ≃ₗ[PadicAlgCl ell] (Fin n → PadicAlgCl ell) :=
  (((fibre ell x).mapBiproduct (fun _ : Fin n ↦
      Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ell) T)) ≪≫
    ModuleCat.biproductIsoPi _).toLinearEquiv).trans
      (LinearEquiv.piCongrRight (fun _ ↦ fibre_regular_coordinates ell x))

private theorem free_fibre_finite (ell : ℕ) [Fact ell.Prime]
    {T : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
    (hM : Mod.IsFree (condensedRingObj (Profinite.padicAlgClRingObj ell) T) M) :
    FiniteDimensional (PadicAlgCl ell) ((fibre ell x).obj M) := by
  obtain ⟨n, ⟨e⟩⟩ := hM
  exact Module.Finite.equiv
    (((fibre ell x).mapIso e).toLinearEquiv.trans (fibre_free_coordinates ell x n)).symm

private noncomputable def fibre_comp_iso (ell : ℕ) [Fact ell.Prime]
    {T S : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (f : S ⟶ T) (x : Spec (.of K) ⟶ S)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T)) :
    (fibre ell (x ≫ f)).obj M ≅ (fibre ell x).obj
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) f).obj M) :=
  (CondensedQbarGeometricEvaluation.fieldFiber K ell).mapIso
    ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj ell) x f).app M)

private theorem fibre_comp_zero (ell : ℕ) [Fact ell.Prime]
    {T S : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (f : S ⟶ T) (x : Spec (.of K) ⟶ S)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
    (hM : IsZero ((fibre ell (x ≫ f)).obj M)) :
    IsZero ((fibre ell x).obj
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) f).obj M)) :=
  hM.of_iso (fibre_comp_iso ell f x M).symm

private theorem lisse_fibre_finite (ell : ℕ) [Fact ell.Prime]
    {T : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) M) :
    FiniteDimensional (PadicAlgCl ell) ((fibre ell x).obj M) := by
  obtain ⟨U, hU⟩ := hM
  obtain ⟨i, g, hg⟩ := U.exists_comp_eq_of_isSepClosed_of_proetale x
  have := free_fibre_finite ell g _ (hU i)
  have h : FiniteDimensional (PadicAlgCl ell) ((fibre ell (g ≫ U.f i)).obj M) :=
    Module.Finite.equiv (fibre_comp_iso ell (U.f i) g M).toLinearEquiv.symm
  subst x
  exact h

-- Abstract restriction predicates before specializing covering or stratum projections.
private def restrictionZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {T S : Scheme.{u}} (f : S ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) : Prop :=
  IsZero ((CondensedRing.upperStar Λ f).obj M)

private theorem restrictionZero_iff
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {T S : Scheme.{u}} (f : S ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
    restrictionZero Λ f M ↔ IsZero ((CondensedRing.upperStar Λ f).obj M) := Iff.rfl

private def restrictionLisse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {T S : Scheme.{u}} (f : S ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) : Prop :=
  IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ f).obj M)

private theorem restrictionLisse_iff
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {T S : Scheme.{u}} (f : S ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
    restrictionLisse Λ f M ↔
      IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ f).obj M) := Iff.rfl

private theorem module_family_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {T : Scheme.{u}} {I : Type u} (U : I → Scheme.{u}) (f : ∀ i, U i ⟶ T)
    (hU : Presieve.ofArrows U f ∈ Scheme.proetalePrecoverage T)
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (g : M ⟶ N) (hg : ∀ i, IsIso ((CondensedRing.upperStar Λ (f i)).map g)) :
    IsIso g := by
  have hweak (i : I) : WeaklyEtale (f i) :=
    (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale T hU) ⟨i⟩
  have : IsIso ((Mod.forget (condensedRingObj Λ T)).map g) := by
    apply isIso_of_isIso_localizationRestriction Ab.{u + 1} _ f hU
    intro i
    let e := coefficientPullbackForgetIso Λ (f i)
    have := hg i
    have hi : IsIso ((upperStar Ab.{u + 1} (f i)).map g.hom) :=
      (NatIso.isIso_map_iff e g).1 (by
        change IsIso ((Mod.forget _).map ((CondensedRing.upperStar Λ (f i)).map g))
        infer_instance)
    exact (NatIso.isIso_map_iff
      (upperStarIsoLocalizationRestriction Ab.{u + 1} (f i) (hweak i)) g.hom).1 hi
  exact isIso_of_reflects_iso g (Mod.forget _)

private theorem module_family_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {T : Scheme.{u}} {I : Type u} (U : I → Scheme.{u}) (f : ∀ i, U i ⟶ T)
    (hU : Presieve.ofArrows U f ∈ Scheme.proetalePrecoverage T)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hM : ∀ i, restrictionZero Λ (f i) M) : IsZero M := by
  have : IsIso (0 : M ⟶ 0) :=
    module_family_iso Λ U f hU _ fun i ↦
      ((restrictionZero_iff Λ (f i) M).mp (hM i)).isIso
        ((CondensedRing.upperStar Λ (f i)).map_isZero (isZero_zero _)) _
  exact (isZero_zero _).of_iso (asIso (0 : M ⟶ 0))

private theorem module_cover_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {T : Scheme.{u}} (U : Scheme.Cover.{u} Scheme.proetalePrecoverage T)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hM : ∀ i, IsZero ((CondensedRing.upperStar Λ (U.f i)).obj M)) : IsZero M :=
  module_family_zero Λ U.X U.f U.mem₀ M
    (fun i ↦ (restrictionZero_iff Λ (U.f i) M).mpr (hM i))

private theorem open_family_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {T : Scheme.{u}} {I : Type u} (U : I → T.Opens) (hU : (⨆ i, U i) = ⊤)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hM : ∀ i, restrictionZero Λ (U i).ι M) : IsZero M := by
  have hcover : Presieve.ofArrows (fun i ↦ (U i).toScheme) (fun i ↦ (U i).ι) ∈
      Scheme.proetalePrecoverage T := by
    let V : T.OpenCover := Scheme.Cover.mkOfCovers I
      (fun i ↦ (U i).toScheme) (fun i ↦ (U i).ι) (by
        intro x
        have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
        exact ⟨i, ⟨x, hi⟩, rfl⟩)
    exact Scheme.zariskiPrecoverage_le_proetalePrecoverage _ V.mem₀
  exact module_family_zero Λ (fun i ↦ (U i).toScheme) (fun i ↦ (U i).ι) hcover M hM

-- Keep the rank argument abstract in the vector space to avoid unfolding pullback actions.
private theorem rank_zero_of_zero (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    (V : ModuleCat.{v} (PadicAlgCl ell))
    (e : V ≃ₗ[PadicAlgCl ell] (Fin n → PadicAlgCl ell)) (hV : IsZero V) : n = 0 := by
  by_contra hn
  let j : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  have := ModuleCat.isZero_iff_subsingleton.mp hV
  have h10 : (fun _ : Fin n ↦ (1 : PadicAlgCl ell)) = 0 :=
    e.symm.injective (Subsingleton.elim _ _)
  exact one_ne_zero (congrFun h10 j)

private theorem empty_biproduct_zero {C : Type v} [Category.{w} C] [Preadditive C]
    [HasFiniteBiproducts C]
    (A : C) : IsZero (⨁ fun _ : Fin 0 ↦ A) := by
  rw [IsZero.iff_id_eq_zero]
  apply biproduct.hom_ext
  intro j
  exact j.elim0

private theorem lisse_zero (ell : ℕ) [Fact ell.Prime]
    {T : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) M)
    (hz : ∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ T),
      IsZero ((fibre ell x).obj M)) : IsZero M := by
  classical
  obtain ⟨U, hU⟩ := hM
  apply module_cover_zero (Profinite.padicAlgClRingObj ell) U M
  intro i
  let N := (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) (U.f i)).obj M
  rcases isEmpty_or_nonempty (U.X i) with h | ⟨⟨z⟩⟩
  · exact CondensedRing.isZero_mod_of_isEmpty (Profinite.padicAlgClRingObj ell) N
  obtain ⟨n, ⟨e⟩⟩ := hU i
  let x := CondensedQbarGeometricEvaluation.geometricPoint (U.X i) z
  have hN : IsZero ((fibre ell x).obj N) :=
    fibre_comp_zero ell (U.f i) x M (hz _ (x ≫ U.f i))
  have hfree : IsZero ((fibre ell x).obj
      (Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ell) (U.X i)) n)) :=
    hN.of_iso ((fibre ell x).mapIso e.symm)
  have hn : n = 0 := rank_zero_of_zero ell n _ (fibre_free_coordinates ell x n) hfree
  subst n
  have : HasFiniteBiproducts (Mod (Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) (U.X i))) :=
    Abelian.hasFiniteBiproducts
  exact (empty_biproduct_zero
    (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ell) (U.X i)))).of_iso e

private theorem coefficient_lisse_stratification (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ell] (PadicAlgCl ell),
      FiniteDimensional ℚ_[ell] E ∧ Λ = Profinite.padicSubfieldCondensedRing ell E) ∨
      Λ = Profinite.padicAlgClCondensedRing ell)
    {T : Scheme.{u}} [IsNoetherian T]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) T))
    (hM : IsConstantModelConstructible (coefficientHeartRingObj Λ) T M) :
    ∃ R : T.FiniteLocallyClosedStratification, ∀ a : Fin R.n,
      restrictionLisse (coefficientHeartRingObj Λ) (R.immersion a) M := by
  obtain ⟨R, hR⟩ := (((coefficientHeart_closure ell Λ hΛ).2 T).2.2.2.2.2.2 M).mp hM
  exact ⟨R, fun a ↦ (restrictionLisse_iff _ _ _).mpr (hR a)⟩

private theorem lisse_stratification (ell : ℕ) [Fact ell.Prime]
    {T : Scheme.{u}} [IsNoetherian T]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T M) :
    ∃ R : T.FiniteLocallyClosedStratification, ∀ a : Fin R.n,
      restrictionLisse (Profinite.padicAlgClRingObj ell) (R.immersion a) M := by
  exact coefficient_lisse_stratification ell (Profinite.padicAlgClCondensedRing ell)
    (Or.inr rfl) M hM

private theorem noetherian_fibre_finite (ell : ℕ) [Fact ell.Prime]
    {T : Scheme.{u}} [IsNoetherian T]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T M)
    {K : Type u} [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ T) :
    FiniteDimensional (PadicAlgCl ell) ((fibre ell x).obj M) := by
  obtain ⟨R, hR⟩ := lisse_stratification ell M hM
  let z := x (IsLocalRing.closedPoint K)
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp
    (R.iUnion_stratum_eq_univ ▸ Set.mem_univ z)
  rw [← R.range_immersion a] at ha
  have : IsImmersion (R.immersion a) := R.isImmersion a
  obtain ⟨y, hy⟩ := Scheme.exists_comp_eq_of_mem_range_of_isField
    (R.immersion a) (Field.toIsField K) x (IsLocalRing.closedPoint K) ha
  have := lisse_fibre_finite ell y _ ((restrictionLisse_iff _ _ _).mp (hR a))
  have h : FiniteDimensional (PadicAlgCl ell)
      ((fibre ell (y ≫ R.immersion a)).obj M) :=
    Module.Finite.equiv (fibre_comp_iso ell (R.immersion a) y M).toLinearEquiv.symm
  subst x
  exact h

private theorem noetherian_zero (ell : ℕ) [Fact ell.Prime]
    {T : Scheme.{u}} [IsNoetherian T]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T M)
    (hz : ∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ T),
      IsZero ((fibre ell x).obj M)) : IsZero M := by
  obtain ⟨R, hR⟩ := lisse_stratification ell M hM
  apply coefficientModuleZero (Profinite.padicAlgClRingObj ell) R M
  intro a
  apply lisse_zero ell _ ((restrictionLisse_iff _ _ _).mp (hR a))
  intro K _ _ x
  exact fibre_comp_zero ell (R.immersion a) x M (hz K (x ≫ R.immersion a))

private theorem constructible_fibre_finite (ell : ℕ) [Fact ell.Prime]
    {T : Scheme.{u}} [IsLocallyNoetherian T]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T M)
    {K : Type u} [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ T) :
    FiniteDimensional (PadicAlgCl ell) ((fibre ell x).obj M) := by
  classical
  by_cases hT : CompactSpace T ∧ QuasiSeparatedSpace T
  · have : CompactSpace T := hT.1
    have : IsNoetherian T := {}
    exact noetherian_fibre_finite ell M hM x
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : T.Opens)) (x := x (IsLocalRing.closedPoint K)) (by simp)
  have : IsAffine U.toScheme := hU
  have : IsNoetherian U.toScheme := {}
  obtain ⟨y, hy⟩ := Scheme.exists_comp_eq_of_mem_range_of_isField U.ι
    (Field.toIsField K) x (IsLocalRing.closedPoint K) (by simpa using hx)
  have hcons := (noetherian_constructible_iff ell U.toScheme _).mpr
    (constructible_affine ell T hT M hM U hU)
  have := noetherian_fibre_finite ell _ hcons y
  have h : FiniteDimensional (PadicAlgCl ell) ((fibre ell (y ≫ U.ι)).obj M) :=
    Module.Finite.equiv (fibre_comp_iso ell U.ι y M).toLinearEquiv.symm
  subst x
  exact h

private theorem constructible_zero (ell : ℕ) [Fact ell.Prime]
    {T : Scheme.{u}} [IsLocallyNoetherian T]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T M)
    (hz : ∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ T),
      IsZero ((fibre ell x).obj M)) : IsZero M := by
  classical
  by_cases hT : CompactSpace T ∧ QuasiSeparatedSpace T
  · have : CompactSpace T := hT.1
    have : IsNoetherian T := {}
    exact noetherian_zero ell M hM hz
  apply open_family_zero (Profinite.padicAlgClRingObj ell) (fun i : T.affineOpens ↦ i.1)
    (by
      apply top_unique
      intro x _
      obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset
        (U := (⊤ : T.Opens)) (x := x) (by simp)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hx⟩) M
  intro i
  apply (restrictionZero_iff _ _ _).mpr
  have : IsAffine i.1.toScheme := i.2
  have : IsNoetherian i.1.toScheme := {}
  apply noetherian_zero ell _
  · exact (noetherian_constructible_iff ell i.1.toScheme _).mpr
      (constructible_affine ell T hT M hM i.1 i.2)
  · intro K _ _ x
    exact fibre_comp_zero ell i.1.ι x M (hz K (x ≫ i.1.ι))

universe u₁ u₂ v₁

private structure ExactFamilyTests {C : Type v} [Category.{w} C] [Abelian C]
    (P : ObjectProperty C) {I : Type u₁} {D : I → Type u₂}
    [∀ i, Category.{v₁} (D i)] [∀ i, Abelian (D i)] (G : ∀ i, C ⥤ D i)
    [∀ i, (G i).Additive] : Prop where
  conservative : ∀ {M N : C} (f : M ⟶ N), P M → P N →
    (∀ i, IsIso ((G i).map f)) → IsIso f
  zero : ∀ {M N : C} (f : M ⟶ N), P M → P N →
    (f = 0 ↔ ∀ i, (G i).map f = 0)
  shortExact : ∀ S : ShortComplex C, P S.X₁ → P S.X₂ → P S.X₃ →
    (S.ShortExact ↔ ∀ i, (S.map (G i)).ShortExact)

private theorem exact_family_tests {C : Type v} [Category.{w} C] [Abelian C]
    (P : ObjectProperty C)
    [P.IsClosedUnderLimitsOfShape WalkingParallelPair]
    [P.IsClosedUnderColimitsOfShape WalkingParallelPair]
    {I : Type u₁} {D : I → Type u₂}
    [∀ i, Category.{v₁} (D i)] [∀ i, Abelian (D i)] (G : ∀ i, C ⥤ D i)
    [∀ i, (G i).Additive]
    [∀ i, PreservesFiniteLimits (G i)] [∀ i, PreservesFiniteColimits (G i)]
    (hz : ∀ M, P M → (∀ i, IsZero ((G i).obj M)) → IsZero M) :
    ExactFamilyTests P G := by
  have hk {M N : C} (f : M ⟶ N) (hM : P M) (hN : P N) : P (kernel f) :=
    P.prop_of_isLimit
      (c := KernelFork.ofι (kernel.ι f) (kernel.condition f)) (kernelIsKernel f)
      (by rintro (_ | _) <;> assumption)
  have hc {M N : C} (f : M ⟶ N) (hM : P M) (hN : P N) : P (cokernel f) :=
    P.prop_of_isColimit
      (c := CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)) (cokernelIsCokernel f)
      (by rintro (_ | _) <;> assumption)
  have hm {M N : C} (f : M ⟶ N) (hM : P M) (hN : P N)
      (hf : ∀ i, Mono ((G i).map f)) : Mono f := by
    apply Preadditive.mono_of_isZero_kernel f
    apply hz _ (hk f hM hN)
    intro i
    have := hf i
    exact (isZero_kernel_of_mono ((G i).map f)).of_iso (PreservesKernel.iso (G i) f)
  have he {M N : C} (f : M ⟶ N) (hM : P M) (hN : P N)
      (hf : ∀ i, Epi ((G i).map f)) : Epi f := by
    apply Preadditive.epi_of_isZero_cokernel f
    apply hz _ (hc f hM hN)
    intro i
    have := hf i
    exact (isZero_cokernel_of_epi ((G i).map f)).of_iso (PreservesCokernel.iso (G i) f)
  have hzero {M N : C} (f : M ⟶ N) (hM : P M) (hN : P N)
      (hf : ∀ i, (G i).map f = 0) : f = 0 := by
    have hi : IsZero (Abelian.image f) := by
      apply hz _ (hk (cokernel.π f) hN (hc f hM hN))
      intro i
      have hzi : IsZero (Abelian.image ((G i).map f)) := by
        have : IsIso (cokernel.π ((G i).map f)) :=
          CokernelCofork.IsColimit.isIso_π
            (CokernelCofork.ofπ (cokernel.π ((G i).map f)) (cokernel.condition _))
            (cokernelIsCokernel _) (hf i)
        exact isZero_kernel_of_mono _
      exact hzi.of_iso (Abelian.PreservesImage.iso (G i) f)
    rw [← Abelian.image.fac f, hi.eq_of_tgt (Abelian.factorThruImage f) 0, zero_comp]
  constructor
  · intro M N f hM hN hf
    have := hm f hM hN (fun i ↦ by have := hf i; infer_instance)
    have := he f hM hN (fun i ↦ by have := hf i; infer_instance)
    exact isIso_of_mono_of_epi f
  · intro M N f hM hN
    exact ⟨by rintro rfl i; exact (G i).map_zero _ _, hzero f hM hN⟩
  · intro S h₁ h₂ h₃
    constructor
    · intro h i
      exact h.map_of_exact (G i)
    · intro h
      have := hm S.f h₁ h₂ (fun i ↦ (h i).mono_f)
      have := he S.g h₂ h₃ (fun i ↦ (h i).epi_g)
      refine { exact := ?_, mono_f := inferInstance, epi_g := inferInstance }
      rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
      apply hzero _ (hk S.g h₂ h₃) (hc S.f h₁ h₂)
      intro i
      let F := G i
      have hex := (h i).exact
      rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero] at hex
      obtain ⟨k, hk⟩ := kernel.lift' (F.map S.g) (F.map (kernel.ι S.g))
        (by rw [← F.map_comp, kernel.condition, Functor.map_zero])
      obtain ⟨l, hl⟩ := cokernel.desc' (F.map S.f) (F.map (cokernel.π S.f))
        (by rw [← F.map_comp, cokernel.condition, Functor.map_zero])
      change kernel.ι (F.map S.g) ≫ cokernel.π (F.map S.f) = 0 at hex
      rw [F.map_comp, ← hl, ← hk, Category.assoc, reassoc_of% hex, zero_comp, comp_zero]

private structure GeometricIndex (T : Scheme.{u}) where
  K : Type u
  [instField : Field K]
  [instAlgClosed : IsAlgClosed K]
  x : Spec (.of K) ⟶ T

attribute [instance] GeometricIndex.instField GeometricIndex.instAlgClosed

private def fibreZero (ell : ℕ) [Fact ell.Prime]
    {T : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T)) : Prop :=
  IsZero ((fibre ell x).obj M)

private theorem fibreZero_iff (ell : ℕ) [Fact ell.Prime]
    {T : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T)) :
    fibreZero ell x M ↔ IsZero ((fibre ell x).obj M) := Iff.rfl

private theorem indexed_constructible_zero (ell : ℕ) [Fact ell.Prime]
    (T : Scheme.{u}) [IsLocallyNoetherian T]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T M)
    (hz : ∀ i : GeometricIndex T, fibreZero ell i.x M) : IsZero M := by
  apply constructible_zero ell M hM
  intro K _ _ x
  exact (fibreZero_iff ell x M).mp (hz
    { K := K
      instField := inferInstance
      instAlgClosed := inferInstance
      x := x })

private theorem geometric_family_zero (ell : ℕ) [Fact ell.Prime]
    (T : Scheme.{u}) [IsLocallyNoetherian T]
    {C : Type v} [Category.{w} C] [Abelian C]
    (F : C ⥤ Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
    [F.Additive] [F.Faithful] (M : C)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T (F.obj M))
    (hz : ∀ i : GeometricIndex T, IsZero ((F ⋙ fibre ell i.x).obj M)) : IsZero M := by
  have hzero : IsZero (F.obj M) := indexed_constructible_zero ell T _ hM
    (fun i ↦ (fibreZero_iff _ _ _).mpr (hz i))
  rw [IsZero.iff_id_eq_zero]
  apply F.map_injective
  simpa only [F.map_zero, F.map_id] using hzero.eq_of_src (F.map (𝟙 M)) 0

private theorem geometric_family_tests (ell : ℕ) [Fact ell.Prime]
    (T : Scheme.{u}) [IsLocallyNoetherian T]
    {C : Type v} [Category.{w} C] [Abelian C]
    (F : C ⥤ Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
    [F.Additive] [F.Faithful] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    ExactFamilyTests
      (ObjectProperty.inverseImage
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T) F)
      (fun i : GeometricIndex T ↦ F ⋙ fibre ell i.x) := by
  let Q : ObjectProperty _ := IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T
  let P : ObjectProperty C := Q.inverseImage F
  have : Q.IsClosedUnderLimitsOfShape WalkingParallelPair :=
    (local_closure ell T WalkingParallelPair).1
  have : Q.IsClosedUnderColimitsOfShape WalkingParallelPair :=
    (local_closure ell T WalkingParallelPair).2
  let G (i : GeometricIndex T) := F ⋙ fibre ell i.x
  exact exact_family_tests P G (fun M hM hz ↦ geometric_family_zero ell T F M hM hz)

private theorem geometric_assertions (ell : ℕ) [Fact ell.Prime]
    (T : Scheme.{u}) [IsLocallyNoetherian T]
    {C : Type v} [Category.{w} C] [Abelian C]
    (F : C ⥤ Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) T))
    [F.Additive] [F.Faithful] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    Assertions ell T F := by
  let P : ObjectProperty C := fun M ↦
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T (F.obj M)
  let G (i : GeometricIndex T) := F ⋙ fibre ell i.x
  have ht : ExactFamilyTests P G := geometric_family_tests ell T F
  constructor
  · intro K _ _ x M hM
    exact constructible_fibre_finite ell (F.obj M) hM x
  · intro K _ _ x
    have := (constructible_inclusion_exact ell T F).1
    have := (constructible_inclusion_exact ell T F).2
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · intro M N f hM hN hf
    exact ht.conservative f hM hN (fun i ↦ hf i.K i.x)
  · intro M N f hM hN
    constructor
    · rintro rfl K _ _ x
      exact (F ⋙ fibre ell x).map_zero _ _
    · intro hf
      exact (ht.zero f hM hN).mpr (fun i ↦ hf i.K i.x)
  · intro S h₁ h₂ h₃
    constructor
    · intro h K _ _ x
      have he := h.map_of_exact (F ⋙ fibre ell x)
      exact ⟨he.moduleCat_injective_f,
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he.exact,
        he.moduleCat_surjective_g⟩
    · intro h
      apply (ht.shortExact S h₁ h₂ h₃).mpr
      intro i
      obtain ⟨hi, he, hs⟩ := h i.K i.x
      exact
        { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr he
          mono_f := (ModuleCat.mono_iff_injective _).mpr hi
          epi_g := (ModuleCat.epi_iff_surjective _).mpr hs }

private theorem open_family_tests
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {T : Scheme.{u}} {I : Type u} (U : I → T.Opens) (hU : (⨆ i, U i) = ⊤)
    {C : Type v} [Category.{w} C] [Abelian C]
    (F : C ⥤ Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    [F.Additive] [F.Faithful] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    ExactFamilyTests (⊤ : ObjectProperty C)
      (fun i ↦ F ⋙ CondensedRing.upperStar Λ (U i).ι) := by
  apply exact_family_tests
  intro M _ hzero
  have hz : IsZero (F.obj M) := open_family_zero Λ U hU (F.obj M)
    (fun i ↦ (restrictionZero_iff _ _ _).mpr (hzero i))
  rw [IsZero.iff_id_eq_zero]
  apply F.map_injective
  simpa only [F.map_id, F.map_zero] using hz.eq_of_src (F.map (𝟙 M)) 0

private theorem affine_assertions (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (T₀ : Over (Spec (.of D.k₀)))
    {C : Type v} [Category.{w} C] [Abelian C]
    (F : C ⥤ Mod (Sheaf (Scheme.ProEt.topology
      (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell)
        (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))))
    [F.Additive] [F.Faithful] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    AffineAssertions D ell T₀ F := by
  let T := pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  let π : T ⟶ T₀.left := pullback.fst _ _
  have ht (I : Type u) (U : I → T₀.left.Opens) (hU : (⨆ i, U i) = ⊤) :
      ExactFamilyTests (⊤ : ObjectProperty C)
        (fun i ↦ F ⋙ affineRestriction D ell T₀ (U i)) := by
    exact open_family_tests (Profinite.padicAlgClRingObj ell) (fun i ↦ π ⁻¹ᵁ U i)
      (by
        apply top_unique
        intro x _
        have hx : π x ∈ ⨆ i, U i := by rw [hU]; trivial
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩) F
  constructor
  · intro I U _ hU M N f _ _
    exact (ht I U hU).zero f trivial trivial
  · intro I U _ hU S _ _ _
    exact (ht I U hU).shortExact S trivial trivial trivial

/-- Constructible condensed geometric fibres are finite-dimensional, exact, jointly
conservative and detect zero morphisms and short exact sequences, also for Weil modules
and on every affine cover of the model.
Source: Bhatt--Scholze, Definitions 6.8.3 and 6.8.6, Lemma 6.8.7; current blueprint,
p-dl-a1-exact.proof.md, Steps 1 and 5 (blueprint: lem-dl-a1-condensed-fibres-exact).

Proof plan (the eight steps of the node):
1. On a finite-type affine patch, finite-type base change gives a Noetherian scheme.
   coefficientHeart gives closure under kernels, cokernels and extensions and a finite
   lisse stratification. Cartesian coefficients and exact restriction make this closure
   local, giving the same result for locally constructible carriers.
2. Cartesian coefficients make module inverse image exact. Geometric-field pro-etale
   evaluation is exact: covers split, module kernels are sectionwise, and cokernels are
   preserved. Constant sections identify the scalar ring with PadicAlgCl ell.
3. Factor a geometric point through its locally closed stratum. Pull a finite-free local
   model through the base-changed pro-etale cover, which has a section over the geometric
   field. Composition of module pullbacks identifies the fibre with a finite power of Omega.
4. If all fibres vanish, on every nonempty local trivializing member choose a geometric
   point. Its fibre forces the finite rank to be zero. Empty members have zero restriction.
   Underlying abelian-sheaf restriction detects isomorphisms on pro-etale covers.
   Scalar transport and module forgetting give the same underived module criterion,
   so each lisse stratum is zero.
5. Finite-stratum zero detection makes each affine restriction zero. Zariski covers
   are pro-etale, so the same cover criterion gives M = 0.
6. Exact functors preserve kernels, cokernels and images. Apply fibrewise zero detection
   to the kernel and cokernel for conservativity, and to the image for the zero test.
   Exactness of a short complex is vanishing of the map from the kernel of its second
   arrow to the cokernel of its first. The zero-morphism criterion detects this map;
   the kernel and cokernel tests additionally give the monomorphism and epimorphism.
7. Exact restriction and the cover criterion detect zero objects on any open cover.
   Apply Step 6 to these restriction functors to obtain both affine assertions.
8. FixedPairCreatedAbelianStructure gives exact faithful conservative forgetting from
   degree-zero Weil pairs, creating kernels and cokernels and reflecting exactness. The
   constructible carriers are closed under these operations by Step 1. Apply Steps 2--7
   through this forgetful functor. No conservativity of geometric evaluation on arbitrary
   module sheaves is used. -/
theorem condensed_fibres_exact
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hell : ell ≠ D.p) (_iota : PadicAlgCl ell →+* ℂ)
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] :
    Assertions ell
      (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      (𝟭 (Mod
        (Sheaf (Scheme.ProEt.topology
          (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ell)
          (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))))) ∧
    AffineAssertions D ell T₀
      (𝟭 (Mod
        (Sheaf (Scheme.ProEt.topology
          (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ell)
          (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))))) ∧
    Assertions ell
      (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      (CategoryTheory.Endofunctor.IsoAlgebra.forget
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
          (CondensedRing.StrictWeil.modelFrobenius D T₀).hom)) ∧
    AffineAssertions D ell T₀
      (CategoryTheory.Endofunctor.IsoAlgebra.forget
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
          (CondensedRing.StrictWeil.modelFrobenius D T₀).hom)) := by
  have : IsLocallyNoetherian
      (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) :=
    inferInstance
  exact ⟨geometric_assertions ell _ _, affine_assertions D ell T₀ _,
    geometric_assertions ell _ _, affine_assertions D ell T₀ _⟩

end AlgebraicGeometry.ProEtale.DeligneLaumonFibres
