/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SmoothPurity.Sf.SfConstructibleHeart
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalDerivedRealization
public import WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension
public import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonScalarExtension
public import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonNatural
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.AlgebraicGeometry.PointAutomorphismRestrictionNatural
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientComplexRationalization
public import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientPullbackSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
import WeilConjectures.SixFunctors.Constructible.ConstructibleTensorCompletion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
import WeilConjectures.WeilSheaf.Ordinary.OrdinaryCompletedIntegralPullback
import WeilConjectures.SixFunctors.Supporting.ConstantCoefficientScalarNormalization
import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.AlgebraicGeometry.Integral.IntegralConstructibleBoundedBelowCompactness
import WeilConjectures.AlgebraicGeometry.Lisse.LisseEConstructibleIntegralLattice
import WeilConjectures.AlgebraicGeometry.LisseLatticeEtaleLocal
import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationDerivedHom
import WeilConjectures.SmoothPurity.Point.PointFibreEquivalence
import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization

/-! # Normalized realization of the rational lisse heart

Source: Bhatt--Scholze, Lemma 6.8.2, Definition 6.8.3, Proposition 6.8.4(1),(4),(6),
Proposition 6.8.14(2), Remark 6.8.15, pp. 58--62
(blueprint: def-real-lisse-realization-data).

The continuous coefficient presentation below is identified with the specified completion
by every residue projection, and with its sheaf localization by the localization unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme MonoidalCategory
open scoped TensorProduct MonoidalCategory
namespace WeilConjectures.LisseRealization

/-- A finite-type geometric-base scheme, with no separation condition. Morphisms between
these bases will be arbitrary scheme morphisms. Source: BS 6.8.14 and Remark 6.8.15
(blueprint: def-real-lisse-realization-data). -/
structure Base (D : FiniteFieldDatum.{u}) (l : ℕ) (hl : l ≠ D.p) where
  scheme : Scheme.{u}
  [over : scheme.Over (Spec (.of D.k))]
  [finiteType : LocallyOfFiniteType (scheme ↘ Spec (.of D.k))]
  [quasiCompact : QuasiCompact (scheme ↘ Spec (.of D.k))]

attribute [instance] Base.over Base.finiteType Base.quasiCompact

/-- The coefficient prime is a unit in each residue field. This is inherited from the
finite-field base, so supplies no extra hypothesis. Source: BS 6.8.14
(blueprint: def-real-lisse-realization-data). -/
@[instance_reducible]
def baseInvertible (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (X : Base D l hl) (x : X.scheme) :
    Invertible (l : X.scheme.residueField x) := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (f := D.a)
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  have hunit : IsUnit (l : D.k₀) :=
    (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) hl.symm).isUnit
  let g := (X.scheme ↘ Spec (.of D.k)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have h : IsUnit (l : X.scheme.residueField x) := by
    simpa only [map_natCast] using hunit.map
      ((Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫ g.appTop ≫
        X.scheme.Γevaluation x).hom
  exact h.invertible

/-- The raw source category. Source: BS 6.8.14
(blueprint: def-real-lisse-realization-data). -/
abbrev Raw (X : Base D l hl) := sfRationalConstructibleCategory l E X.scheme

attribute [instance] baseInvertible

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ordinary continuous/localized rational module category. Source: BS 6.8.2
(blueprint: def-real-lisse-realization-data). -/
abbrev Modules (X : Base D l hl) := pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)

/-- The exact recorded completed rational tensor. Source: BS 6.8.15
(blueprint: def-real-lisse-realization-data). -/
abbrev tensor (X : Base D l hl) := rationalDerivedTensor l E X.scheme

/-- The recorded coefficient unit. Source: BS 6.8.15
(blueprint: def-real-lisse-realization-data). -/
abbrev unit (X : Base D l hl) := pullbackTensorRationalUnit l E X.scheme

/-- The recorded pullback, for arbitrary scheme maps. Source: BS 6.8.15
(blueprint: def-real-lisse-realization-data). -/
abbrev pull {X Y : Base D l hl} (f : X.scheme ⟶ Y.scheme) :=
  rationalDerivedPullback l E f

/-- The actual rational coefficient map, adjunct to precomposition of functions.
Source: BS 6.8.15 (blueprint: def-real-lisse-realization-data). -/
def coefficientPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (adicTowerInverseImage f).obj (rationalCoefficientSheaf l Y E) ⟶
      rationalCoefficientSheaf l X E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientPullback (ULift.{u + 1, u} E) f

/-- Ordinary module inverse image, not completed inverse image. Source: BS 6.8.15
(blueprint: def-real-lisse-realization-data). -/
abbrev ordinaryPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ContinuousRational.modulePull f (coefficientPull l E f)

/-- Normalized derived realization and its restriction to the lisse heart. All comparison
data are part of the conclusion, never additional input. Source: BS 6.8.2 and 6.8.14
(blueprint: def-real-lisse-realization-data). -/
structure At (X : Base D l hl) where
  completion : completedIntegralCommRingSheafUnrestricted l E X.scheme ≅
    AlgebraicGeometry.Scheme.integralCoefficientSheaf l X.scheme E
  completion_residues : ∀ n : ℕ,
    completion.hom ≫ continuousCoefficientReduction l E X.scheme n =
      completedIntegralCommRingProjectionUnrestricted l E X.scheme n ≫
        (discreteContinuousCoefficientIso X.scheme).hom.app
          (AlgebraicGeometry.Scheme.finiteCoefficientRing l E n)
  localization : integralCoefficientLocalization l X.scheme E ≅
    rationalCoefficientSheaf l X.scheme E
  localization_unit : integralCoefficientLocalizationNormalized l E X.scheme localization.hom
  J : Raw D l hl E X ⥤ DerivedCategory (Modules D l hl E X)
  [additive : J.Additive]
  integral : sfRationalConstructibleLocalization l E X.scheme ⋙ J ≅
    (sfIntegralConstructible l E X.scheme).ι ⋙
      pbcDerivedExtend (completion.hom ≫ integralRationalCoefficientMap l E X.scheme)
  fractions : ∀ (K L : sfIntegralConstructibleCategory l E X.scheme)
      (f : K ⟶ L) (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
    J.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) =
      sfRationalCoefficientEquiv l E a •
        J.map ((sfRationalConstructibleLocalization l E X.scheme).map f)
  degree_zero : ∀ (K : Raw D l hl E X), Lisse D l hl E X K →
    Nonempty (J.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((DerivedCategory.homologyFunctor _ 0).obj (J.obj K)))
  fully_faithful : ∀ (K L : Raw D l hl E X),
    Lisse D l hl E X K → Lisse D l hl E X L →
      Function.Bijective ((J ⋙ DerivedCategory.homologyFunctor _ 0).map :
        (K ⟶ L) → _)
  image : ∀ M : Modules D l hl E X, M.IsFiniteLocallyFree ↔
    ∃ K : Raw D l hl E X, Lisse D l hl E X K ∧
      Nonempty ((DerivedCategory.homologyFunctor _ 0).obj (J.obj K) ≅ M)

/-- The sheaf realization is the actual degree-zero cohomology of scalar extension.
Source: BS 6.8.14 (blueprint: def-real-lisse-realization-data). -/
def At.sheaf {X : Base D l hl} (a : At D l hl E X) :=
  a.J ⋙ DerivedCategory.homologyFunctor _ 0

/-- Pullback comparison to actual ordinary module inverse image, together with its
integral balanced-tensor normalization. Source: BS 6.8.15
(blueprint: def-real-lisse-realization-data). -/
structure Along {X Y : Base D l hl} (f : X.scheme ⟶ Y.scheme)
    (aX : At D l hl E X) (aY : At D l hl E Y) where
  preserves : ∀ K : Raw D l hl E Y, Lisse D l hl E Y K →
    Lisse D l hl E X ((pull D l hl E f).obj K)
  comparison : ∀ K : Raw D l hl E Y, Lisse D l hl E Y K →
    ((aX.sheaf D l hl E).obj ((pull D l hl E f).obj K) ≅
      (ordinaryPull l E f).obj ((aY.sheaf D l hl E).obj K))
  naturality : ∀ (K L : Raw D l hl E Y)
    (hK : Lisse D l hl E Y K) (hL : Lisse D l hl E Y L) (g : K ⟶ L),
    (aX.sheaf D l hl E).map ((pull D l hl E f).map g) ≫ (comparison L hL).hom =
      (comparison K hK).hom ≫ (ordinaryPull l E f).map ((aY.sheaf D l hl E).map g)
  balance : pbcExtend (aY.completion.hom ≫ integralRationalCoefficientMap l E Y.scheme) ⋙
      ordinaryPull l E f ≅
    ContinuousRational.modulePull f
      ((adicTowerInverseImage f).map (purCoefficientIso l E Y.scheme).inv ≫
        AlgebraicGeometry.Scheme.completedCoefficientMap f (pbcIntegralDatum l E) ≫
          (purCoefficientIso l E X.scheme).hom) ⋙
      pbcExtend (aX.completion.hom ≫ integralRationalCoefficientMap l E X.scheme)

/-- Composition comparison on the ordinary pullbacks, fixed by the images of tensor
unit sections. Source: BS 6.8.15 (blueprint: def-real-lisse-realization-data). -/
structure Composition {X Y Z : Base D l hl} (f : X.scheme ⟶ Y.scheme)
    (g : Z.scheme ⟶ X.scheme) (aX : At D l hl E X) (aY : At D l hl E Y)
    (aZ : At D l hl E Z) (af : Along D l hl E f aX aY) (ag : Along D l hl E g aZ aX)
    (ac : Along D l hl E (g ≫ f) aZ aY) where
  ordinary : ordinaryPull l E (g ≫ f) ≅ ordinaryPull l E f ⋙ ordinaryPull l E g
  sections : ∀ (M : Modules D l hl E Y) (U : Y.scheme.ProEt)
    (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (g ≫ f)).obj U))
        (ContinuousRational.moduleUnit (g ≫ f) (coefficientPull l E (g ≫ f)) M U m) =
      (((ordinaryPull l E g).obj ((ordinaryPull l E f).obj M)).val.map
        ((MorphismProperty.Over.pullbackComp g f).hom.app U).op)
          (ContinuousRational.moduleUnit g (coefficientPull l E g)
            ((ordinaryPull l E f).obj M) ((proEtaleBaseChange f).obj U)
            (ContinuousRational.moduleUnit f (coefficientPull l E f) M U m))
  compatibility : ∀ (K : Raw D l hl E Y) (hK : Lisse D l hl E Y K),
    (ac.comparison K hK).hom ≫ ordinary.hom.app ((aY.sheaf D l hl E).obj K) =
      (aZ.sheaf D l hl E).map (pullbackTensorRationalComposition l E f g K).hom ≫
        (ag.comparison _ (af.preserves K hK)).hom ≫
          (ordinaryPull l E g).map (af.comparison K hK).hom

/-- Identity comparison, fixed by the identity base-change projection.
Source: BS 6.8.15 (blueprint: def-real-lisse-realization-data). -/
structure Identity (X : Base D l hl) (a : At D l hl E X)
    (ai : Along D l hl E (𝟙 X.scheme) a a) where
  ordinary : ordinaryPull l E (𝟙 X.scheme) ≅ 𝟭 _
  sections : ∀ (M : Modules D l hl E X) (U : X.scheme.ProEt) (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 X.scheme)).obj U))
      (ContinuousRational.moduleUnit (𝟙 X.scheme) (coefficientPull l E (𝟙 X.scheme)) M U m) =
        M.val.map ((MorphismProperty.Over.pullbackId _ _ X.scheme).hom.app U).op m
  raw : pull D l hl E (𝟙 X.scheme) ≅ 𝟭 _
  compatibility : ∀ (K : Raw D l hl E X) (hK : Lisse D l hl E X K),
    (ai.comparison K hK).hom ≫ ordinary.hom.app ((a.sheaf D l hl E).obj K) =
      (a.sheaf D l hl E).map (raw.hom.app K)

/-- Finite scalar extension with the normalized balanced map, not an arbitrary equivalence.
Source: BS 6.8.14--6.8.15 (blueprint: def-real-lisse-realization-data). -/
structure FieldChange (i : E →ₐ[ℚ_[l]] F) (X : Base D l hl)
    (aE : At D l hl E X) (aF : At D l hl F X) where
  coefficient : rationalCoefficientSheaf l X.scheme E ⟶ rationalCoefficientSheaf l X.scheme F
  normalized : ∀ (U : X.scheme.ProEtᵒᵖ)
    (s : (rationalCoefficientSheaf l X.scheme E).obj.obj U) (x : U.unop.left),
    rationalCoefficientValue l F X.scheme U (coefficient.hom.app U s) x =
      i (rationalCoefficientValue l E X.scheme U s x)
  preserves : ∀ (K : Raw D l hl E X), Lisse D l hl E X K →
    Lisse D l hl F X ((sfRationalScalarExtension l E X.scheme D.p hl F i).obj K)
  comparison : ∀ (K : Raw D l hl E X), Lisse D l hl E X K →
    ((aF.sheaf D l hl F).obj
        ((sfRationalScalarExtension l E X.scheme D.p hl F i).obj K) ≅
      (pbcExtend coefficient).obj ((aE.sheaf D l hl E).obj K))
  naturality : ∀ (K L : Raw D l hl E X)
    (hK : Lisse D l hl E X K) (hL : Lisse D l hl E X L) (f : K ⟶ L),
    (aF.sheaf D l hl F).map
        ((sfRationalScalarExtension l E X.scheme D.p hl F i).map f) ≫
      (comparison L hL).hom = (comparison K hK).hom ≫
        (pbcExtend coefficient).map ((aE.sheaf D l hl E).map f)

/-- The rational point as a finite-type base, with its identity structure map.
Source: BS 6.8 and the blueprint geometric point convention
(blueprint: def-real-lisse-realization-data). -/
def point : Base D l hl := ⟨Spec (.of D.k)⟩

/-- Constants acting on ordinary sections at the geometric point. Source: BS 6.8.1
(blueprint: def-real-lisse-realization-data). -/
def pointConstants : E →+*
    (rationalCoefficientSheaf l (Spec (.of D.k)) E).obj.obj
      (op (ProEt.mk (𝟙 (Spec (.of D.k))))) :=
  { toFun := fun a ↦ (ContinuousRational.scalarSections l E (Spec (.of D.k)) a).val _
    map_one' := rfl
    map_mul' := fun _ _ ↦ rfl
    map_zero' := rfl
    map_add' := fun _ _ ↦ rfl }

/-- Ordinary sheaf sections, with coefficients restricted along constant rational functions.
Source: BS 6.8.1 (blueprint: def-real-lisse-realization-data). -/
def sections : Modules D l hl E (point D l hl) ⥤ ModuleCat.{u + 1} E :=
  AlgebraicGeometry.ProEtale.pointModuleSections D.k
    (rationalCoefficientSheaf l (Spec (.of D.k)) E) ⋙
      ModuleCat.restrictScalars (pointConstants D l E)

/-- The actual recorded point fibre, lifted only in carrier size. Source: blueprint order 1509
(blueprint: def-real-lisse-realization-data). -/
def fibre : Raw D l hl E (point D l hl) ⥤ ModuleCat.{u + 1} E :=
  pointRationalFibre D l hl E ⋙ (DerivedCategory.pointFiniteDimensional E).ι ⋙
    DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) 0 ⋙ ModuleCat.uliftFunctor.{u + 1, u} E

/-- Coefficient extension commutes with pullback through the same balanced section map.
Source: BS 6.8.15 (blueprint: def-real-lisse-realization-data). -/
structure Mixed (i : E →ₐ[ℚ_[l]] F) {X Y : Base D l hl} (f : X.scheme ⟶ Y.scheme)
    (aXE : At D l hl E X) (aYE : At D l hl E Y)
    (aXF : At D l hl F X) (aYF : At D l hl F Y)
    (afE : Along D l hl E f aXE aYE) (afF : Along D l hl F f aXF aYF)
    (bX : FieldChange D l hl E F i X aXE aXF)
    (bY : FieldChange D l hl E F i Y aYE aYF) where
  ordinary : pbcExtend bY.coefficient ⋙ ordinaryPull l F f ≅
    ordinaryPull l E f ⋙ pbcExtend bX.coefficient
  sections : ∀ (M : Modules D l hl E Y) (U : Y.scheme.ProEt)
    (b : (rationalCoefficientSheaf l Y.scheme F).obj.obj (op U)) (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
      (ContinuousRational.moduleUnit f (coefficientPull l F f)
        ((pbcExtend bY.coefficient).obj M) U (pbcTensorSection bY.coefficient M (op U) b m)) =
      pbcTensorSection bX.coefficient ((ordinaryPull l E f).obj M)
        (op ((proEtaleBaseChange f).obj U))
        (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
          (coefficientPull l F f)).hom.app (op U) b)
        (ContinuousRational.moduleUnit f (coefficientPull l E f) M U m)
  compatibility : ∀ (K : Raw D l hl E Y) (hK : Lisse D l hl E Y K),
    (aXF.sheaf D l hl F).map
        ((rationalPullbackScalarComparison l E F i f).hom.app K) ≫
        (afF.comparison _ (bY.preserves K hK)).hom ≫
        (ordinaryPull l F f).map (bY.comparison K hK).hom ≫
        ordinary.hom.app ((aYE.sheaf D l hl E).obj K) =
      (bX.comparison _ (afE.preserves K hK)).hom ≫
        (pbcExtend bX.coefficient).map (afE.comparison K hK).hom

attribute [instance] At.additive

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]

variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

end WeilConjectures.LisseRealization
