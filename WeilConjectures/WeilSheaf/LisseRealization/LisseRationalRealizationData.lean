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

/-- The recorded coefficient unit. Source: BS 6.8.15
(blueprint: def-real-lisse-realization-data). -/
abbrev unit (X : Base D l hl) := pullbackTensorRationalUnit l E X.scheme

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

attribute [instance] At.additive

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]

variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

end WeilConjectures.LisseRealization
