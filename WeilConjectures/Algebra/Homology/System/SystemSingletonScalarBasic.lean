/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos
public import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedExtension
public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtension
public import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedEvaluation
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence

/-! # Singleton extension and arbitrary coefficient change

Source: Stacks 0D6D, lemma-derived-pullback-composition, and Zheng, Construction 4.1.
The singleton functor is an extension left adjoint, not a geometric inverse image.
(blueprint: def-pur-system-singleton-scalar-comparisons)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- The coefficient morphism on the vertical sequence site, with component a_j.
Source: Stacks 03EK; Zheng 4.1
(blueprint: def-pur-system-singleton-scalar-comparisons). -/
def singletonSequenceRingMap {B D : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : B ⟶ D) :
    systemSequenceRing B ⟶ systemSequenceRing D :=
  ⟨Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := C)).functor
    (Functor.uncurry.map (Functor.whiskerRight a (sheafToPresheaf J CommRingCat.{w})))⟩

variable (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- The existing sequence-equivalence additivity instance, with the projection exposed.
Source: Zheng 4.1 (blueprint: def-pur-system-singleton-scalar-comparisons). -/
instance singletonSequenceFunctorAdditive :
    (strictSystemSequenceEquivalence B).functor.Additive := strictSystemToSequenceAdditive B

/-- The existing inverse-equivalence additivity instance, with the projection exposed.
Source: Zheng 4.1 (blueprint: def-pur-system-singleton-scalar-comparisons). -/
instance singletonSequenceInverseAdditive :
    (strictSystemSequenceEquivalence B).inverse.Additive := sequenceToStrictSystemAdditive B

variable {B} {D : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : B ⟶ D)

/-- Actual scalar restriction on the sequence site.
Source: Stacks 03DA (blueprint: def-pur-system-singleton-scalar-comparisons). -/
abbrev singletonSequenceRestriction :=
  restrictScalars.{w} ((sheafCompose (coefficientSequenceTopology J)
    (forget₂ CommRingCat.{w} RingCat.{w})).map (singletonSequenceRingMap a))

/-- Actual scalar restriction at one level.
Source: Stacks 03DA (blueprint: def-pur-system-singleton-scalar-comparisons). -/
abbrev singletonLevelRestriction (n : ℕ) :=
  restrictScalars.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
    (a.app (op n)))

/-- Evaluation and restriction commute by the identity on sections.
Source: Stacks 03DA; vertical-site calculation
(blueprint: def-pur-system-singleton-scalar-comparisons). -/
def singletonRestrictionEvaluation (n : ℕ) :
    singletonSequenceRestriction a ⋙ systemSequenceEvaluation B n ≅
      systemSequenceEvaluation D n ⋙ singletonLevelRestriction a n :=
  NatIso.ofComponents (fun M ↦ (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by intros; ext x; rfl)))
    (by intros; ext U x; rfl)

variable (A : SystemScalarModel (singletonSequenceRingMap a))

end SheafOfModules
