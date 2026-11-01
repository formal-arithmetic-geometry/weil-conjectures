/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.PointFiberFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonScalarExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonScalarLimits
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonScalarColimits
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointEvaluationEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedBoundaryDerivedEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointScalarPresentation

/-! # Component equivalence for point evaluation -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]
  (I : Type w) [Finite I]

private theorem assemble_component_equivalence
    (P : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
      (point k).left ≌
        (DerivedCategory.pointFiniteDimensional
          (ULift.{u + 1} (PadicAlgCl ℓ))).FullSubcategory)
    (G : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
      (condensedPointBoundary k I) ≌
        (I → ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
          (point k).left))
    (hP : Nonempty (P.functor ⋙
      (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))).ι ≅
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
        (point k).left).ι ⋙ (pointSections ℓ k).mapDerivedCategory))
    (hL : Nonempty (P.inverse ⋙
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
        (point k).left).ι ≅
      (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))).ι ⋙
        (condensedPointScalarExtension ℓ k).mapDerivedCategory))
    (hG : ∀ t : I, Nonempty (G.functor ⋙ Pi.eval (fun _ : I ↦
      ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) (point k).left) t ⋙
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
          (point k).left).ι ≅
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
        (condensedPointBoundary k I)).ι ⋙
          (condensedBoundaryRestriction ℓ k I t).mapDerivedCategory)) :
    CondensedBoundaryEquivalenceAssertion ℓ k I := by
  classical
  let E := G.trans (Equivalence.pi (fun _ : I ↦ P))
  obtain ⟨eP⟩ := hP
  obtain ⟨eL⟩ := hL
  refine ⟨E, ?_, ?_⟩
  · intro t
    obtain ⟨eG⟩ := hG t
    exact ⟨Functor.isoWhiskerLeft (G.functor ⋙ Pi.eval _ t) eP ≪≫
      Functor.isoWhiskerRight eG (pointSections ℓ k).mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso
        (condensedBoundaryRestriction ℓ k I t) (pointSections ℓ k)).symm⟩
  · intro t
    obtain ⟨eG⟩ := hG t
    exact ⟨Functor.isoWhiskerLeft (Equivalence.pi (fun _ : I ↦ P)).inverse
        eG.symm.inverseCompIso ≪≫
      Functor.isoWhiskerLeft (Pi.eval (fun _ : I ↦
        (DerivedCategory.pointFiniteDimensional
          (ULift.{u + 1} (PadicAlgCl ℓ))).FullSubcategory) t) eL⟩

/-- The component equivalence and its scalar-extension presentation.
Source: blueprint local boundary duality, Step 5, point reconstruction and clopen gluing.
Split covers of the geometric point give global finite presented condensed models.
Their presentation matrices have finite free cokernels. The upstream point fiber functor's
projective Hom calculation gives the equivalence on bounded constructible complexes;
uniqueness of left adjoints identifies its inverse with the prescribed copower functor.
Internal module reconstruction on the finite clopen cover, followed by finite-product derived
localization and componentwise constructibility, assembles the boundary equivalence.
Finite cohomological supports have a finite common union. A counit scalar adjunction and the
constant scalar normalization identify the copower with finiteConstantScalarExtension.
Empty products and rank zero are included.
(blueprint: lem-a1-condensed-point-component-equivalence) -/
theorem condensed_point_component_equivalence
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    CondensedBoundaryEquivalenceAssertion ℓ k I ∧
      CondensedBoundaryScalarExtensionPresentation ℓ k := by
  obtain ⟨P, hP, hL⟩ := point_evaluation_equivalence_with_inverse ℓ k
  obtain ⟨G, hG⟩ := condensed_boundary_derived_equivalence ℓ k I
  exact ⟨assemble_component_equivalence ℓ k I P G hP hL hG,
    condensed_point_scalar_presentation ℓ k⟩

end AlgebraicGeometry.ProEtale.CondensedRing
