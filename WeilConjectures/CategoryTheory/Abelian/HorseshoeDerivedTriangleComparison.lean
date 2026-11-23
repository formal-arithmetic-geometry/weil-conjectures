/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Abelian.NatComplexDerivedBoundary
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.CategoryTheory.Abelian.HorseshoeComparisonBoundary
import WeilConjectures.CategoryTheory.Abelian.InjectiveResolutionDerivedComparisonNaturality
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Comparing the derived image triangle with a fixed horseshoe

Source: Stacks Project, Derived Categories, Tags 014Q, 05TE and 015B.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A fixed compatible horseshoe gives a morphism from the derived image of the
single-object triangle to the derived triangle of the termwise image resolution.
Its endpoint homology maps are the canonical right-derived identifications.
No delta-functor or chosen connecting maps are involved in this statement.

Source: Stacks Project, Derived Categories, Tags 014Q, 05TE and 015B. -/
theorem horseshoe_derived_triangle_comparison
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [EnoughInjectives A] [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v]
    (S : ShortComplex A) (hS : S.ShortExact)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (_hιA : IA.ι ≫ α = (CochainComplex.single₀ A).map S.f ≫ IB.ι)
    (_hιB : IB.ι ≫ β = (CochainComplex.single₀ A).map S.g ≫ IC.ι)
    (_hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval A (ComplexShape.up ℕ) k)).ShortExact)
    (hvH : ((ShortComplex.mk α β hαβ).map
      (v.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact)
    (hExt : (((ShortComplex.mk α β hαβ).map
      (v.mapHomologicalComplex (ComplexShape.up ℕ))).map
      (ComplexShape.embeddingUpNat.extendFunctor B)).ShortExact) :
    ∃ τ : ((v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
        hS.singleTrianglePlus) ⟶ DerivedCategory.triangleOfSES hExt,
      (∀ n : ℕ,
        (DerivedCategory.homologyFunctor B (n : ℤ)).map τ.hom₁ ≫
            (natComplexDerivedHomologyIso
              ((v.mapHomologicalComplex _).obj IA.cocomplex) n).hom =
          (v.homologyRightDerivedFunctorPlusObjSingleFunctorIso S.X₁ n).hom ≫
            (IA.isoRightDerivedObj v n).hom) ∧
      (∀ n : ℕ,
        (DerivedCategory.homologyFunctor B (n : ℤ)).map τ.hom₃ ≫
            (natComplexDerivedHomologyIso
              ((v.mapHomologicalComplex _).obj IC.cocomplex) n).hom =
          (v.homologyRightDerivedFunctorPlusObjSingleFunctorIso S.X₃ n).hom ≫
            (IC.isoRightDerivedObj v n).hom) := by
  have h₃ := horseshoe_comparison_boundary v S hS IA IB IC
    α β hαβ _hιA _hιB _hH hvH hExt
  let τ : ((v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
      hS.singleTrianglePlus) ⟶ DerivedCategory.triangleOfSES hExt :=
    { hom₁ := injectiveResolutionDerivedComparison v IA
      hom₂ := injectiveResolutionDerivedComparison v IB
      hom₃ := injectiveResolutionDerivedComparison v IC
      comm₁ := by
        exact injectiveResolutionDerivedComparison_naturality v S.f IA IB α _hιA
      comm₂ := by
        exact injectiveResolutionDerivedComparison_naturality v S.g IB IC β _hιB
      comm₃ := h₃ }
  refine ⟨τ, ?_, ?_⟩
  · intro n
    exact injectiveResolutionDerivedComparison_homology v IA n
  · intro n
    exact injectiveResolutionDerivedComparison_homology v IC n

end CategoryTheory
