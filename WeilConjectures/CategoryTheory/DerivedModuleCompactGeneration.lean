/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.CompactlyGenerated
import WeilConjectures.CategoryTheory.DerivedModuleRankOneProperties

/-! # Compact generation of the derived category of modules

Source: Stacks Project, Tags 0F5X and 07D9.
-/

@[expose] public section

universe w vH

namespace CategoryTheory

open Limits

/-- The derived module category is compactly generated in the modules' universe.
Source: Stacks Project, Tag 0F5X, first paragraph, and Tag 07D9. -/
theorem derivedModuleCompactGeneration
    {S : Type w} [Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    [HasCoproducts.{max w vH} (DerivedCategory (ModuleCat.{max w vH} S))] :
    IsCompactlyGeneratedTriangulated.{max w vH}
      (DerivedCategory (ModuleCat.{max w vH} S)) := by
  classical
  let P := (DerivedCategory.singleFunctor (ModuleCat.{max w vH} S) 0).obj
    (ModuleCat.of S (ULift.{vH} S))
  obtain ⟨hPcompact, hPgen⟩ := derivedModule_rankOne_properties (S := S)
  let I : Type (max w vH) := ULift.{max w vH} PUnit
  let E : I → DerivedCategory (ModuleCat.{max w vH} S) := fun _ => P
  let e : (∐ E) ≅ P := coproductUniqueIso E
  have hgenE : IsWeakTriangulatedGenerator (∐ E) := by
    intro K hK
    obtain ⟨n, f, hf⟩ := hPgen K hK
    refine ⟨n, e.hom ≫ f, ?_⟩
    intro hz
    apply hf
    have hh : e.hom ≫ f = e.hom ≫ (0 : P ⟶ K⟦n⟧) := by
      simpa only [comp_zero] using hz
    exact (cancel_epi e.hom).1 hh
  refine ⟨I, E, ?_, hgenE⟩
  intro i
  exact hPcompact

end CategoryTheory
