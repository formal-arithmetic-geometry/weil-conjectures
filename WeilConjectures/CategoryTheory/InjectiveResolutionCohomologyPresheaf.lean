/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CechResolutionDoubleComplex
public import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.InjectiveResolutionCohomologyPresheafData

/-!
# The cohomology presheaf computed by an injective resolution
-/

@[expose] public section

universe u v

namespace CategoryTheory

/-- Evaluation of an injective resolution computes the Ext cohomology presheaf,
naturally in the object of the site. -/
theorem Sheaf.injectiveResolution_cohomologyPresheaf
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    {F : Sheaf J AddCommGrpCat.{v}} (I : InjectiveResolution F) (q : ℕ) :
    Nonempty
      ((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).asFunctor ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q ≅
      F.cohomologyPresheaf q) := by
  obtain ⟨e, he⟩ := Sheaf.injectiveResolution_cohomologyPresheaf_data I q
  exact ⟨NatIso.ofComponents e he⟩

end CategoryTheory
