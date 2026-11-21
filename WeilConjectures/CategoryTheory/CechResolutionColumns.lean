/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CechResolutionDoubleComplex
import WeilConjectures.CategoryTheory.CechComplexHomology
import WeilConjectures.CategoryTheory.InjectiveResolutionCohomologyPresheaf

/-!
# Column cohomology of the Čech resolution double complex
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasFiniteWidePullbacks C] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- The column cohomology, including its horizontal differential, is the Čech
complex of the cohomology presheaf. -/
theorem Sheaf.cechResolutionDoubleComplex_columns
    {F : Sheaf J AddCommGrpCat.{v}} (I : InjectiveResolution F) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X) (q : ℕ) :
    Nonempty
      (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (Sheaf.cechResolutionDoubleComplex I X π) ≅
      (cechComplexFunctor fun i ↦ Over.mk (π i)).obj
        ((Over.forget X).op ⋙ F.cohomologyPresheaf q)) := by
  let A := (sheafToPresheaf J AddCommGrpCat.{v} ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{v}).obj (Over.forget X).op)
  let R := (A.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  obtain ⟨e⟩ :=
    cechComplexFunctor_homology (fun i ↦ Over.mk (π i)) R q
  obtain ⟨h⟩ := Sheaf.injectiveResolution_cohomologyPresheaf I q
  refine ⟨e ≪≫ (cechComplexFunctor fun i ↦ Over.mk (π i)).mapIso ?_⟩
  exact ((Functor.whiskeringLeft _ _ AddCommGrpCat.{v}).obj (Over.forget X).op).mapIso h

end CategoryTheory
