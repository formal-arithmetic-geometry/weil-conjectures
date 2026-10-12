/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.CategoryTheory.Sites.PresheafCechComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Sheaf.AlgebraicTopology.SetCechNerveFreeResolution

/-! # Exact augmentation of the sheafified free presheaf Čech nerve

Source: Stacks Project, Tag 01GC.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

/-- The canonical free Čech augmentation is exact and epic for a locally
surjective presheaf map.
Source: Stacks Project, Tag 01GC, degree-zero part.
(blueprint: lem-sc-presheaf-cech-sheaf-augmentation-exact)

Proof: the augmentation sends each vertex to its image. Both faces of an edge
have the same image, so its composite with the first differential is zero.
Objectwise the free nerve resolves the free abelian group on the image of the
map, by `AlgebraicTopology.setCechNerve_free_resolution`. Sheafification is exact.
For the image inclusion, free abelianization is injective. A finite sum of target
generators lifts locally: lift each generator using local surjectivity and take
a common covering refinement for their finitely many covers. Thus the free image
inclusion is a local bijection, and its sheafification is an isomorphism. Hence
the augmentation is epic with kernel the first differential's image. Empty
fibres cause no problem: only the image is used before sheafification.
-/
theorem presheafCechSheaf_augmentation_exact
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}] (f : Arrow (Cᵒᵖ ⥤ Type v))
    (hf : Presheaf.IsLocallySurjective J f.hom) :
  let F := (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf J AddCommGrpCat
  let A := (AlgebraicTopology.alternatingFaceMapComplex _).obj (f.cechNerve ⋙ F)
  let ε := F.map (WidePullback.base (fun _ : Fin 1 ↦ f.hom))
  ∃ hz : A.d 1 0 ≫ ε = 0,
    (ShortComplex.mk (A.d 1 0) ε hz).Exact ∧ Epi ε := by sorry

end CategoryTheory.Sheaf
