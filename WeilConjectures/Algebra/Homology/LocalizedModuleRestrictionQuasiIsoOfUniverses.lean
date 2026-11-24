/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-!
# Exact restriction of module complexes to a localized site

## References

* Stacks Project, Section 18.19 (Tag 03DH), Tag 03DK and Tag 0A95
-/

@[expose] public section

universe u v r
open CategoryTheory
namespace CategoryTheory

/-- Restriction of a quasi-isomorphism of module complexes to `C/U` is a quasi-isomorphism. -/
theorem localizedModule_restriction_quasiIsoOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J RingCat.{max u v r}) (U : C)
    (hzero : (SheafOfModules.overFunctor.{max u v r} R U).PreservesZeroMorphisms)
    {L' L : CochainComplex (SheafOfModules.{max u v r} R) ℤ}
    (t : L' ⟶ L) [QuasiIso t] :
    letI := hzero
    QuasiIso (((SheafOfModules.overFunctor.{max u v r} R U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map t) := by
  let := hzero
  let F := SheafOfModules.overFunctor.{max u v r} R U
  let G := SheafOfModules.toSheaf.{max u v r} (R.over U)
  let H := J.overPullback AddCommGrpCat.{max u v r} U
  let e : F ⋙ G ≅ SheafOfModules.toSheaf.{max u v r} R ⋙ H := Iso.refl _
  have : Limits.PreservesFiniteLimits H := by
    dsimp [H]
    infer_instance
  have : Limits.PreservesFiniteLimits (SheafOfModules.toSheaf.{max u v r} R ⋙ H) :=
    Limits.comp_preservesFiniteLimits _ _
  have : Limits.PreservesFiniteLimits (F ⋙ G) :=
    Limits.preservesFiniteLimits_of_natIso e.symm
  have : Limits.PreservesFiniteLimits F :=
    Limits.preservesFiniteLimits_of_reflects_of_preserves F G
  have : Limits.PreservesColimitsOfSize.{max u v r, max u v r} H :=
    ((Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat.{max u v r}
      (J.over U) J).leftAdjoint_preservesColimits
  have : Limits.PreservesFiniteColimits H := by infer_instance
  have : Limits.PreservesFiniteColimits (SheafOfModules.toSheaf.{max u v r} R ⋙ H) :=
    Limits.comp_preservesFiniteColimits _ _
  have : Limits.PreservesFiniteColimits (F ⋙ G) :=
    Limits.preservesFiniteColimits_of_natIso e.symm
  have : Limits.ReflectsFiniteColimits G := by
    exact { reflects := fun K _ _ ↦
      Limits.reflectsColimitsOfShape_of_reflectsIsomorphisms }
  have : Limits.PreservesFiniteColimits F :=
    Limits.preservesFiniteColimits_of_reflects_of_preserves F G
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  exact HomologicalComplex.quasiIso_map_of_preservesHomology t F

end CategoryTheory
