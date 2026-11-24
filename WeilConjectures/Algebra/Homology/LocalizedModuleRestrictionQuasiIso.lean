/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.QuasiIso

import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Exact restriction of module complexes to a localized site

## Implementation details

The statement holds for arbitrary Grothendieck topologies and needs no boundedness of the
complexes.

## References

* Stacks Project, Section 18.19 (Tag 03DH), Tag 03DK and Tag 0A95
-/

@[expose] public section

universe u v
open CategoryTheory
namespace CategoryTheory

/-- Restriction of a quasi-isomorphism of module complexes to `C/U` is a quasi-isomorphism. -/
theorem localizedModule_restriction_quasiIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (hzero : (SheafOfModules.overFunctor.{max u v} R U).PreservesZeroMorphisms)
    {L' L : CochainComplex (SheafOfModules.{max u v} R) ℤ}
    (t : L' ⟶ L) [QuasiIso t] :
    letI := hzero
    QuasiIso (((SheafOfModules.overFunctor.{max u v} R U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map t) := by
  let := hzero
  let F := SheafOfModules.overFunctor.{max u v} R U
  let G := SheafOfModules.toSheaf.{max u v} (R.over U)
  let H := J.overPullback AddCommGrpCat.{max u v} U
  let e : F ⋙ G ≅ SheafOfModules.toSheaf.{max u v} R ⋙ H := Iso.refl _
  have : Limits.PreservesFiniteLimits H := by
    dsimp [H]
    infer_instance
  have : Limits.PreservesFiniteLimits (SheafOfModules.toSheaf.{max u v} R ⋙ H) :=
    Limits.comp_preservesFiniteLimits _ _
  have : Limits.PreservesFiniteLimits (F ⋙ G) :=
    Limits.preservesFiniteLimits_of_natIso e.symm
  have : Limits.PreservesFiniteLimits F :=
    Limits.preservesFiniteLimits_of_reflects_of_preserves F G
  have : Limits.PreservesColimitsOfSize.{max u v, max u v} H :=
    ((Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat.{max u v}
      (J.over U) J).leftAdjoint_preservesColimits
  have : Limits.PreservesFiniteColimits H := by infer_instance
  have : Limits.PreservesFiniteColimits (SheafOfModules.toSheaf.{max u v} R ⋙ H) :=
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
