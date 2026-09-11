/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Topology.Sheaves.LocallySurjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Mathlib.Topology.Sheaves.Stalks

/-!
# Exactness of the stalk functor on sheaves of modules

Mathlib's `Mathlib/Algebra/Category/ModuleCat/Stalk.lean` endows the stalk of a presheaf of
modules with a module structure over the stalk of the presheaf of rings. This file adds the
two things that are needed to *compute* with stalks:

* the map induced on stalks by a morphism of presheaves of modules is linear, and
* taking stalks is an exact functor on sheaves of modules.

Exactness is obtained by combining left exactness, which holds already at the level of
presheaves because a stalk is a filtered colimit
(`TopCat.Presheaf.stalkFunctor_preservesFiniteLimits`), with the fact that an epimorphism of
sheaves is locally surjective, hence surjective on stalks.

## Main declarations

* `PresheafOfModules.stalkMapₗ`: the map induced on stalks by a morphism of presheaves of
  modules, as a linear map over the stalk of the structure presheaf of rings.
* `SheafOfModules.stalkFunctor`: taking the stalk at `x`, as a functor to abelian groups.
* `CategoryTheory.ShortComplex.ShortExact.map_stalkFunctor`: a short exact sequence of sheaves
  of modules induces a short exact sequence of stalks.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace PresheafOfModules

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (φ : M ⟶ N) (x : X)

/-- The map induced on stalks by a morphism of presheaves of modules, as a linear map over the
stalk of the presheaf of rings. -/
noncomputable def stalkMapₗ :
    TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x →ₗ[R.stalk x]
      TopCat.Presheaf.stalk (C := Ab.{u}) N.presheaf x where
  toFun := (TopCat.Presheaf.stalkFunctor Ab.{u} x).map ((toPresheaf _).map φ)
  map_add' := map_add _
  map_smul' r m := by
    obtain ⟨V, hxV, a, rfl⟩ := R.exists_germ_eq r
    obtain ⟨U, hUV, hxU, s, rfl⟩ :=
      TopCat.Presheaf.exists_le_germ_eq (C := Ab.{u}) M.presheaf m hxV
    rw [RingHom.id_apply, ← R.germ_res_apply (homOfLE hUV) x hxU a, ← germ_smul]
    -- `erw`: after `← germ_smul` the section lives in `M.obj (op U)`, which is the carrier of
    -- `M.presheaf.obj (op U)` only up to unfolding `PresheafOfModules.presheaf`.
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply, ← germ_smul]
    congr 1
    exact map_smul (φ.app (op U)).hom _ _

@[simp]
lemma stalkMapₗ_apply (m : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) :
    stalkMapₗ φ x m = (TopCat.Presheaf.stalkFunctor Ab.{u} x).map ((toPresheaf _).map φ) m := rfl

end PresheafOfModules

namespace SheafOfModules

variable {X : TopCat.{u}} (R : TopCat.Sheaf RingCat.{u} X)

/-- Taking the stalk at `x`, as a functor from sheaves of modules to abelian groups. -/
noncomputable def stalkFunctor (x : X) : SheafOfModules.{u} R ⥤ Ab.{u} :=
  SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj ⋙
    TopCat.Presheaf.stalkFunctor Ab.{u} x

instance (x : X) : PreservesFiniteLimits (stalkFunctor R x) :=
  letI : PreservesFiniteLimits (TopCat.Presheaf.stalkFunctor Ab.{u} x) := inferInstance
  letI : PreservesFiniteLimits
      (PresheafOfModules.toPresheaf R.obj ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x) :=
    comp_preservesFiniteLimits _ _
  comp_preservesFiniteLimits _ _

instance (x : X) : (stalkFunctor R x).Additive :=
  Functor.additive_of_preserves_binary_products _

instance (x : X) : (stalkFunctor R x).PreservesEpimorphisms where
  preserves {M N} φ hφ := by
    have := hφ
    have := (toSheaf R).map_epi φ
    exact (AddCommGrpCat.epi_iff_surjective _).2
      (TopCat.Sheaf.surjective_stalkFunctor_map_of_epi ((toSheaf R).map φ) x)

end SheafOfModules

namespace CategoryTheory.ShortComplex.ShortExact

variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}

/-- **Taking stalks is exact**: a short exact sequence of sheaves of modules induces a short
exact sequence of stalks at every point. -/
lemma map_stalkFunctor {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact) (x : X) :
    (S.map (SheafOfModules.stalkFunctor R x)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (SheafOfModules.stalkFunctor R x)).1 inferInstance S hS
  exact { exact := h.1, mono_f := h.2, epi_g := (SheafOfModules.stalkFunctor R x).map_epi _ }

end CategoryTheory.ShortComplex.ShortExact
