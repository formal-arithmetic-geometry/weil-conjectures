/-
Copyright (c) 2026 The Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Mathlib.Topology.Sheaves.Stalks

/-!
# Stalks of sheaves of modules on a scheme
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace Topology

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

lemma toSheaf_map_hom {M N : X.Modules} (φ : M ⟶ N) :
    ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom = (Modules.toPresheaf X).map φ := rfl

theorem Hom.isIso_of_isIso_stalkFunctor_map {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, IsIso ((SheafOfModules.stalkFunctor X.ringCatSheaf x).map φ)) :
    IsIso φ := by
  have h' : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).1) := h
  have h2 : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _
  have h3 : IsIso ((Modules.toPresheaf X).map φ) := by
    have := (sheafToPresheaf (Opens.grothendieckTopology X) Ab.{u}).map_isIso
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)
    exact this
  exact isIso_of_reflects_iso φ (Modules.toPresheaf X)

end AlgebraicGeometry.Scheme.Modules
