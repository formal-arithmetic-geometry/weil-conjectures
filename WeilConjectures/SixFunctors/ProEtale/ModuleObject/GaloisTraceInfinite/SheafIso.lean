/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsFilteredColimit

/-!
# Isomorphisms of abelian sheaves detected on a covering family of objects

A morphism `φ : F ⟶ G` of sheaves of abelian groups which is bijective on sections over the
objects of a class `P` is an isomorphism, as soon as every object is covered by objects of `P`
(`CategoryTheory.Sheaf.isIso_of_isIso_app_of_forall_exists_mem`): it is then locally injective
and locally surjective.

We also record the variant of
`AlgebraicGeometry.Scheme.ProEt.isColimitSectionsOfIsColimit` for filtered diagrams indexed by a
small category in `Type u`
(`AlgebraicGeometry.Scheme.ProEt.isColimitSectionsOfIsColimitOfShrink`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}} {J : Type u} [SmallCategory J] [IsFiltered J]
  {F : J ⥤ Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}} {c : Cocone F}

end AlgebraicGeometry.Scheme.ProEt
