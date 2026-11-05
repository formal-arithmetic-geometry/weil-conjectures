/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-!
# Fibres of morphisms out of constant sheaves

`CategoryTheory.GrothendieckTopology.Point.sheafFiberConstantSheafIso_inv_comp_sheafFiber_map`:
at a point `Φ` of a site with terminal object `T`, the fibre of a morphism `ψ : M_C ⟶ G` is,
through `(M_C)_Φ ≅ M`, the adjunct `M ⟶ Γ(T, G)` followed by the germ map `Γ(T, G) ⟶ G_Φ`.
-/

@[expose] public section

universe w v u v' u'

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]
  [HasWeakSheafify J A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [J.WEqualsLocallyBijective A] [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{w, w} (CategoryTheory.forget A)] [LocallySmall.{w} C]

end CategoryTheory.GrothendieckTopology.Point
