/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section

/-!
# Adjunction-compatible restriction

Source: Proof of (2) and (3) in
`prop-sf-localization-all-stages`, and the restriction clauses in
`det-thm-sf-ctf-stability-adjunctions` (blueprint: def-sp-compatible-adjunction-restriction).
-/

universe vA vB vA₀ vB₀ uA uB uA₀ uB₀

set_option autoImplicit false

open CategoryTheory

namespace WeilConjectures

/--
`podCompatibleRestriction adj iA iB` records restricted functors, comparison
isomorphisms, and an adjunction whose Hom bijection is the transported ambient
Hom bijection. Source: the restriction clauses in
`det-thm-sf-ctf-stability-adjunctions` (blueprint: def-sp-compatible-adjunction-restriction).
-/
def podCompatibleRestriction
    {A : Type uA} {B : Type uB} {A₀ : Type uA₀} {B₀ : Type uB₀}
    [Category.{vA, uA} A] [Category.{vB, uB} B]
    [Category.{vA₀, uA₀} A₀] [Category.{vB₀, uB₀} B₀]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    (iA : A₀ ⥤ A) (iB : B₀ ⥤ B) : Prop :=
  ∃ (F₀ : A₀ ⥤ B₀) (G₀ : B₀ ⥤ A₀)
    (α : F₀ ⋙ iB ≅ iA ⋙ F) (β : G₀ ⋙ iA ≅ iB ⋙ G) (adj₀ : F₀ ⊣ G₀),
    ∀ (K : A₀) (L : B₀) (h : F₀.obj K ⟶ L),
      iA.map (adj₀.homEquiv K L h) =
        adj.homEquiv (iA.obj K) (iB.obj L) (α.inv.app K ≫ iB.map h) ≫ β.inv.app L

end WeilConjectures
