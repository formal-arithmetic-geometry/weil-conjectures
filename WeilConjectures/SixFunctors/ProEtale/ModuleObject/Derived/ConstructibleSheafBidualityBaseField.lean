/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

@[expose] public section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Conservativity used in the reduction from an arbitrary base field.

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/det-prop-sf-biduality-general.proof.md`, the final
conservativity sentence.  A fully faithful base-change functor reflects
isomorphisms, so a biduality map checked after algebraic-closure base change
can be descended once the evaluation square has been transported.
(blueprint: lem-pd-constructible-sheaf-biduality-base-field) -/
theorem base_field_reduction_reflects_isomorphisms
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    (F : C ⥤ D) (hF : F.FullyFaithful) {A B : C} (f : A ⟶ B)
    [IsIso (F.map f)] : IsIso f := by
  exact hF.isIso_of_isIso_map f

end AlgebraicGeometry.ProEtale.CondensedRing
