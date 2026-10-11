/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.SetTheory.Cardinal.HasCardinalLT
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# Smallness of objects with respect to ordinal chains of monomorphisms

Source: Stacks Project, Injectives, Proposition 19.11.5 (Tag 079F),
`proposition-objects-are-small` (blueprint: prop-pur-kinjective-objects-small).
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- In a Grothendieck abelian category, an object is small with respect to monomorphisms
indexed by an ordinal whose cofinality exceeds the cardinality of its set of subobjects.
Source: Stacks Project, Injectives, Proposition 19.11.5 (Tag 079F)
(blueprint: prop-pur-kinjective-objects-small).

Proof: (1) By AB5 from `def-sp-grothendieck-abelian`, the structure maps of the monomorphism
chain into its colimit are monic. For `f : M ⟶ c.pt`, their inverse images are an increasing
family of subobjects of `M` whose colimit is `M`.
(2) Choose one index for each distinct inverse-image subobject. There are at most `|M|`
such indices. Since `|M| < α.cof`, they have an upper bound strictly below `α`. The inverse
image at this bound contains all the others and therefore equals `M`.
(3) The pullback defining that inverse image then gives a factorization of `f` through
its corresponding stage of the chain. -/
theorem exists_factorization_of_subobject_cardinal_lt_cof
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    (M : A) (α : Ordinal.{w}) (hsize : HasCardinalLT (Subobject M) α.cof)
    (B : α.ToType ⥤ A)
    (hmono : ∀ ⦃β γ : α.ToType⦄ (h : β ≤ γ), Mono (B.map (homOfLE h)))
    (c : Cocone B) (hc : IsColimit c) (f : M ⟶ c.pt) :
    ∃ (β : α.ToType) (g : M ⟶ B.obj β), g ≫ c.ι.app β = f := by
  sorry

end CategoryTheory
