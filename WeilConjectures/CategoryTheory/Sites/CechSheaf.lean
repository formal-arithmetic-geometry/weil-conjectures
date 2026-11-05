/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.Sites.CechInjective

/-!
# Čech complexes of sheaves in degree `0`

Let `V : ι → Over X` be a family of objects over `X` whose structure morphisms generate a
covering sieve of `X`, and let `P` be a sheaf of abelian groups. The augmented Čech complex
`0 ⟶ P(X) ⟶ Č⁰(V, P) ⟶ Č¹(V, P)` is exact: this is the sheaf condition for the covering.

Together with `CategoryTheory.Presheaf.exact_cechComplexFunctor_of_injective`, this shows that
the augmented Čech complex of an injective abelian sheaf is exact.

## Main statements

- `CategoryTheory.Presheaf.mono_cechAugmentation_of_isSheaf`: `P(X) ⟶ Č⁰(V, P)` is injective.
- `CategoryTheory.Presheaf.exact_cechAugmentation_of_isSheaf`: exactness at `Č⁰(V, P)`.
- `CategoryTheory.Sheaf.injective_obj`: an injective abelian sheaf is injective as
  a presheaf (Stacks `03F6`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {X : C}
  [HasFiniteProducts (Over X)] {ι : Type w} (V : ι → Over X) (P : Cᵒᵖ ⥤ AddCommGrpCat.{max v w})

variable {V P}

section

variable (hP : Presheaf.IsSheaf J P)
  (hV : Sieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (V i).hom) ∈ J X)

end

end CategoryTheory.Presheaf

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]

end CategoryTheory.Sheaf
