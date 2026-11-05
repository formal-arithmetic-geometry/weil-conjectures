/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Order.Directed

/-!
# The pair category of a directed system of categories

Let `I` be a directed preorder (in the application, the finite subextensions `E ⊆ ℚ̄_ℓ` of
`ℚ_ℓ`, ordered by inclusion) and let `C i` (`i : I`) be categories with transition functors
`T h : C i ⥤ C j` for `h : i ≤ j` and associators `T h ⋙ T h' ≅ T (h.trans h')` satisfying the
cocycle condition (`CategoryTheory.StageSystem`). In the application `C E = D^b_c(T, E)` and
`T_{F/E} = F ⊗ᴸ_E -` is the derived extension of scalars.

The *pair category* `S.PairCategory` has
as objects the pairs `(i, x)` with `x : C i`, and as morphisms `(i, x) ⟶ (j, y)` the filtered
colimit
```
  colim_{n ≥ i, j} Hom_{C n}(T x, T y)
```
of the Hom sets at the common stages, the transition maps being the transports
`u ↦ u_p = a⁻¹ ≫ T u ≫ a` (`CategoryTheory.StageSystem.tr`). A morphism is represented by a
triple `(n, u)` (`CategoryTheory.StageSystem.Rep`), two representatives being identified when
their transports to some common stage agree; composition is computed after transporting the
representatives to a common stage. It is the filtered 2-colimit of the categories `C i`
(in the ordinary-category sense). No unit isomorphisms `T (le_refl i) ≅ 𝟭` are needed for
this construction: only the cocycle condition of the associators is used.

## Main definitions

- `CategoryTheory.StageSystem`: a directed system of categories with associators.
- `CategoryTheory.StageSystem.PairCategory`: its pair category, with
  `CategoryTheory.StageSystem.PairCategory.mkHom n hX hY u` the morphism represented by `u` at
  the stage `n`.
- `CategoryTheory.StageSystem.ι i : C i ⥤ S.PairCategory`: the inclusion `j_i` of the stage `i`,
  and `CategoryTheory.StageSystem.transIso h : S.T h ⋙ S.ι j ≅ S.ι i`.

## Main statements

- `CategoryTheory.StageSystem.PairCategory.mkHom_eq_mkHom_iff`: two morphisms represented at a
  stage `n` are equal if and only if they become equal at some further stage.
- `CategoryTheory.StageSystem.PairCategory.exists_mkHom_eq`: every morphism is represented at
  every sufficiently large stage.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category

variable {I : Type w} [Preorder I] (C : I → Type u) [∀ i, Category.{v} (C i)]

namespace StageSystem

variable {C} (S : StageSystem C)

variable {S}

variable (S)

namespace PairCategory

variable {S}

namespace Rep

variable {X Y : S.PairCategory}

variable [IsDirectedOrder I]

end Rep

variable [IsDirectedOrder I]

end PairCategory

open PairCategory

variable [IsDirectedOrder I]

namespace PairCategory

variable {S}

end PairCategory

open PairCategory

variable {S}

end StageSystem

end CategoryTheory
