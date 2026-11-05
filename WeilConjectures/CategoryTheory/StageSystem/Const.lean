/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import WeilConjectures.CategoryTheory.StageSystem.Functor

/-!
# Functors from a pair category to a fixed category

The constant stage system `CategoryTheory.StageSystem.const I D` on a category `D` has the
identity functors as transition functors and identities as associators. Its pair category maps
to `D` by forgetting the stages (`CategoryTheory.StageSystem.constEval`).

A *coherent cocone* on a stage system `S` with vertex `D`, i.e. functors `Φ_i : C i ⥤ D` with
isomorphisms `T_{j/i} ⋙ Φ_j ≅ Φ_i` compatible with the associators, is the same as a morphism of
stage systems `S ⟶ const I D` (`CategoryTheory.StageSystem.Morphism.ofCocone`); it therefore
induces a functor `S.PairCategory ⥤ D` (`CategoryTheory.StageSystem.descFunctor`), the comparison
functor from the `2`-colimit to the vertex, sending `(i, x)` to `Φ_i x`.

The stage inclusions `j_i : C i ⥤ S.PairCategory` form a cocone of categories
(`CategoryTheory.StageSystem.cocone`) which is a filtered `2`-colimit in the sense of
`CategoryTheory.CategoryCocone.IsFilteredTwoColimit`
(`CategoryTheory.StageSystem.cocone_isFilteredTwoColimit`).
-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory

namespace StageSystem

variable (I : Type w) [Preorder I] (D : Type u') [Category.{v'} D]

variable {I D}

variable [IsDirectedOrder I]

open PairCategory

variable {C : I → Type u} [∀ i, Category.{v} (C i)] {S : StageSystem C}

end StageSystem

end CategoryTheory
