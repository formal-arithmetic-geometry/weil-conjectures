/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Surjective quasi-isomorphisms of simplicial abelian groups

Source: Stacks Project, Simplicial, Lemma 08P1, `lemma-qis-simplicial-abelian-groups`
(blueprint: lem-trf-surjective-qis-simplicial-group-trivial-kan).

The associated complex is Mathlib's alternating-face complex, extended by zero along
`ComplexShape.embeddingUpNat.op` to integer degrees. The underlying simplicial map is obtained
by whiskering with the forgetful functor. Trivial Kan fibrations are expressed by the right
lifting property against all boundary inclusions, including the empty boundary in degree zero.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

/-- A termwise surjective quasi-isomorphism of simplicial abelian groups is a trivial Kan
fibration on underlying simplicial sets. Source: Stacks Project, Simplicial, Lemma 08P1
(blueprint: lem-trf-surjective-qis-simplicial-group-trivial-kan).

Proof (blueprint steps).
Step 1: put `C_X^r = s(X)_{-r}` and `C_Y^r = s(Y)_{-r}`, with the same differentials. These are
the nonpositive cochain complexes of
`lem-trf-simplicial-abelian-surjective-quasi-iso-boundary-lifting`: in degree `-n` the term is
`X_n` with the alternating face sum for `n > 0`, and zero in degree `0` and positive degrees.
Kernels and images are those of the same homomorphisms, so `H^r(C_X) = H_{-r}(s(X))`,
compatibly with `f`; hence `C_f` is a quasi-isomorphism by the hypothesis `hqis`.
Step 2: apply `lem-trf-simplicial-abelian-surjective-quasi-iso-boundary-lifting` to `f`; its
surjectivity hypothesis is `hsurj` and Step 1 gives its quasi-isomorphism hypothesis. It supplies
fillers of every boundary square `∂Δ[n] ⟶ Δ[n]` against the underlying map, for every `n ≥ 0`
(for `n = 0` the boundary is empty and this is surjectivity on vertices). This is lifting
against every generator of `SSet.modelCategoryQuillen.I`, i.e. a trivial Kan fibration
(Stacks Definition 08NL). The source proof of 08P1 is carried by that proof dependency. -/
theorem trivialKanFibration_of_surjective_of_quasiIso
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)
    (hsurj : ∀ n : ℕ, Function.Surjective (f.app (Opposite.op (SimplexCategory.mk n))))
    (hqis : ∀ n : ℤ, IsIso (HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap
        ((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).map f)
        ComplexShape.embeddingUpNat.op) n)) :
    SSet.modelCategoryQuillen.I.rlp (Functor.whiskerRight f (forget AddCommGrpCat.{u})) := by
  sorry

end CategoryTheory.SimplicialObject
