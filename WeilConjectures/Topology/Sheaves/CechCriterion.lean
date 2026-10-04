/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.Topology.Sheaves.Cech

/-!
# Vanishing of cohomology from vanishing of Čech cohomology

Let `X` be a topological space, `B` a class of open subsets of `X` containing `X`, and `𝒞` a
class of finite families of open subsets such that all finite intersections of the members of a
family in `𝒞` lie in `B`, and such that every open covering of a member `V` of `B` is refined by
a family in `𝒞` covering `V`. If an abelian sheaf `F` has vanishing higher Čech cohomology on all
the families in `𝒞`, then the higher sheaf cohomology `H^q(X, F)` vanishes.

This is [Stacks, Cohomology, Lemma 20.11.9][stacks-project] (tag `01EV`). The proof is the
usual dimension shifting: embed `F` into an injective sheaf `I` with cokernel `Q`. The vanishing
of the first Čech cohomology of `F` shows that `I(V) → Q(V)` is surjective for every `V` in `B`,
hence that the Čech complexes of `F`, `I` and `Q` on a family in `𝒞` form a short exact sequence.
Since the Čech complexes of `I` are exact in positive degrees, `Q` again has vanishing higher Čech
cohomology on the families in `𝒞`, and `H^{q + 1}(X, F) ≅ H^q(X, Q)` for `q > 0` while
`H^1(X, F)` is the cokernel of `I(X) → Q(X)`.

## Main statements

- `TopCat.Presheaf.surjective_app_of_exactAt_cechComplex_one`: if the first Čech cohomology of
  `F` vanishes on families refining every covering of `V`, then `I(V) → Q(V)` is surjective for
  every short exact sequence `0 → F → I → Q → 0` of abelian sheaves.
- `TopCat.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex`: the vanishing criterion.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Presheaf

variable {X : TopCat.{u}}

/-- Let `0 → F → I → Q → 0` be a short exact sequence of abelian sheaves and `V` an open subset
such that every open covering of `V` is refined by a finite family `U` covering `V` on which the
first Čech cohomology of `F` vanishes. Then `I(V) → Q(V)` is surjective. -/
theorem surjective_app_of_exactAt_cechComplex_one
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})} (hS : S.ShortExact) {V : Opens X}
    (hV : ∀ W : V → Opens X, (∀ x, x.1 ∈ W x) → ∃ (n : ℕ) (U : Fin n → Opens X),
      iSup U = V ∧ (∀ i, ∃ x, U i ≤ W x) ∧ ((cechComplex U).obj S.X₁.obj).ExactAt 1) :
    Function.Surjective (S.g.hom.app (op V)) :=
  sorry

end TopCat.Presheaf

namespace TopCat.Sheaf

open Presheaf

variable {X : TopCat.{u}}

/-- **The Čech criterion for the vanishing of cohomology.** Let `B` be a class of open subsets of
`X` containing `X` and `𝒞` a class of finite families of open subsets such that the finite
intersections of the members of a family in `𝒞` lie in `B`, and such that every open covering of
a member `V` of `B` is refined by a family in `𝒞` covering `V`. If the Čech complexes of the
abelian sheaf `F` on the families in `𝒞` are exact in positive degrees, then `H^q(X, F) = 0` for
`q > 0`. -/
@[stacks 01EV]
theorem subsingleton_H_succ_of_exactAt_cechComplex (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (B : Opens X → Prop) (𝒞 : ∀ {n : ℕ}, (Fin n → Opens X) → Prop) (hB : B ⊤)
    (h𝒞 : ∀ {n : ℕ} (U : Fin n → Opens X), 𝒞 U → ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      B (⨅ l, U (y l)))
    (hcov : ∀ V, B V → ∀ W : V → Opens X, (∀ x, x.1 ∈ W x) → ∃ (n : ℕ) (U : Fin n → Opens X),
      𝒞 U ∧ iSup U = V ∧ ∀ i, ∃ x, U i ≤ W x)
    (hF : ∀ {n : ℕ} (U : Fin n → Opens X), 𝒞 U → ∀ q : ℕ,
      ((cechComplex U).obj F.obj).ExactAt (q + 1))
    (q : ℕ) : Subsingleton (CategoryTheory.Sheaf.H F (q + 1)) :=
  sorry

end TopCat.Sheaf
