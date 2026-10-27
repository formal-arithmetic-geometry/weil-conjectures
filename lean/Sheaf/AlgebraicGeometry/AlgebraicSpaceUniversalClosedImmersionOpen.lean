/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # The universal closed-immersion locus for algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 05XA,
`spaces-more-morphisms-lemma-where-closed-immersion`
(blueprint: lem-sfb-space-universal-closed-immersion-open).

The open subfunctor represents the closed-immersion condition after every algebraic-space
base change. The induced map is the canonical map between the sheaf fibre products.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The base changes making a morphism a closed immersion form an open subspace.
Source: Stacks Project, More on Morphisms of Spaces, Tag 05XA
(blueprint: lem-sfb-space-universal-closed-immersion-open).

Proof:
1. Form P = A ×_B C and the graph Γ = (id, f) : A → P. The graph square is the
   pullback of the diagonal of q: on each scheme test its elements satisfy f(a) = y = c.
   Since q is separated, its diagonal, and hence Γ, is a representable closed immersion
   by def-sfb-space-morphism-properties and lem-trf-space-fibre-products-etale-covers.
   By lem-sfb-space-closed-subspace-proper, Γ is proper and universally closed.
2. The projection P → C is a base change of p. Universal closedness is stable under
   base change directly from its definition, and under composition since composites of
   closed point maps are closed. Thus f is universally closed. The projection
   A ×_C A → A is a base change of f, so its composite p₂ to B is universally closed.
   Taking identity base changes shows that p and p₂ are closed on points.
3. Apply lem-sfb-space-unramified-radicial-parameter-open (Tag 05X9), using the assumed
   local finite type of p and the two closedness conclusions, to obtain an open V such
   that h factors through V exactly when f_T is unramified and universally injective.
4. Each f_T is a base change of f, hence universally closed by step 2. Apply
   lem-sfb-space-closed-immersion-unramified-criterion (Tag 05W8) to identify that last
   condition with being a closed immersion, for every algebraic-space parameter T. -/
theorem exists_openSubspace_universal_closedImmersion {S : Scheme.{u}}
    (A C B : AlgebraicSpace S) (p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C)
    (w : f ≫ q = p) (hp_lft : MapIsLocally (@LocallyOfFiniteType) p)
    (hp_closed : MapIsUniversallyClosed p) (hq_sep : MapIsSeparated q) :
    ∃ V : OpenSubspace B, ∀ (T : AlgebraicSpace S) (h : T ⟶ B),
      IsRepresentableWith (fun _ _ r ↦ IsClosedImmersion r.left)
        (pullback.map p.hom h.hom q.hom h.hom f.hom (𝟙 T.obj) (𝟙 B.obj)
          (by simpa using (congrArg (fun k : A ⟶ B ↦ k.hom) w).symm)
          (by simp)).hom ↔
        ∃ l : T.obj.obj ⟶ V.val.toFunctor, l ≫ V.val.ι = h.hom.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
