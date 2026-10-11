/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.LocallyFreeExtCohomology
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Naturality of the degree-zero boundary under pullback

Source: Stacks Project, Cohomology Tag 0B3A, Derived Categories Tag 05TE, and
Cohomology Section Tag 01DZ (blueprint: lem-sc-p1-boundary-connecting-naturality).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The connecting maps of a short exact module sequence and its pullback agree on
sections composed with the pullback map. Both sides are written in `Ext O A 1`, under
its canonical identification with `H¹(X,A)` from `lem-sc-ext-locally-free`.
The map `hS.extClass.postcomp O (zero_add 1)` is precisely the boundary in Mathlib's
`Abelian.Ext.covariantSequence O hS 0 1 (zero_add 1)`, not a separately chosen map.
Here `i'`, `p'`, and `v` present any pullback short exact sequence, with the same kernel
`S.X₁`; `hi` fixes its canonical kernel inclusion.

Source: Stacks Project, Tag 05TE (naturality of the derived delta-functor), Section
01DZ (module cohomology), and Tag 0B3A (the canonical Ext/H¹ identification).
(blueprint: lem-sc-p1-boundary-connecting-naturality).

Proof, Step 1: form the pullback as pairs `(e,c')` satisfying `S.g(e) = u(c')`.
Its first projection `v` and `u` give the morphism of short exact sequences
`(id_A,v,u)`. The first square commutes by `hi`, and the second by the pullback
condition. Its kernel is A, and its second projection is locally surjective because
S.g is; thus the pullback row is short exact.
Step 2: apply `lem-weil-pbc-right-derived-universal-delta-functor` to this morphism
in degree zero, using `def-sc-sheaf-cohomology-functor`. The map on H¹(A) is the
identity and the map on H⁰ sends t to t followed by u. Evaluate naturality at t.
The same canonical Ext/H¹ identification on both sides expresses the result below;
Mathlib's Ext long exact sequence uses postcomposition with the extension class. -/
theorem boundary_connecting_naturality {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {C' E' : X.Modules} (u : C' ⟶ S.X₃)
    (i' : S.X₁ ⟶ E') (p' : E' ⟶ C') (w' : i' ≫ p' = 0)
    (hT : (ShortComplex.mk i' p' w').ShortExact)
    (v : E' ⟶ S.X₂) (_hi : i' ≫ v = S.f) (_hp : IsPullback v p' S.g u)
    (t : SheafOfModules.unit X.ringCatSheaf ⟶ C') :
    hS.extClass.postcomp (SheafOfModules.unit X.ringCatSheaf) (zero_add 1)
        (Abelian.Ext.mk₀ (t ≫ u)) =
      hT.extClass.postcomp (SheafOfModules.unit X.ringCatSheaf) (zero_add 1)
        (Abelian.Ext.mk₀ t) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
