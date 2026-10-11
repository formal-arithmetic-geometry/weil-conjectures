/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.BaseChangeConventions

/-!
# Pointwise étaleness under extension of the base field

Source: Stacks Project, Varieties, Tag 0C4Y, and the pointwise analogue of Descent,
Tag 02VN (blueprint: lem-sc-etale-base-change-geometric).

The neighbourhood formulation uses open subschemes and the existing `Etale` predicate.
Base change is the map of `Over.pullback`, as in `def-pc-base-change`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Pointwise étaleness is preserved and reflected by extension of the base field.
Source: Stacks Project, Varieties, Tag 0C4Y; pointwise analogue of Descent, Tag 02VN
(blueprint: lem-sc-etale-base-change-geometric).

Proof:
1. If `f` is étale on an open neighbourhood `U` of `x`, its base change is étale on
   `U_K`, which contains `xK`. This is stability under base change
   (`lem-weil-pbc-etale-scheme-base-change`, Stacks, Tag 02GO).
2. Conversely, if the base change is étale on a neighbourhood of `xK`, the local ring
   map at `x` and `xK` is faithfully flat (Stacks, Tag 0C4Y). Apply pointwise descent
   (`lem-sc-etale-faithfully-flat-local`) to obtain an étale neighbourhood of `x`.
   Global fpqc descent (Tag 02VN) alone does not establish this pointwise assertion;
   Tag 036N concerns fppf coverings, which an arbitrary field extension need not be. -/
theorem etaleAt_iff_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y)
    (x : X.left)
    (xK : (pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme))
    (hx : (pullback.fst X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) xK = x) :
    (∃ U : X.left.Opens, x ∈ U ∧ Etale (U.ι ≫ f.left)) ↔
      (let fK := ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map f).left
       ∃ U : (pullback X.hom
         (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Opens,
         xK ∈ U ∧ Etale (U.ι ≫ fK)) := by
  sorry

end AlgebraicGeometry
