/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.CategoryTheory.Filtration
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Compatible splitting of a filtration with injective graded pieces

Source: Stacks Project, Derived Categories, Tag 05TP, `lemma-filtered-injective`
(blueprint: lem-trf-injective-graded-filtration-splits).

The interval is fixed in advance. A single isomorphism carries every filtration subobject
onto the corresponding tail of the finite biproduct. The explicit `HasBiproduct` arguments
are the standard finite-product construction, available in every abelian category.
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.FilteredObject

/-- A finite filtration with injective graded pieces admits a simultaneous splitting.
Source: Stacks Project, Derived Categories, Tag 05TP, `lemma-filtered-injective`
(blueprint: lem-trf-injective-graded-filtration-splits).

The right-hand subobject is the image of `biproduct.fromSubtype`, the canonical split
inclusion of the summands indexed by `n ≥ p`. Thus the equality specifies the embedded
subobject, not merely an abstract isomorphism of its underlying object.

Proof:
1. Set `J_n = gr^n I` for `a ≤ n ≤ b`. These are injective by hypothesis, with identity
   graded-piece isomorphisms. Put `B_n = ⨁_{n ≤ k ≤ b} J_k`. Descend from `b + 1` to `a`,
   constructing `θ_n : F^n I ≅ B_n` compatible with all inclusions `F^p I → F^n I` for
   `n ≤ p ≤ b + 1`. At `b + 1`, both objects are zero, so compatibility is automatic.
2. By `lem-weil-pbc-product-injectives`, the finite biproduct `B_(n+1)`, including the
   empty one, is injective. Transfer its extension property along `θ_(n+1)` to show
   `F^(n+1) I` is injective.
3. The inclusion `i_n : F^(n+1) I → F^n I` and quotient `q_n : F^n I → J_n` form a short
   exact sequence. By `lem-weil-pbc-ses-injective-kernel-splits`, choose `r_n` and `s_n`
   with `r_n i_n = 1`, `q_n s_n = 1`, and `i_n r_n + s_n q_n = 1` (composition here is
   written in the usual mathematical order).
4. The splitting identities and monicity of `i_n` give `r_n s_n = 0`. Hence `(q_n,r_n)`
   and `(s_n,i_n)` are inverse maps between `F^n I` and `J_n ⊕ F^(n+1) I`: their four
   matrix blocks are `1,0,0,1`. Compose with `1 ⊕ θ_(n+1)` to obtain `θ_n : F^n I ≅ B_n`.
5. Since `q_n i_n = 0` and `r_n i_n = 1`, `θ_n` carries the next inclusion to the tail
   inclusion. Factor every deeper inclusion through this one and use the induction
   hypothesis to get simultaneous compatibility. These equations identify subobjects
   because the maps `θ_p` are isomorphisms.
6. At `a`, use `F^a I = I` to obtain `θ`. Compatibility handles `a ≤ p ≤ b + 1`. If
   `p < a`, decreasingness forces `F^p I = I`, and the tail is the whole biproduct. If
   `p > b + 1`, decreasingness forces `F^p I = 0`, and the tail is empty. Thus the same
   `θ` identifies the required subobjects for every integer `p`. -/
theorem injective_graded_filtration_splits {C : Type u} [Category.{v} C] [Abelian C]
    (X : FilteredObject C) (a b : ℤ) (hab : a ≤ b)
    (ha : X.filtration.F a = ⊤) (hb : X.filtration.F (b + 1) = ⊥)
    (hgr : ∀ n : Set.Icc a b, Injective (X.filtration.gradedPiece n.1)) :
    ∃ J : Set.Icc a b → C,
      (∀ n : Set.Icc a b, Injective (J n)) ∧
      (∀ n : Set.Icc a b, Nonempty (J n ≅ X.filtration.gradedPiece n.1)) ∧
      ∃ θ : X.obj ≅ @biproduct _ C _ _ J (HasBiproduct.of_hasProduct J),
        ∀ p : ℤ, (Subobject.map θ.hom).obj (X.filtration.F p) =
          imageSubobject (@biproduct.fromSubtype _ C _ _ J (HasBiproduct.of_hasProduct J)
            (fun n : Set.Icc a b ↦ p ≤ n.1) (HasBiproduct.of_hasProduct _)) := by
  sorry

end CategoryTheory.FilteredObject
