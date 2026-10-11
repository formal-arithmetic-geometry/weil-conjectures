/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.CategoryTheory.Generator.Sheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-!
# Flatness of the sheafified free presheaf

Source: literature/stacks-project/sites-modules.tex, Lemma 03EV (blueprint:
lem-weil-pbc-free-sheaf-flat).

## Main statement

The sheaf associated to the free presheaf on a representable, with a flat
coefficient object, is flat.
-/

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace CategoryTheory.GrothendieckTopology

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A]

/--
The sheafification of the free presheaf on a representable with flat
coefficient object is flat, expressed as preservation of finite limits by
left tensoring. This is Lemma 03EV of the Stacks Project, generalized to
Grothendieck abelian symmetric monoidal closed coefficient categories.
Source: Stacks Project, Modules on Sites, Lemmas 03EV, 03ES, 03ET and 0GMW;
the coefficient-category generalization is described in the module docstring of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`
(blueprint: lem-weil-pbc-free-sheaf-flat).

Proof:
1. Put `Q = Presheaf.freeYoneda X P`, and write `a` for sheafification and
   `iota` for the sheaf inclusion. Strong monoidality of `a`
   [lem-weil-pbc-sheaf-tensor-closed] (2), together with the counit isomorphism
   [lem-weil-pbc-presheaf-finite-limits-objectwise] (3), gives a natural
   isomorphism from tensoring with `a Q` to `iota` followed by tensoring with
   `Q` and then `a`. It suffices to show that this composite is left exact.
2. For each `V`, `Q(V)` is the coproduct of copies of `P` indexed by `V ⟶ X`.
   Each copy is flat by `hP`, and the coproduct is flat by
   [lem-weil-pbc-flat-coproduct]: closedness makes tensor preserve coproducts,
   and AB4, implied by the Grothendieck AB5 condition, makes coproducts exact.
   This includes the empty coproduct, which is zero.
3. Evaluation preserves finite limits, and finite limits of presheaves are
   computed objectwise [lem-weil-pbc-presheaf-finite-limits-objectwise] (1).
   Evaluation of tensoring with `Q` is evaluation followed by tensoring with
   the flat object `Q(V)` from step 2, so tensoring with `Q` is left exact.
4. The inclusion `iota` preserves finite limits
   [lem-weil-pbc-presheaf-finite-limits-objectwise] (2), and `a` is exact
   [lem-weil-pbc-sheaf-tensor-closed] (1). The composite in step 1 therefore
   preserves finite limits; transport along its natural isomorphism proves
   the conclusion.
-/
lemma free_sheaf_flat (P : A) (hP : PreservesFiniteLimits (tensorLeft P))
    (X : C) :
    PreservesFiniteLimits (tensorLeft (Sheaf.freeYoneda J X P)) := by
  sorry

end CategoryTheory.GrothendieckTopology
