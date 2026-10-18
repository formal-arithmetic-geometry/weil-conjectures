/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Data.Set.Countable
public import Mathlib.RingTheory.Flat.Basic
public import Sheaf.RingTheory.IsMittagLeffler

/-!
# Countably generated flat Mittag-Leffler modules are projective

Source: Stacks Project, Algebra, Tag 059X, `lemma-countgen-projective`
(blueprint: lem-trf-countable-flat-mittag-leffler-projective).
-/

@[expose] public section

universe u v

namespace Module

/--
Source: Stacks Project, Algebra, Tag 059X, `lemma-countgen-projective`.

A flat, Mittag-Leffler, countably generated module is projective. Countable generation
is expressed by a countable subset whose span is the whole module, which says exactly
that every element is a finite linear combination of elements of that subset.

Proof:
1. By flatness and the Lazard presentation, write `P` as a filtered colimit of finite
   free modules. The countable generation and the tensor-product Mittag-Leffler
   condition yield a countable cofinal sequence of finite free stages.
2. Applying the Hom-system Mittag-Leffler result to this sequence shows that the
   inverse systems of Hom groups are Mittag-Leffler. Hom from each finite free stage
   preserves a short exact sequence coordinatewise, and the Mittag-Leffler inverse-limit
   exactness theorem therefore gives exactness after taking inverse limits.
3. The colimit universal property identifies these inverse limits naturally with
   `Hom_R(P, -)`. Thus `Hom_R(P, -)` is exact, and the characterization of projective
   modules gives `Module.Projective R P`.

(blueprint: lem-trf-countable-flat-mittag-leffler-projective)
-/
theorem projective_of_countable_flat_mittagLeffler
    {R : Type u} [CommRing R] {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Flat R P] (hML : Module.IsMittagLeffler R P)
    (hcountable : ∃ E : Set P, E.Countable ∧ Submodule.span R E = ⊤) :
    Module.Projective R P := by
  sorry

end Module
