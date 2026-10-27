/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing

/-!
# Equal-image profinite Cech tuples

Source: Stacks Project, Tags 08ZY, 0A2P and 016E; Bhatt--Scholze, Lemma 4.3.9.

The tuple and deletion definitions are shared by finite and normed coefficient proofs.
(blueprint: def-sfb-profinite-cech-tuples).
-/

@[expose] public section

set_option autoImplicit false

universe v

namespace Profinite

/-- Equal-image tuples in the Cech nerve, with the subtype topology of the finite product.
Source: Bhatt–Scholze, Lemma 4.3.9(2)–(4), explicit Cech expansion in the DAG
(blueprint: lem-sfb-normed-scalar-profinite-cech-exact). -/
abbrev scalarCechTuples {S T : Profinite.{v}} (q : C(T, S)) (r : ℕ) :=
  {t : Fin r → T // ∀ i j : Fin r, q (t i) = q (t j)}

/-- Delete coordinate `j`, retaining the equal-image condition.
Source: Bhatt–Scholze, Lemma 4.3.9(2)–(4), explicit Cech expansion in the DAG
(blueprint: lem-sfb-normed-scalar-profinite-cech-exact). -/
def scalarCechDelete {S T : Profinite.{v}} (q : C(T, S)) (r : ℕ) (j : Fin (r + 1))
    (x : scalarCechTuples q (r + 1)) : scalarCechTuples q r :=
  ⟨fun i ↦ x.val (j.succAbove i), fun i k ↦ x.property (j.succAbove i) (j.succAbove k)⟩

end Profinite
