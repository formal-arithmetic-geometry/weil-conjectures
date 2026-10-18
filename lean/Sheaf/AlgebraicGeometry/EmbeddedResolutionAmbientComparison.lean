/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Sheaf.AlgebraicGeometry.LabeledEmbeddedResolution
import WeilConjectures.Blowup.FlatBaseChange
import WeilConjectures.Compactification.StrictTransformBlowup

/-!
# Synchronized embedded resolution independent of the ambient scheme

Source: ILO, Expose VIII, 2.3.11 and 2.3.13, printed pp. 93--94;
Bierstone--Milman--Temkin, Q-universal desingularization, Theorem 6.1 and
Addendum, section 6.3 (blueprint: lem-trf-embedded-resolution-ambient-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- There is one ordered set of synchronization labels and an embedded resolution
algorithm on every reduced closed subscheme of every smooth separated finite-type
rational scheme, including finite disjoint unions. It stops at regularity, commutes
with all smooth ambient pullbacks by deleting exactly empty centers, and has coherent
intrinsic comparisons independent of the ambient embedding.

Source: ILO VIII 2.3.11, 2.3.13, pp. 93--94; BMT Theorem 6.1 and Addendum, section 6.3
(blueprint: lem-trf-embedded-resolution-ambient-comparison).

Proof plan:
1. Apply `lem-trf-hilbert-samuel-resolution-invariant-calculus` simultaneously to
   all embedded pairs and histories. At each nonregular stage blow up the reduced
   full maximum locus of the corrected invariant. Its regularity, nonemptiness,
   nowhere density and coherent ideals are clause (1). Label the stage by its
   maximum in the reverse invariant order. Maxima strictly decrease. Taking maxima
   on an entire finite disjoint union synchronizes its components.
2. Clause (4) of the same invariant calculus terminates precisely this recursion.
   Clause (1) implies regularity at termination. Stop at the first regular stage,
   omitting exceptional cleanup. Empty and regular inputs have no active labels.
3. For a smooth ambient map use `lem-pc-smooth-flat`, flat blowup base change
   (`thm-nagata-blowup-flat-base-change` and its canonical comparison
   `def-nagata-blowup-flat-base-change-map`), and smooth base change
   (`lem-pc-proper-base-change`, clause (2)). Apply
   `lemma-nagata-strict-transform-ambient-closed` to identify strict transforms
   with intrinsic blowups of the pulled-back ideals. This gives cartesian stage
   comparisons scheme-theoretically, rather than only topological closures.
4. Induct over the finitely many labels. Clause (2) of the invariant calculus
   identifies invariants and stratum ideals under arbitrary smooth pullback.
   A nonempty inverse image of a maximum is the next maximum; an empty inverse
   image has the unit ideal and gives an identity stage. At the last label the
   pulled-back invariant is bottom everywhere. There are no additional stages.
5. For two embeddings of the same reduced scheme, clause (3) identifies invariant
   histories, next labels and ideal centers intrinsically. Their next strict
   transforms are the same intrinsic blowup by
   `lemma-nagata-strict-transform-ambient-closed`. Induct, retaining the ideals
   even when the intrinsic blowup is an isomorphism.
6. Identity and composite smooth maps (`lem-trf-smooth-composition`) give equal
   extended ideals, equal blowup comparisons and equal deletions of empty centers.
   Thus the stage comparison maps satisfy identity and composition laws.
7. Clause (3) also transports histories along isomorphisms of the initial schemes.
   The maps induced by the same ideal on its blowup coincide. Stagewise induction
   proves the intrinsic identity law and cocycle for three ambient embeddings.
   Insert identity stages at absent labels to obtain the cut-indexed diagrams.
-/
theorem exists_synchronized_embedded_resolution :
    ∃ (L : Type (u + 1)) (order : LinearOrder L),
      Nonempty (@SynchronizedEmbeddedResolution.{u, u + 1} L order) := by
  sorry

end AlgebraicGeometry
