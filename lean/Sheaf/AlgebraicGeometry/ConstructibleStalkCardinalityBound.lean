/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-!
# A uniform cardinality bound for constructible abelian sheaves

Source: Stacks Project, Tags 03RW and 095E, and the finite-cover argument in step 1 of
`lem-weil-pbc-curve-constructible-annihilator`.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The geometric stalks of a constructible underlying set sheaf on a Noetherian scheme
are finite and have uniformly bounded cardinality. No torsion hypothesis is needed.

Source: Stacks Project, Definition 03RW and Lemma 095E; the finite-cover part of step 1
of `lem-weil-pbc-curve-constructible-annihilator`.
(blueprint: lem-weil-pbc-constructible-stalk-cardinality-bound)

Proof: Take the finite stratification in the constructibility hypothesis. Each stratum
is homeomorphic to a subspace of the Noetherian underlying space of X, hence is
quasi-compact. On each stratum choose a trivializing etale cover for its set-sheaf
pullback. Etale morphisms are open, so finitely many images cover the stratum.
Discard empty members. On a remaining member, choose a geometric point. The stalk
of the constant set sheaf is its constant value, and the pullback stalk is the stalk
on the stratum. Thus this value is finite. At any point of this member the same
stalk formula identifies its stalk with that finite value. Take the maximum of the
cardinalities of all these values over all strata and selected members (zero for
an empty family). A geometric point of X factors through its locally closed stratum:
the defining ideal vanishes in the residue field and its open neighbourhood contains
the point. The etale covering of that stratum lifts the geometric point. The inverse
image stalk formula for sets (`etaleSetInverseImageStalkGerm`) then identifies its
stalk with one of the selected finite values.
Finally forgetting abelian groups commutes with geometric stalks, since these are
filtered colimits and forgetting preserves filtered colimits. This transfers both
finiteness and the cardinality bound to the displayed abelian stalks. In the empty
scheme case there are no stalk conditions; for the zero sheaf every stalk has
cardinality one, so one is a valid bound. -/
theorem exists_stalk_cardinality_bound_of_constructible
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F)) :
    ∃ N : ℕ, ∀ x : X,
      Finite (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) ∧
      Nat.card (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) ≤ N := by sorry

end AlgebraicGeometry.Scheme
