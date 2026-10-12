## What changed

Second reading rejected the submitted reduction: its new strictification theorem
and the original item assert incompatible finiteness and composition properties.
Restored the repository version of the item, including all imports and its original
named theorem hole, and added a STATEMENT-DISPUTED comment with a counterexample.
No statement, definition, signature, or public import changed. Removed both new
statement modules and their nodes from the delivery. The rejected submission is
preserved under sandbox scratchpad/rejected-reduction, outside the delivery tree.

## Proved and sorry left

Holes closed: none. Holes added: none. This is a disputed-statement delivery, not
a proof or a decomposition. The original hole remains:
`AlgebraicGeometry.Scheme.exists_affineEtale_colimit_presentation`, node
`lem-weil-pbc-affine-etale-colimit-presentation`.

The proposed lower holes `exists_affineEtale_strictification` and
`exists_affineEtale_strict_colimit` are not delivered. The former is false;
the latter's proof plan incorrectly claimed fully faithful functors inject on
arrows with variable source objects. That inference is false, although this alone
does not refute its theorem: the proposed duplicate-object counterexample fails
its strong composition hypothesis. No such example is claimed as a counterexample
in this report.

## No longer needed

None: all original imports and proof-dependency edges are retained. No pruning
or ledger progress is claimed. The two proposed new modules and nodes were rejected,
not pruned from the library, since they never entered it.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the original conclusion, and the proposed strictification,
require finite covering presieves together with Mathlib's
`Precoverage.IsStableUnderComposition`. This class is strictly stronger than
transitivity of a finite pretopology: it permits arbitrary indexed families with
repeated outer arrows and different inner refinements for each repetition.

Counterexample to the original item: use a singleton directed preorder, a constant
scheme diagram with S = Spec(k) for a field k, its identity limiting cone, and all
U, v, gamma, delta, p, q equal to the identity data. S is qcqs and its identity is
affine. Cover and pullback preservation, continuity and the finite-limit-preserving
identity left adjoint give h10-h14. Object, map and equality descent are identities;
h18 is the identity presentation in one direction and invariance of finite jointly
surjective etale families under source and target isomorphisms in the other.
Normalization and both coherence equations hold. Thus every original hypothesis holds.

Let A be the identity affine etale object of S. For each n in Nat let B_n be the
disjoint union of n+1 copies of S, with its fold map b_n : B_n -> A. This is a finite
affine etale object and the singleton presieve of b_n covers. The B_n are pairwise
nonisomorphic (their numbers of connected components differ). The asserted e is an
equivalence, so the objects e(B_n) are still pairwise nonisomorphic, hence distinct.
Its cover-preservation clause makes each singleton e(b_n) a Q-cover.

Take the outer family indexed by Nat with constant source e(A) and every arrow
the identity. Its presieve is the singleton identity, hence a Q-cover by HasIsos.
For its nth member take the inner family indexed by Unit consisting of e(b_n).
Mathlib's `Precoverage.comp_mem_coverings` now forces the presieve consisting of all
e(b_n) to be a Q-cover. Its uncurried set is infinite: n maps injectively to the
pair (e(B_n), e(b_n)), since the source objects are distinct. This contradicts the
asserted finiteness of every Q-cover. The contradiction already occurs at one stage;
no colimit or sheaf argument can repair it. The same example refutes the new
strictification theorem, whose hypotheses are a subset of this identity system.

Sources inspected directly: Mathlib/CategoryTheory/Sites/Precoverage.lean,
`IsStableUnderComposition` and `comp_mem_coverings`; Sites/Finite.lean,
`Pretopology.finite`; Sites/Sieves.lean, `Presieve.map`, `map_iff` and `map_ofArrows`.
Finite.lean provides only HasIsos for the finite precoverage, and defines the finite
pretopology via presieve-bind transitivity. It does not provide the stronger composition
instance used here. The existing docstring's claim that these site axioms follow
from finite etale precoverage is therefore invalid for the displayed Lean classes.
No target is weakened or changed. A correction of the affected intermediate
interfaces and their users needs a separately scoped statement-change delivery.

## Second reading by J1

1. Compared the original submitted item by diff: only proof imports and the theorem
body differed; the existing signature was byte-for-byte unchanged. The final delivery
restores the whole repository module and only adds the disputed-statement comment.
No definitions, signatures, or public imports changed and no change record is needed.

2. Compiled all three submitted files locally via lcompile.py: all passed without
warnings. A scratch copy with explicit #print axioms for all three declarations
reported only propext, Classical.choice, Quot.sound and sorryAx. This was a reduction
to two new holes, not an axiom-free proof. No forbidden declaration or hollow definition
was present. The final delivery retains only the original named hole.

3. Read both new statements, their docstrings and nodes. The strictification is false
by the singleton identity-system counterexample above. The strict-colimit finiteness
argument also contains an invalid use of full faithfulness across different sources.
Rejected both new modules and nodes. Independent Loogle search for Presieve.map found
no identifier; LeanFinder search for faithful functors, object injectivity and finite
presieve images found Functor.map_injective, whose signature fixes BOTH source and
target objects. Direct library and Mathlib grep confirmed the precise stronger
composition axiom and the weaker finite-pretopology construction. No shorter proof
can establish the false original statement.

4. Read dag/units/sk-thm-p1.json, including realized. Neither the original item nor
its four old generic proof dependencies realizes a unit statement or step. The
submitted reduction was below unit level. Final delivery keeps the unit and all
original dependencies/imports unchanged, with no pruning claims. The difficulty is
mathematical falsity, not the previously reported universe mismatch alone.

5. Compared the parent node with its Lean statement and the proposed new nodes with
their Lean statements. The submitted parent proof tracked the actual two applications,
but its strictification dependency is false. Removed all node edits from the final
delivery, preserving the original node and route pending a proper statement repair.
The explicit disputed comment and this report expose why its old proof plan fails.

Changes made: rejected the invalid decomposition, restored the original named hole
and imports, marked the item disputed with a concrete counterexample, and removed
all proposed new nodes/modules from the delivery. No false helper is delivered.
