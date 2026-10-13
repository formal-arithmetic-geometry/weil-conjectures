## What changed

Proved `AlgebraicGeometry.Scheme.prefixDeletionRestrictions` in
`Sheaf.AlgebraicGeometry.PrefixDeletionRestrictions`, preserving its signature and
existing docstring. Added proof-only imports of `Mathlib.Data.Fin.Tuple.Sort` and
`Sheaf.AlgebraicGeometry.AlternatingCechPartialSortUnique`. Two proved private helpers
construct the complement restriction and transfer stable sorting to it. The main
proof establishes the deleted stable label, identifies the restricted stable sort
using `Tuple.eq_sort_iff`, transfers the partial prefix and tail inequalities, and
uses `cechPartialSort_existsUnique` to identify the restricted partial sort.
Updated the existing node's proof and dependencies to record these actual steps.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.prefixDeletionRestrictions`
(node `new-prefix-deletion-restrictions`). No sorries remain in the delivered module;
no holes were added or split off. Both private helpers are proved. The imported
partial-sort uniqueness theorem is already proved in the library.
Compilation checks the full general statement, including p=0, an empty prefix,
the final allowed prefix, repeated values and any linearly ordered index type.

## No longer needed

None of the original imports, proof-dependency nodes or modules were removed.
The proof follows the existing restriction-and-uniqueness route. No extra existence,
construction of the outgoing/incoming equivalence, sign formula, or before-condition
lemma is needed. A trial proof import of `Mathlib.Logic.Equiv.Fin.Basic` was removed
because the existing public sorting-operators import already provides its API.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The existing DAG did not explicitly cite the
available, proved partial-sort uniqueness node; the proof dependency now names it.
No statements, definitions, visibility or other modules were changed.

## Second reading by T4

1. Compared the only delivered Lean module with the repository using `diff`, and
   separately checked the existing theorem signature byte for byte. The signature,
   original docstring, public import and definitions are unchanged. The only Lean
   additions are two proved private helpers, two proof-only imports and the proof
   replacing the original `sorry`. No change record is needed. Verdict: pass.
2. Compiled the module with `lcompile.py`: exit code 0, no warnings. Compiled a
   scratch copy with `#print axioms` for `restrict_perm`, `stable_restrict` and
   `prefixDeletionRestrictions`: each lists only `propext`, `Classical.choice` and
   `Quot.sound`, with no `sorryAx`. Searched the delivered Lean for forbidden
   declarations and sorries: none. The complement permutations are explicit
   compositions of proved equivalences, not witnesses from an unproved theorem.
   Verdict: pass.
3. No statements or holes were split off. Read both private helper proofs: the
   first composes the increasing complement bijections with the permutation's
   subtype equivalence; the second transports monotonicity and equal-value label
   order through strictly increasing embeddings. For n=0 the restriction is the
   unique empty permutation. In the main proof, r<a=b+1 ensures that k<b lifts
   below a and k>=b lifts at or above a, including b=0 and b=p. Stable uniqueness
   handles repeated values without an injectivity assumption on the tuple.
   Verdict: pass; one hole closed, zero added.
4. Read Mathlib's `Tuple.eq_sort_iff`, the existing proved
   `cechPartialSort_existsUnique`, and searched both Lean roots for deletion,
   restriction and sorting uniqueness. The analogous tail-deletion helpers are
   private and address a different correspondence; no public declaration removes
   this argument. The proof uses Mathlib stable uniqueness directly and the
   existing partial-sort theorem. Each import is used; the sorting-operators
   public import supplies the signature's predicates, and both added imports
   remain private to the proof. The original proof dependency is retained, so
   `No longer needed` is complete. Read `dag/units/sk-thm-picard-pn.json`:
   its existing `realized` entries are empty, and this local restriction proof
   neither changes them nor replaces any unit step. Verdict: pass.
5. Compared the node JSON with the repository. Only `proof`, `proof_deps` and
   `proof_origin` differ. The recorded steps describe the explicit restriction,
   stable uniqueness, prefix/tail arithmetic and partial uniqueness used in Lean;
   `proof_deps` is exactly the union of their `uses`. The added dependency names
   the existing partial-sort uniqueness node. The statement and Lean signature
   record are unchanged, and there are no new nodes. Verdict: pass.

Second reading changed only this report: added the independent checks and their
verdicts. No repair to the Lean proof or DAG was necessary.
