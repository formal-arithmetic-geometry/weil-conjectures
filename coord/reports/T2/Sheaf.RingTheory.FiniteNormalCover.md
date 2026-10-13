## What changed

The existing theorem `exists_finite_normal_cover` has exactly its repository signature
and docstring. Its proof now extracts a finite family with a genuine covering property,
forms its supremum, and applies normality transfer using that covering property.
The two new statements live in their own modules:
`Sheaf.RingTheory.FiniteNormalCoverFamily` and
`Sheaf.RingTheory.FiniteNormalCoverSupNormal`. Both imports in the item are proof-only.
The family module imports the stated normal-locus dependency and the Mathlib local
normality and Noetherian tools for its documented proof route, all proof-only.

## Proved and sorry left

Existing hole closed: `exists_finite_normal_cover`
(node `lem-weil-pbc-finite-normal-cover`), by a reduction to two strictly smaller steps.

New holes added:
- `exists_finite_normal_cover_family`
  (node `lem-weil-pbc-finite-normal-cover-family`): finite extraction of a cover of
  base primes by algebras with normal fibers; it does not assert normality of a supremum.
- `finite_normal_cover_sup_normal`
  (node `lem-weil-pbc-finite-normal-cover-sup-normal`): algebraic transfer from that
  covering property to the supremum; it assumes the cover and does not extract it.

This is a decomposition, not a completed normal-cover proof: one existing hole closed,
two new holes added, net holes closed minus added = -1. Both lower holes have complete
natural-language proofs and sources in their docstrings. No `sorry` remains in the item.
No definitions or data constructions from unproved existence statements are added.
The superseded, undelivered helper statements were removed rather than counted as
closed holes. Their replacements remain open; the searches found ingredients rather
than a direct proof of either step.

All three modules compile with `lcompile.py --all`. A scratch copy with `#print axioms`
for all three declarations reports only `propext`, `Classical.choice`, `Quot.sound`,
and `sorryAx` from the two explicitly open steps. Edge-case scratch proofs verify that
the covering property implies the family is nonempty and that a singleton bottom
algebra satisfies that property when its prime localizations are normal.

## No longer needed

No repository import, old proof-dependency node, or previously reached module is pruned.
The original node had no proof dependencies. The invalid undelivered decomposition has
been replaced, not pruned from the existing library.

## Where the brief, the DAG or earlier work was wrong

The first reader's extraction theorem contained no covering property: the empty family
proved its conclusion irrespective of either hypothesis. The first reader's normality
lemma asserted normality of the supremum of *any* finite integral family. It is false.
For example, take A = k[t²,t³], K = k(t), and s empty. A is a Noetherian domain,
A localized away from t² is normal, and its finite normalization k[t] supplies hLocal
at every maximal ideal. But the empty supremum is the bottom algebra, isomorphic to A,
whose localization at the cusp is not integrally closed (t is missing, although t²
and t³ belong). The original lemma would assert that this localization is normal.

The repair retains the actual finite-cover condition in the extraction conclusion,
uses it as a hypothesis of the algebraic transfer, and removes hAway, hLocal,
Noetherianity and module-finiteness assumptions from the transfer theorem because they
are unnecessary there. These are new, undelivered helpers, so no existing interface or
change record is involved. The existing target statement is unchanged.

## New nodes

`lem-weil-pbc-finite-normal-cover-family` records the finite cover of Spec A from
Stacks Tag 0333. Its planned proof uses the existing normal-locus, local normality,
and finite-algebra Noetherian nodes, then compactness. Its statement, full proof,
source, three fresh search records, blueprint ancestry, and Lean signature were repaired.

`lem-weil-pbc-finite-normal-cover-sup-normal` records the strictly algebraic transfer
from a cover to normal prime localizations of the finite supremum. Its proof contracts
a prime to one of the chosen normal local rings, uses integrality in the common
fraction field, and localizes. It has the same complete metadata and fresh searches.
The item node now records precisely the combination of these two lemmas.
No existing statement or definition changes; no change records are necessary.

## Second reading by T2

1. Compared every delivered module with the repository version. The sole existing
   declaration's signature is byte-for-byte unchanged, as is its docstring. The other
   two modules and declarations are new. No existing definition, instance, visibility,
   or public import changes. Verdict: pass after the repair.
2. Compiled all three modules in import order using only lcompile.py. Checked the
   declarations for forbidden constructs and definitions with holes. The only holes
   are the two named, documented, listed lower theorems. Scratch #print axioms shows
   exactly the allowed axioms and sorryAx. Verdict: pass as an explicit decomposition.
3. Read both new statements against Stacks Tags 0333 and 0332, and tested small cases.
   Rejected the former arbitrary-family lemma with the empty-family cusp counterexample.
   Repaired extraction to include every base prime and transfer to require that cover.
   The normal-fiber cover can exist without asserting normality of its supremum; the
   transfer applies to a given cover without any compactness or local approximation
   hypotheses. Each is true, needed, and strictly part of the argument. Repeated
   LeanFinder, Loogle and grep searches with different queries and searched both local
   library roots. Found standard tools (closed integral spectrum maps, compactness,
   integrally closed elements of fraction fields, normality of localization), but no
   exact duplicate. Verdict: pass after correcting the false and insufficient lemmas.
4. Reviewed the reduction from the target downward. The two steps follow the finite
   subcover and integral-localization paragraphs of Tag 0333; neither merely restates
   the item. Both added imports in the item and all proof-dependency imports in the
   extraction module are plain imports. Existing public Mathlib imports are required
   by the signatures. Checked dag/units/sk-thm-p1.json realized: the item is below the
   realized unit statements and steps, and none of those routes changes. The original
   proof_deps was empty, so No longer needed is complete. Verdict: pass.
5. Compared node lean.statement fields with the actual signatures; checked proof steps,
   proof_deps unions, proof_origin, source, searches, blueprint ancestry and new-module
   paths. Rewrote the new nodes' vague and inaccurate proofs as complete arguments and
   updated the item's dependency plan to match the Lean reduction. Verdict: pass.

Second-reading changes: removed the false arbitrary-family claim; added the missing
normal-fiber cover; moved the new statements to their own modules; removed unnecessary
transfer hypotheses; restored the original theorem docstring; repaired node metadata
and searches; corrected the report to count the work as a decomposition with two holes.

Preflight repair: recorded fresh LeanSearch attempts for both nodes. The service returned
Internal Server Error for both; no no-match verdict is inferred from its unavailability.
The successful independent searches and local-source checks remain recorded.
