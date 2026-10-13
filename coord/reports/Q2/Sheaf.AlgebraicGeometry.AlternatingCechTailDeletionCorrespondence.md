## What changed

Proved `AlgebraicGeometry.Scheme.cechTailDeletionBasic` in
`Sheaf.AlgebraicGeometry.AlternatingCechTailDeletionCorrespondence` without changing any
existing statement, definition, or visibility. Added a proof-only import of
`Sheaf.AlgebraicGeometry.AlternatingCechPartialSortUnique` and proved private finite-index
helpers. Updated the basic-deletion node to record the actual argument and dependency.

The explicit forward map deletes the outgoing position `k = r - 1` from the partial
permutation and its stable rank from the stable permutation. Stable sorting and partial
sorting survive restriction. The incoming order condition follows from the stable ordering
of the pairs `(t(label), label)`. Injectivity uses stable-sort and partial-sort uniqueness;
surjectivity takes `Tuple.sort t`, recovers the prefix rank from the incoming order condition,
and uses the existing proved unique partial sort. The four requested identities follow
from the explicit restriction formula. The pre-existing junction and correspondence proofs
remain valid.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.Scheme.cechTailDeletionBasic`
(node `lem-pc-alternating-cech-tail-deletion-basic`).

No sorry remains in the module; no holes were added. This is a proof, not a decomposition.
The imported `AlgebraicGeometry.Scheme.cechPartialSort_existsUnique` is already proved.
Single-file compilation succeeds without warnings. The delivery dry run checks the axioms
of all declarations.

## No longer needed

Removed the redundant proof-only import `Mathlib.Logic.Equiv.Fin.Basic`; its omission-map
equivalences are already available through `Mathlib.Data.Fin.Tuple.Sort`. The sorting import
is necessary (removing it fails compilation). The existing sorting-operator definition
dependency remains needed. The only additional
proof dependency is `lem-pc-alternating-cech-partial-sort-unique`; no planned node or module
was pruned. No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The remaining basic-deletion node described deletion and insertion only abstractly. Its
forward construction and bijectivity are now implemented. Explicit insertion of a permutation
is unnecessary: existence and uniqueness of the existing partial sort produce the preimage.
The proof handles `p = 0`, repeated values of `t`, zero prefix, and the largest possible
omitted position uniformly. The nonjunction condition excludes the final prefix position
when there is no later stable rank, providing the bound for the shorter prefix index.
No statement or tool error was found. No new nodes or forced adaptations were needed.


## Second reading by Q2

1. Compared the complete delivered module and node with the repository versions. All existing
   declaration signatures, definitions, docstrings, and visibility are byte for byte unchanged.
   Only the basic theorem's proof, private helpers, and proof-only imports changed. No change
   record is required. Verdict: pass.
2. Compiled the module locally without errors or warnings and compiled a scratch copy with
   `#print axioms` for `cechTailDeletionBasic`, `cechTailDeletionJunction`, and
   `cechTailDeletionCorrespondence`. Each reports exactly `propext`, `Classical.choice`, and
   `Quot.sound`. No sorry or forbidden declaration mechanism occurs. The deletion map is
   explicit; the surjectivity witness comes from the already proved unique partial sort,
   not an unproved existence assertion. Verdict: pass.
3. No statements were split off and no nodes or holes were added. Read the imported
   `cechPartialSort_existsUnique`: its prefix and increasing-tail clauses match precisely
   the two uses in injectivity and surjectivity. Checked the new private restrictions for
   zero prefix, repeated values, p=0, and deletion at the last position: increasing omission
   maps preserve the tail order; a<d ensures the retained prefix lies in Fin(p+1).
   The nonjunction condition excludes r=0 and r=a. Verdict: pass.
4. Read the full proof downward. Stable uniqueness uses Mathlib `Tuple.eq_sort_iff`; partial
   uniqueness reuses the existing proved library theorem. Searched the library and upstream
   algebraic-geometry sources for deletion, partial-sort, and stable-sort alternatives, and
   read Mathlib's tuple-sort declarations; no shorter complete correspondence was found.
   There are no unused old proof-dependency nodes. Read `dag/units/sk-thm-picard-pn.json`:
   its existing realized lists are empty, and this delivery neither changes those lists nor
   bypasses any realized step. The correspondence and junction route stays intact.
   Verdict: pass after removing the redundant Fin.Basic import.
5. Read the changed basic node and the existing correspondence and junction nodes. The basic
   node records k=r-1, j=tau(k), d=sigma^{-1}(j), deletion restrictions, injectivity by
   uniqueness, and surjectivity from Tuple.sort and the unique partial sort, exactly as Lean
   implements them. Its proof_deps retain sorting operators and add partial-sort uniqueness;
   proof_origin records the actual argument. No new-node fields need checking. Verdict: pass.

Changed only the redundant proof-only `Mathlib.Logic.Equiv.Fin.Basic` import and this report.
The mathematical proof was left intact. One original hole closed, zero holes added.
