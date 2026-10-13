## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.cechPrefixDeletionBijection` with a
reduction combining `prefixDeletionExistence` and `prefixDeletionRestrictions`.
The original signature, the two `CechPrefix*` subtype definitions and their visibility
are byte for byte unchanged. The two new modules are proof-only imports of the item.
Their signatures use the filtered subtypes inline, avoiding duplicate public aliases
and an import cycle with the item. Both have complete natural-language proofs and nodes.
No definition chooses data from an unproved existence theorem.

## Proved and sorry left

Hole closed in the item: `AlgebraicGeometry.Scheme.cechPrefixDeletionBijection`
(node `lem-pc-alternating-cech-prefix-deletion-bijection`). Its proof is a genuine
combination of two proper subclaims, but still depends on their `sorry`s.

Holes added and left:

- `AlgebraicGeometry.Scheme.prefixDeletionExistence`
  (node `new-prefix-deletion-existence`): existence of the equivalence and only
  its prefix-length/deleted-label facts; does not assert either restriction identity.
- `AlgebraicGeometry.Scheme.prefixDeletionRestrictions`
  (node `new-prefix-deletion-restrictions`): the two restriction identities for
  any equivalence already satisfying the base facts; does not construct an equivalence.

This is a decomposition, not an axiom-free proof: one original hole closed, two
added, local net -1. Neither helper was closed during the second reading.
The unchanged sorting-operators module has no holes added by this delivery.

Local compilation of all three delivered modules passed without warnings.
Explicit `#print axioms` in scratch copies reports `propext`, `Quot.sound` and `sorryAx` for each open
helper and the item's reduction, and only `propext` and `Quot.sound` for the
two subtype abbreviations. The delivery tool independently probes every
declaration. No forbidden declarations or sorry-bearing definitions occur.

## No longer needed

No existing imported module is pruned. The original plan's direct proof dependency
`def-pc-alternating-cech-sorting-operators` is replaced by the two new intermediate
nodes; it remains their statement/proof dependency and the item's signature import.
The unnecessary public import of `PrefixDeletionExistence` in the new restrictions
module is removed; that signature needs only the sorting-operators module.
The unchanged sandbox copy of `AlternatingCechSortingOperators` is removed from
this delivery. Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The first attempt lacked full proof docstrings for both new holes. Their node
`statement` fields were just module names and their Lean records lost newlines
around `let` expressions, so they were not verbatim signatures. Its restriction
proof sketch also missed the crucial uniqueness argument: the supplied equivalence
need not be the constructed deletion map. Stable sorting uniquely enumerates the
(value,label) pairs; partial sorting uniquely enumerates the remaining labels after
the prescribed prefix. These two uniqueness facts identify its output permutations.
All of these defects are repaired. The report previously called the item proved
without making the decomposition and its net increase of holes explicit.

The source [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
introduces the stable/partial permutations and omits the homotopy verification.
The helper docstrings supply the agent-written combinatorial details of that
omitted verification; they are not claimed to be separately stated Stacks lemmas.

## New nodes

`new-prefix-deletion-existence` and `new-prefix-deletion-restrictions` have
self-contained mathematical statements, full proof steps, sources, creation and
blueprint ancestry, the item's chapter/unit, exact Lean signatures, and fresh
LeanSearch (unavailable: Internal Server Error), Lean Finder, Loogle and grep searches. Searches found `Tuple.sort`,
`finSuccAboveEquiv`, `Equiv.Perm.decomposeFin` and ordered-list insertion/erasure
infrastructure, but no theorem asserting either filtered correspondence.
The local library already has `cechPartialSort_existsUnique`, sorting uniqueness
via `Tuple.eq_sort_iff`, and `Fin.signed_face_permutation`; these give useful
infrastructure, not the full deletion/insertion filters or restriction theorem.

## Second reading by B3

1. **Interfaces:** Compared every existing delivered module with the repository
   using `diff`. Only two plain proof imports and the theorem proof differ in the
   item; all existing signatures, definitions, docstrings and visibility are
   unchanged. The sorting-operators copy was identical and removed. No existing
   external module is adapted and no change record is required. Verdict: pass.
2. **Proof and axioms:** Compiled all three final modules through `lcompile.py`;
   audited explicit `#print axioms` in scratch copies; checked for forbidden
   constructs and all sorry occurrences. Exactly the two reported named public
   theorems remain sorry, with full docstrings and matching nodes; no data hole
   or arbitrary witness-based definition exists. Verdict: valid decomposition,
   not a completed axiom-free proof.
3. **New subclaims:** Checked the deletion/insertion and uniqueness arguments,
   including p=0, b=0, b=p, constant/repeated values and the vacuous empty-I case.
   Independently tested all 1,089 tuples with values in {0,1,2} and lengths 2–6:
   13,941 outgoing indices, all restriction identities, inverse insertion and
   equality of incoming/outgoing sets passed. Enumerated all permutations in
   lengths 2–4 to check uniqueness of stable/partial sorting. These finite tests
   supplement the written general arguments, not replace Lean proofs. Ran fresh
   LeanSearch (service unavailable)/Lean Finder/Loogle/grep searches with different queries and read related
   upstream/local sorting and signed-face modules. Neither helper restates the
   full item: one supplies existence/base facts, the other deduces restrictions
   from base facts. Verdict: true, needed, strictly smaller subclaims.
4. **Route and pruning:** The reduction really combines both helpers for the
   same equivalence. No readily applicable library theorem closes the filtered
   correspondence; proving the restrictions still needs the finite-permutation
   restriction construction and transport of the sorting predicates. Imports
   are minimal for the delivered reduction and signatures. The old direct DAG
   sorting dependency is reported above and remains transitively needed. Read
   `dag/units/sk-thm-picard-pn.json`; its route and `realized` are unchanged, and
   this item is below the unit level. Verdict: pass, no module pruning.
5. **DAG agreement:** Checked the item's proof steps/dependencies against the
   Lean calls. Repaired both new mathematical statements, exact Lean signatures,
   proof steps (including uniqueness), provenance and search records. Both new
   nodes carry all required metadata. Verdict: pass after repairs.

Second-reading changes: completed proof docstrings; repaired node statements,
verbatim Lean records and proof descriptions; removed duplicate public subtype
aliases and the redundant helper import; removed the identical sorting module
copy; corrected hole accounting and dependency/pruning notes. The item proof
itself was correct and retained.
