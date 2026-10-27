## What changed

Pruned the unused auxiliary theorem
WeilConjectures.PurScalarProjection.native_scalar_identification from
Sheaf.Paper.CompactSupportScalarProjectionIdentification. No other Lean text changes:
all remaining declarations, definitions, proofs, imports and attributes are identical.

This is a pruning delivery, not a proof of the withdrawn auxiliary. The actual
replacement argument is already present in the current source. gamma_identification
proves the integral scalar-mate identification from its finite counit equations and
the constructible Milnor injection. compactSupportScalarProjectionIdentification
conjugates ordinaryCompletedSquare by the canonical realizations and uses that gamma
identification. diagram_projection reduces compactSupportProjectionCoefficientChange
and postcomposes with nativeRealization. None uses the withdrawn whole-diagram
scalar-coherence equation. nativeRealization itself remains because the finite
projection theorem uses it.

Updated the item's Step 7 to this actual argument and removed the unused theorem's
Lean attachment. The node's statement and the blueprint unit route are unchanged.
The only DAG parent, lem-pur-compact-support-integral-coefficient-comparison, cites
this node in Step 5 for the retained finite and integral projection squares. Its
required declarations remain verbatim. The unit realization records do not require
the withdrawn auxiliary. Searches covered the entire Lean tree, node dependency
fields and proof-step uses, the unit records, current rework and repair records.
There are no direct Lean importers of the item module and no other declaration-name
references. No parent module or adopted source-library module is modified.

Change record: coord/changes/E4-prune-unused-native-scalar-identification.md.

## Proved and sorry left

Starting item: 1 sorry, in
WeilConjectures.PurScalarProjection.native_scalar_identification
(node lem-pur-compact-support-scalar-projection-identification).

Removed that hole by pruning the unused declaration. Theorems newly proved: 0.
Holes closed by pruning: 1. Holes added: 0. Split-off holes: 0.
Remaining item sorries: 0. All existing proved declarations remain unchanged.
The imported library still has its previously existing proof obligations; no
claim of axiom closure for the complete target dependency graph is made.

Validation: launcher single-file compilation and delivery preflight.

## No longer needed

- WeilConjectures.PurScalarProjection.native_scalar_identification: its whole-system
  scalar square is unnecessary for either the finite projection square or the
  integral projection square, by the replacement argument above.
- The direct Step 7 branches through lem-pur-perfect-quotient-exchange-normalization,
  lem-weil-pbc-mate-pasting, lem-pur-tower-limit-transpose-normalization and
  lem-pur-compact-support-roos-cofinality are removed from this node's proof_deps.
  Existing uses of these nodes elsewhere remain. In particular scalar-limit
  foundations still use Roos cofinality; no global withdrawal of that module is
  claimed.
- Removed the now-obsolete lem-weil-pbc-mate-pasting entry from tool_uses, preserving
  the order of the other approvals.

No import is removed. No module or existing DAG node is withdrawn. No new node
or split-off statement is delivered.

## Where the brief, the DAG or earlier work was wrong

The remaining hole was an obsolete auxiliary route. The node's old Step 7 still
planned a whole-diagram augmentation/transposition proof, even though the later
proved gamma_identification component already used finite counits and constructible
Milnor detection, and diagram_projection had an independent direct ordinary proof.
Their current source proofs remove the mathematical need for that auxiliary.
The brief's instruction to prune below unit level applies: the node statement,
unit route, main projection theorem, finite projection theorem and completion-unit
normalizations all remain intact.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
