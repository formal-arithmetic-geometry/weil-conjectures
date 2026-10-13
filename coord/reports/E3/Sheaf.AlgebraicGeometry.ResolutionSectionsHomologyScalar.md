## What changed

Proved `AlgebraicGeometry.Scheme.Modules.resolutionSectionsHomology_scalar` in
`Sheaf.AlgebraicGeometry.ResolutionSectionsHomologyScalar` with its statement unchanged.
Added the proved private helper `homology_scalar_transport`: apply homology to a square
intertwining scalar natural transformations, then cancel the homology comparisons.
The degreewise square follows from `RestrictedResolutionSections.components`, module-map
linearity, restriction semilinearity, and the equality of the displayed chart ring map
with `f.app V` after `topIso`. No imports were added or removed.
Updated the existing node's proof and proof origin to the scalar-endomorphism argument.
The module compiles without warnings through the required local compiler.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.Scheme.Modules.resolutionSectionsHomology_scalar`
(node `lem-pc-resolution-sections-homology-scalar`). The private helper is also proved.
No `sorry` remains in the item's module; no holes or new modules were added.
This is a proof, not a decomposition into new unproved statements.

## No longer needed

None. The sole public import `Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices` is
needed by the existing statement and supplies the pinned degreewise comparison.
The only recorded dependency remains `def-weil-pbc-flat-base-change-open-choices`.
The argument does not need augmentation or resolution naturality, or a separately
constructed restriction-of-scalars homology comparison. No node or module for those
was present in the dependency list, so none is claimed as pruned.
The item is below the realized statements and steps of unit `sk-thm-p1`; its route is kept.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The former proof described explicit restriction of scalars;
the proof now uses scalar natural transformations and Mathlib's
`ShortComplex.homologyMap_mapNatTrans`, which avoids constructing that comparison.
The edge cases in the original docstring remain covered without extra hypotheses.
The general short-complex calculation is factored into a proved private helper so that
Lean does not repeatedly elaborate the nested scheme/evaluation expressions.

## Second reading by E3

1. **Visible declarations:** compared the delivered module with the repository version.
   The public theorem signature is byte-for-byte unchanged; only its proof, comments,
   author line, and local elaboration options changed. The DAG proof fields match the
   implemented route.
2. **Proof validity:** compiled the module with `lcompile.py`; it succeeds without
   errors or warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by` declarations. The helper and target use only the permitted existing
   library assumptions; no new unproved theorem was introduced.
3. **Statement and helper review:** the target remains exactly the scalar-transport
   statement from the node. The private helper is a genuine intermediate equality for
   homology maps, strictly more general than the target and proved from
   `homologyMap_mapNatTrans`; it is not a restatement of the target. No Mathlib or
   upstream duplicate was found in the searches recorded above.
4. **Pruning and route:** the sole public import remains needed by the target and by
   `RestrictedResolutionSections`; no unused import or proof dependency was found.
   The proof follows the unit route through the pinned degreewise comparison and keeps
   the realized unit `sk-thm-p1` statements and steps.
5. **Nodes and records:** the existing node's `proof`, `proof_deps`, and
   `proof_origin` agree with the Lean proof. No split-off holes or new nodes were added;
   the report's proved/sorry inventory is complete.

Changed during second reading: added this review section only; no Lean code or node
statement was altered.
