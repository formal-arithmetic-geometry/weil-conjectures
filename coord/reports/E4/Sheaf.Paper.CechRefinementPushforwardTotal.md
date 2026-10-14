## What changed

Removed the duplicate top-level `cech_coefficient_apply` declaration that caused
`import_prune_check.py` to reject the landing. Its component calculation is now a
local helper inside `exists_cechRefinement_pushforward_total`, where it is used at
the beta square. The target theorem and all public signatures are unchanged.

This delivery adds Sheaf.Paper.CechPushforwardTupleTotal, its concrete cechPushforwardTupleMap and proved component formula, and the named tuple-total obligation. The item adds import Sheaf.Paper.CechPushforwardTupleTotal, three private helpers, local elaboration attributes and scoped proof options. Its node proof, proof_deps and proof_origin are updated; the change record is coord/changes/cech-pushforward-total-proof-elaboration.md.

## Proved and sorry left

Replaced the sorry in AlgebraicGeometry.Scheme.Modules.exists_cechRefinement_pushforward_total with a proof using the new obligation AlgebraicGeometry.Scheme.Modules.exists_unique_cechPushforward_tuple_total (node lem-sc-cech-pushforward-tuple-total). One hole is closed and one is added: this is a decomposition. cechPushforwardTupleMap_apply and the three private helpers are proved.

## No longer needed

The duplicate private top-level `cech_coefficient_apply` declaration is no longer
needed. No import or dependency was removed. The proof adds the plain import Sheaf.Paper.CechPushforwardTupleTotal.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery redeclared a theorem whose statement already exists in the
library, which the landing prune check correctly rejected. The repaired proof
keeps the calculation local to the target proof and therefore does not publish a
duplicate declaration.

## New nodes

`lem-sc-cech-pushforward-tuple-total` is added by this delivery in module `Sheaf.Paper.CechPushforwardTupleTotal`. It states the unique total cochain map determined by explicit restriction maps on every summand, without augmentations or resolutions. Its remaining proof obligation is named above. Change record: `coord/changes/cech-pushforward-total-proof-elaboration.md`.

## Earlier second reading (a previous round; superseded)

Repair review: the target module compiles with the duplicate declaration removed,
and the local helper has the same component calculation. Public signatures and the
lower tuple-total module are unchanged. The existing change record remains
`coord/changes/cech-pushforward-total-proof-elaboration.md`.


## Earlier second reading (a previous round; superseded)

1. The delivered module was diffed against the repository. Existing theorem and definition signatures are unchanged byte for byte; the only implementation changes are proof-local helpers, local attributes, and proof options. Verdict: pass.

2. Both modules compile through `lcompile.py`; the target has no `sorry`, and the only remaining `sorry` is the named lower theorem `exists_unique_cechPushforward_tuple_total`, recorded in the new node lem-sc-cech-pushforward-tuple-total. No forbidden declarations or hollow definitions were introduced. Verdict: pass.

3. The target proof uses the new tuple-total obligation and proves the two augmentation squares by explicit component calculations, then transports them through homology naturality. The lower split statement is a strict, independently useful construction of the total cochain map and is added by this delivery. Verdict: pass.

4. The proof follows the unit route through `exists_unique_cechPushforward_tuple_total`; no proof dependency import was removed, and the duplicate public helper from the earlier attempt is absent. Verdict: pass.

5. The DAG node for the target matches the Lean declaration, proof dependencies, and proof origin; the lower node matches its module and remaining hole. The delivery adds lem-sc-cech-pushforward-tuple-total; its Lean signature matches the node, including arbitrary K, uniqueness and every summand equation. Verdict: pass.

Changed during this reading: added this review record only; no Lean or DAG edits were necessary.

## Second reading by E4

1. Compared the delivered target module with the repository version. Existing declaration
   signatures are unchanged; the added import and proof-local helpers are declared in this
   report. Verdict: pass.

2. Compiled both delivered modules with `lcompile.py`. The target has no `sorry`; the sole
   remaining `sorry` is the named theorem `exists_unique_cechPushforward_tuple_total`, with
   node `lem-sc-cech-pushforward-tuple-total`. No forbidden declarations or hollow
   definitions occur. Explicit axiom printing gives only `propext`, `Classical.choice`,
   `Quot.sound` and (for the upper theorem) `sorryAx`. Verdict: pass.

3. Checked the target proof componentwise: the tuple map formula, zero component, coefficient
   naturality, and forgotten-scalar homology square establish both required equalities. The
   split lower statement is a strictly smaller construction obligation and is true as stated.
   Empty indexing families yield zero tuple groups; degree zero has the sole (0,0)
   summand; identity refinement gives identity restrictions. Independent searches via
   leanfinder, loogle and grep found general total-map APIs, but none constructs this
   cross-scheme map. Checked against Stacks Tag 01FD. Verdict: pass.

4. The proof follows the unit route through `exists_unique_cechPushforward_tuple_total` and
   retains the required tuple-total import. No unused proof dependency was identified.
   Verdict: pass.

5. Checked the target and lower DAG nodes against their Lean declarations, including proof
   dependencies and origins. The unit realization remains intact. Verdict: pass.

Changed during this reading: appended this second-reading record only; no Lean or DAG edits
were necessary.
