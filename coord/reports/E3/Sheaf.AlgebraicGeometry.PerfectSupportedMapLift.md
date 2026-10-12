## What changed

`Sheaf.AlgebraicGeometry.PerfectSupportedMapLift` now proves
`AlgebraicGeometry.Scheme.exists_perfect_supported_map_lift` from the finite stabilized
construction. Its signature and existing docstring are unchanged. The private proved
`stabilization_split` gives both retraction and map compatibility by induction, using
biproduct inclusions/projections and the stabilization isomorphisms. The final proof
transports these maps through the construction isomorphism and checks both equations.

Added `Sheaf.AlgebraicGeometry.PerfectSupportedStabilizedLift` for the unfinished finite
cover/gluing construction, with an explicit sequence of objects, stabilization isomorphisms,
and first-projection maps. It asserts no retraction or summand property. This isolates
the construction in steps 1–4 of the original plan from the final categorical calculation;
it retains all three original inputs and the unit route. No existence witness is used to
define data: the sequence and its maps in the main proof are genuine `Nat.rec` constructions.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.exists_perfect_supported_map_lift`
(node `lem-sc-perfect-support-map-lift`). The private `stabilization_split` is fully proved.
There are no remaining sorries in the item's module.

Added one hole: `AlgebraicGeometry.Scheme.exists_perfect_supported_stabilized_lift`
(node `lem-sc-perfect-supported-stabilized-lift`). This is a decomposition: one upper hole
closed, one construction hole added, net zero holes removed. The finite cover construction,
restriction comparisons, and locality of perfectness/support remain to be formalized.
The new theorem is a construction invariant with an explicit finite iterated stabilization,
not the original summand theorem renamed. Its conclusion lacks the two summand maps and
their equations, which the main module proves by a separate induction.

Both modules compile without errors or warnings through lcompile.py. Edge cases checked
in the mathematical construction: zero attachments take n=0; empty U, zero source, empty T,
and T=X are allowed. The private induction base and successor are checked by Lean.

## No longer needed

Removed the direct proof imports of `Sheaf.AlgebraicGeometry.AffinePerfectMapLift`,
`Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension`, and
`Sheaf.AlgebraicGeometry.DerivedOpenGluing` from the item. They are retained by the new
construction module and its proof plan, so none of these modules or their nodes is
pruned from the target closure. No other node or module is no longer needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The DAG describes the last direct-summand
calculation after one affine attachment; over a general finite affine cover the source on U
is repeatedly stabilized. This iteration is now explicit, and the summand calculation
handles every number of attachments. The local literature file named by the node was
unavailable on this clone, so the Stacks pages for Tag 09IM and its surrounding results
were read directly. LeanSearch returned Internal Server Error; LeanFinder, Loogle,
Mathlib grep and blueprint/node searches were also attempted.

## New nodes

`lem-sc-perfect-supported-stabilized-lift` in
`dag/nodes/sec-picard-framework/lem-sc-perfect-supported-stabilized-lift.json`
records the finite affine-cover construction before the summand calculation, in the same
chapter and unit as the item. Its declaration is in
`lean/Sheaf/AlgebraicGeometry/PerfectSupportedStabilizedLift.lean`.
No statement or definition changes, change records, or forced adaptations.

## Second reading by E3

1. Compared the delivered item module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only proof text and proof imports changed. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. There are no errors or warnings. The item has no remaining `sorry`; the only remaining `sorry` is the named construction theorem, recorded with its DAG node. No forbidden declarations or hollow definitions were introduced. Verdict: pass.
3. Checked the split construction statement and node against the Lean theorem. It is a strictly simpler finite-stabilization construction: it does not assert a retraction or rename the item theorem, and its hypotheses and conclusion match the recorded node. Edge cases (including zero attachments) are covered by the stated construction. Verdict: pass.
4. Reviewed the proof route and imports. The item uses the new stabilization node and the elementary induction/transport proof; the affine and gluing imports are retained by the construction module. No shorter available library declaration was found, and the unit route remains the finite-cover construction followed by the summand calculation. Verdict: pass.
5. Checked DAG agreement: proof steps, proof dependencies, proof origin, Lean declaration, and unit/chapter metadata match the delivered modules. The unit's realized route is unchanged. Verdict: pass.

Changed during second reading: appended this review section only; no Lean proof or statement changes were needed.
