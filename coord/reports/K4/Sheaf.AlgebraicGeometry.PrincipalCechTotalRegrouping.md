## What changed

Proved `AlgebraicGeometry.principalCechTotalRegroup_isIso` in
`Sheaf.AlgebraicGeometry.PrincipalCechTotalRegrouping`, without changing its signature,
existing definitions, or visibility. Added a proof-only import of
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`.

The inverse is constructed explicitly: restrict the terms to a row, transport degrees,
and use the inverse product-comparison map for evaluation of the categorical column
product. Sum these row retractions, followed by the inverse column isomorphisms and
canonical total inclusions, over the finite image of the subset-cardinality function.
Private proved helpers check the evaluated projections, row extensionality, the
same-row identity, the different-row zero composite, and the coordinate mask.
The two inverse identities follow by total extensionality and a finite sum with one
surviving row. Rows outside the image have an empty product, so their sources are zero.
This also covers r = 0 and arbitrary total degrees and coefficient complexes.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.principalCechTotalRegroup_isIso`
(node `lem-sc-principal-cech-total-regrouping`).
One hole closed, zero holes added; this is a proof, not a decomposition.
No `sorry` remains in the delivered module, and none was split off into new modules.
All new private lemmas are proved. The file compiles without warnings.

## No longer needed

None. Both original public imports and all three original definition dependencies
remain necessary. No planned theorem dependency, node, or module is pruned. The proof
implements the existing inverse-by-finite-regrouping route using Mathlib universal
properties, without introducing any further dependency on a Sheaf theorem with a hole.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The existing plan is sufficient. The Lean proof
sums over the distinct occupied rows rather than separately over all subset coordinates;
these are the same inverse because a row retraction contains all its subset coordinates.
The unit route is unchanged. No new nodes or forced adaptations are needed.


## Second reading by K4

1. **Interface: PASS.** Read the full repository/sandbox diff. The only original
   body replaced is `principalCechTotalRegroup_isIso`; all existing signatures,
   definitions, docstrings, universes, variables, and visibility remain byte for byte
   unchanged. The added Products import is plain, proof-only `import`. No target,
   public import, or statement changed; no change record is needed. The node's
   arbitrary integer-indexed F, arbitrary bicomplex B, column isomorphisms e, and
   total degree n are exactly the Lean hypotheses. No covering, boundedness, or
   horizontal compatibility hypothesis was introduced.
2. **Proof: PASS.** Compiled the delivered module through `lcompile.py`, cleanly
   in 6.6 seconds. A scratch copy with `#print axioms` for all four original
   declarations and all six added private declarations also compiled. Every result
   lists only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Inspected the explicit row retraction and the finite-sum inverse: no unproved
   existence witness supplies data, no definition contains a hole, and no forbidden
   declaration or kernel-check bypass occurs. Both inverse identities are proved.
3. **Split statements: PASS (none).** There are no new public statements, new
   holes, or split-off nodes to review. Checked the private helpers against their
   uses: evaluated product projections are jointly monic, equal-row degree
   transports cancel, distinct rows have zero intersection, and the mask recovers
   exactly the row coordinates. For r=0 both subset families are empty and every
   source row is zero; for r=1 only row 0 survives; for r=2 the occupied rows are
   0 and 1. The argument holds for negative total degrees and arbitrary complexes.
4. **Route and pruning: PASS.** Read PrincipalCechColumns and the existing plan.
   Independently searched the local Sheaf/upstream code and Mathlib total-complex
   infrastructure, and used msearch Loogle and LeanFinder with different queries.
   LeanFinder returned total.mapIso and index-transport lemmas; total.mapIso needs
   an isomorphism of bicomplexes, whereas this statement assumes only column
   isomorphisms and concludes degreewise invertibility. No shorter replacement
   was found. Both public imports occur in existing signatures/definitions; the
   new plain Products import supplies piComparison facts. All three original
   proof dependency nodes are still used, so `No longer needed: None` is complete.
   Read sk-thm-picard-duality's unit record: its realized statement and step lists
   are empty; no realized unit node is bypassed or altered. The inherited finite
   alternating Cech comparison route is preserved.
5. **DAG: PASS after clarification.** Read the complete item node, its statement,
   proof dependencies, provenance, and unit record. The old plan described sums
   of subset insertions, while the code sums the complete row retractions over
   the finite image of subset cardinality. These are mathematically the same
   inverse. Updated only `proof` and `proof_origin` to describe the actual product
   comparison, occupied-row sum, empty-row argument, and two inverse identities.
   `proof_deps` is unchanged and equals the union of the steps' uses. No new node
   is necessary, and no node statement or Lean record changed.

Second-reading changes: clarified the existing node's proof and proof provenance,
and appended this independent review. The Lean code was correct and left unchanged.
