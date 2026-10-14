## What changed
Added the coordinate helper module and imported it privately. The target theorem now applies coordinate-equivalence injectivity and the helper pointwise.

## Proved and sorry left
The target declaration `picardExternalCechCupBidegree_leibniz` is proved. The helper declaration `picardExternalCechCupBidegree_leibniz_coordinate` remains `sorry` (node `lem-sc-picard-external-cech-cup-leibniz-coordinate`) and isolates the signed face calculation.

## No longer needed
None beyond the existing bidegree import; no planned dependencies were removed.

## Where the brief, the DAG or earlier work was wrong
The face calculation is substantial, so it was split into its coordinate-level statement; the final map equality is a direct extensionality argument.

## New nodes
`lem-sc-picard-external-cech-cup-leibniz-coordinate` records the coordinate-level face identity.

## Earlier second reading (a previous round; superseded)
Pending independent second reading of the coordinate helper and target extensionality proof.

## Second reading by H3
1. I compared the delivered target module with the repository version. The theorem
   `picardExternalCechCupBidegree_leibniz` has the same signature byte for byte; only its
   proof and a private proof import changed. Verdict: pass.
2. Both delivered modules compile with `lcompile.py --all`. The target has no `sorry`; the
   coordinate helper has the one named `sorry` recorded in node
   `lem-sc-picard-external-cech-cup-leibniz-coordinate`. No forbidden declarations or hollow
   definitions occur. Verdict: pass, with that documented split hole remaining.
3. The helper statement is pointwise under the target Cech coordinate equivalence and is
   strictly simpler than the target equality, so it is a needed decomposition rather than a
   restatement. Its source, proof sketch, node, and Lean declaration agree. Searches found no
   existing declaration in the project or upstream library. Verdict: pass.
4. The target proof takes the shortest available route: injectivity of the coordinate
   equivalence followed by the helper. The existing bidegree import remains needed, and the
   helper is imported privately. No unused imports or proof dependencies were removed, and the
   unit route is retained. Verdict: pass.
5. The target node records the extensionality proof and the new node records the coordinate
   calculation and its dependency. The helper's documented source and edge cases cover
   `p = 0`, `q = 0`, empty families, and characteristic two. Verdict: pass.

I changed only this report section; no Lean statements or proofs were altered during the
second reading.

The interface addition is recorded in
`coord/changes/picard-external-cech-cup-leibniz-coordinate.md`.
