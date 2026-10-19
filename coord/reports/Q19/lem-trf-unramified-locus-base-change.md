# Stage-1 report: lem-trf-unramified-locus-base-change

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-unramified-locus-base-change.json`: item split, no new nodes; Mathlib searches found only algebra-level `Algebra.unramifiedLocus` results, so no Mathlib leaf.
- `citations.json`: verbatim quotes for both cited DAG nodes in step 2.
- `report.md`: this report.

## Attachments

No sorry-free project declaration states this item exactly. The source checkout contains no declaration tagged `(blueprint: lem-trf-unramified-locus-base-change)`.

## WANTED

None.

## What was checked and corrected

The imported statement was compared with `literature/stacks-project/morphisms.tex`, Tag 0475 (lines 7938--7980), and Tag 02GF (lines 7875--7936). It is correct as written: local finite type is the only hypothesis, the fibrewise set is open, its formation commutes with arbitrary base change, and the local-ring/residue formulation uses the actual residue map. I checked the edge cases of an empty source, an open immersion, a finite separable field extension, and a ramified or inseparable field extension. No statement correction was needed.

The whole DAG and blueprint were searched for Tag 0475, Tag 02GF, and the unramified-locus wording. No existing node states this same scheme-level locus theorem, and no new node was created. The existing node `lem-trf-unramified-maximal-ideal-residue-criterion` is a pointwise ring criterion, not a locus or base-change theorem; it is cited only for the local characterization. The existing Mathlib leaf `lem-weil-pbc-lft-base-change` supplies local finite type for the scheme-theoretic fibre and is declared as an off-unit generic tool use.

## Review by Q19

I read the item source in `morphisms.tex` at Tags 0475 and 02GF, the statements of `lem-weil-pbc-lft-base-change` and `lem-trf-unramified-maximal-ideal-residue-criterion`, and the unit route through `lem-trf-nodal-open-locus`, which uses this item. Step 1 follows Tag 0475 directly: the union defining `W_h` has the same points as the source-neighbourhood unramified locus, Tag 0475 identifies that locus with fibrewise unramified points, proves it is open, and gives the inverse-image formula after every base change. Step 2 verifies the hypotheses of the cited base-change leaf for the fibre map, then applies the cited maximal-ideal criterion with base local ring `κ(s)`. Since its maximal ideal is zero, equality of maximal ideals is exactly that the fibre local ring has zero maximal ideal, equivalently that the canonical residue map to `κ(z)` is an isomorphism; the remaining condition is finite separability of `κ(z)/κ(s)`. I checked that the quotes in `citations.json` are verbatim portions of the cited statements and that `proof_deps` is exactly the union of step uses. The only change from the imported node is the completed proof, blueprint metadata, split report, and citations file; no hypotheses or conclusions were changed.

## Not duplicates

No new nodes were created, so there are no new-node duplicate pairs.
