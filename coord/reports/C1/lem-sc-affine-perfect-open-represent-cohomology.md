1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-affine-perfect-open-represent-cohomology.json` (item, split; Mathlib no match).
- `dag/nodes/sec-picard-framework/lem-sc-affine-perfect-koszul-principal-unit.json` (statement, unsplit; Mathlib no match).
- `dag/nodes/sec-picard-framework/lem-sc-affine-koszul-cech-derived-comparison.json` (statement, unsplit; Mathlib no match).

2. Attachments: none.

3. Source read: `/home/ubuntu/c1-stacks-review/perfect.tex`, Tags 08CX, 08DC, 08DD, 08D1, and 08D2. The repository literature packet is absent, but the local review packet supplies the cited source.

4. The item has no matching declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; the only nearby Lean declarations concern unrelated direct-image perfect loci. The existing affine map-lifting node uses this item as a black box and does not state it. No existing DAG node states the finite-power Koszul representability proposition; the existing Koszul nodes concern regular sequences or orthogonality and are not duplicates.

## Review by C1

I read the target node, its ancestor `lem-sc-finite-duality`, the unit record, and the already split `lem-sc-affine-perfect-map-lift`. Step 1 uses the new Koszul principal-unit statement, which explicitly supplies both perfection of every `I_e` and the restriction isomorphism. Step 2 uses the Koszul-complex definition for the explicit transition-map calculation. Step 3 uses the strictly weaker Koszul-Cech derived-comparison node and the affine derived equivalence, rather than a node restating the item. Step 4 uses the degree-zero identification and checks the zero and empty-cover cases. I verified all new node dependencies exist in the DAG, searched the whole DAG and blueprint for duplicates, searched the Lean source for the blueprint tag and relevant names, and ran the required LeanFinder, Loogle, and Mathlib grep searches for the item and each new node.

5. Nothing remains unfinished.

## Second reading by C1

- Item statement: checked against Tags 08CX, 08DC, and 08DD; corrected the truncated sign-reversed Koszul definition and made the triangle and comparison map explicit.
- Step 1: checked against Tag 08CX and the principal-open contraction; the cited node states perfectness and restriction isomorphism.
- Step 2: checked against Tag 08CX equation-system; replaced the unsupported elementary claim by the explicit basis multiplier and cited the Koszul definition.
- Step 3: checked against Tags 08D1 and 08D2; removed the node that merely restated the item and cited the weaker complex comparison.
- Step 4: checked against Tag 08DC; compatibility and empty/zero checks are elementary.
- Principal-unit node: checked against Tag 08CX; made it self-contained, corrected `K[-1]` to the source's truncated sign-reversed complex, and rewrote notation in TeX.
- Koszul-Cech comparison node: checked against Tags 08D1 and 08D2; made it self-contained and acyclic with no circular dependency.

Changes made: fixed `created.item`; replaced section-only source places by Stacks tags and labels; removed `lem-sc-affine-koszul-hom-colimit-sections`; added `lem-sc-affine-koszul-cech-derived-comparison`; repaired citations and proof dependencies; and recorded the source packet location.

## Not duplicates

`lem-sc-affine-koszul-cech-derived-comparison` vs `lem-pc-qcoh-truncation-derived-limit`: both cite Tag 08D1 in the source history, but the new node compares Koszul Hom complexes with alternating Cech derived sections, whereas the existing node reconstructs a complex from its truncation tower; their statements and roles are different.
