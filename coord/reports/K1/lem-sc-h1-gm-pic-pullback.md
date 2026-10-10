Files written: `dag/nodes/sec-curve-estimates/lem-sc-h1-gm-pic-pullback.json`; no new nodes; `citations.json`.

Attachments: none.

WANTED: none.

The target had no sorry-free declaration with the exact statement in the slopmaster2 source. I checked `GmPicard.lean` and found the closed declarations for the Picard-to-etale-H¹ bijection, but no pullback naturality theorem. The existing dependency `lem-sc-torsor-h1-functoriality` is Zariski-only, so I removed it from `stmt_deps` and used the etale torsor classification plus the general cohomology-pullback naturality node instead. No new node was needed: the Isom-torsor pullback is a direct calculation from the module-pullback definition.

## Review by K1

I read the item's source citation, Stacks Tag 040E, the imported `lem-sc-h1-gm-pic` statement, `lem-sc-torsor-h1`, `def-pc-module-pullback`, `def-weil-pbc-inverse-image`, `lem-weil-pbc-cohomology-pullback-functorial`, and the degree-zero node. Step 1 uses exactly the Picard-to-Isom-torsor clause and the etale torsor/H¹ bijection. Step 2 is the local tensor-product calculation defining pullback of modules; the inverse-image unit supplies the coefficient comparison. Step 3 uses the torsor cocycle description and the stated naturality equation for cohomology pullback; the identification with the Picard pullback is then the same Isom-torsor clause. Step 4 uses the degree-zero pullback clause verbatim. I checked the identity morphism and the structure morphism from a point as small cases: the Isom torsor and global-unit map reduce to the expected identity and unit restriction maps. The prior Zariski-only citation was corrected before writing the split.

## Second reading by K1

- Item statement: checked against Stacks Tag 040E (Lemma 21.6.1) and the cohomology-pullback definitions; the Picard, torsor, coefficient-comparison, and degree-zero clauses have the required hypotheses and objects.
- Step 1: checked against `lem-sc-h1-gm-pic` and `lem-sc-torsor-h1`; both explicitly provide the etale Isom torsor and its H¹ class.
- Step 2: checked against `def-pc-module-pullback` and `def-weil-pbc-inverse-image`; the tensor-product description and inverse-image comparison supply the local identification. Identity and point-morphism cases give the expected torsor and unit restriction.
- Step 3: checked against `lem-sc-torsor-h1`, `lem-weil-pbc-cohomology-pullback-functorial`, and `lem-sc-h1-gm-pic`; the cocycle pullback is explicit and the step is non-elementary because it proves the central naturality compatibility.
- Step 4: checked against `lem-weil-pbc-cohomology-pullback-degree-zero`; it gives exactly global sections and pullback of units.
- New nodes: none; B1-B7 and duplicate/Mathlib checks therefore introduce no auxiliary statement. Recorded searches found no Mathlib Picard/H¹ pullback declaration.

Changes: corrected the node's `created.item` provenance to this item and changed Step 3 from elementary to non-elementary because its cocycle/naturality argument is substantive. The prior incorrect Zariski-only dependency remains removed.
