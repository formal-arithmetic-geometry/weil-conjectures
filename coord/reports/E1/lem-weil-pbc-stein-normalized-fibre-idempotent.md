# Stage 1 delivery report: `lem-weil-pbc-stein-normalized-fibre-idempotent`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-stein-normalized-fibre-idempotent.json`: split along the normalized affine part of More on Morphisms Theorem 37.53.5 (Tag 03H2), with nonemptiness from the Tag 03GY universal factorization and connectedness from the proper-fibre idempotent route.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-stein-fibre-idempotent-image.json`: new unsplit public lemma exposing the full Tag 0G7X statement that a proper-fibre idempotent comes from the pushforward stalk.

## Sources and proof route

The parent follows `more-morphisms.tex` Tag 03H2, lines 15312--15357. The proper-fibre idempotent image statement is the public Tag 0G7X interface; its formal-functions construction and arbitrary-base approximation remain below that unsplit node for later Stage1 work. The normalized contradiction cites the existing proper/qcqs, quasi-coherent pushforward, relative-spectrum and affine tilde/global-sections nodes. No private lemma is cited.

## Work status

No Lean was written or compiled. The new nodes are statement-only (`unsplit`) and each has LeanSearch, LeanFinder/Loogle, and Mathlib grep records with no exact match. No existing target statement was changed.

## Problems found

The initial draft incorrectly treated the completion of a finite algebra over a local ring as local. That assertion is false without the normalized pushforward hypothesis; it was removed. The corrected proof first obtains a stalk lift by Tag 0G7X and then uses the cited normalized identification with the local base ring, followed by the explicit zero-or-one contradiction.

## Unfinished

None.

## Review by E1

I checked the repair against More on Morphisms Theorem 37.53.5 (03H2) and Derived Categories Lemma 21.16.1 (0G7X). The parent now uses only the proper-fibre idempotent image interface, cites public proper/qcqs, pushforward quasi-coherence, relative-Spec, and affine tilde/global-sections nodes, and explicitly concludes that the lifted local idempotent is 0 or 1 before invoking the two-nonempty-clopen contradiction. The sole new child is statement-only, has the exact source and `created.item` equal to this item, and the parent split report is complete. No unresolved tag, private module, or Lean change remains.
