Files written:
- `dag/nodes/sec-picard-framework/lem-pc-direct-image-qc-support-reduction.json`: item split into three proof steps, no new nodes, no Mathlib match.
- `citations.json`: verbatim quotes for all cited statements.

Attachments:
- None. I searched `WeilConjectures/` for the item id, Tag 08EV labels, and direct-image/support terminology; no exact sorry-free declaration states this item.

WANTED:
- None; the local Stacks review checkout contains `perfect.tex` and the Tag 08EV proof.

What was incomplete in the imported item:
- The statement was correct but had no proof or proof dependencies. I supplied the finite-union proper-support reduction, quasi-compact neighborhood construction, supported-open restriction isomorphism, and derived direct-image composition argument.

## Review by F1

I read the item statement and the Tag 08EV `lemma-perfect-direct-image` proof in `/home/ubuntu/c1-stacks-review/perfect.tex`, from the paragraph introducing the union T through the equality of the two derived direct images. Step 1 uses the existing finite-union proper-support statement, whose clause (1) says exactly that the finite union of the closed proper supports is proper over S; boundedness supplies finiteness of the union. Step 2 uses the existing quasi-compact immersion-neighborhood theorem for the reduced support and the qcqs permanence theorem for the restricted locally-finite-type morphism over the Noetherian qcqs base. Step 3 uses the supported-open pushforward statement, which gives `E -> Rj_*j^*E` when all cohomology is supported in the open, and the general ringed-space derived-direct-image composition statement to identify the composite pushforward with `Rf_*E`. Every quoted sentence was checked verbatim against its node.

I checked hypotheses explicitly: each support is closed and proper by the item assumptions; the finite number of nonzero cohomology sheaves comes from boundedness; the reduced support is quasi-compact because it is proper over S; and the restricted morphism has quasi-compact source and locally finite-type structure over the Noetherian qcqs base. The identity morphism, the zero complex, and a one-degree coherent sheaf give the expected special cases. No new node was created because all non-elementary facts used by the three steps already have project statements. The cross-unit geometric inputs are recorded as tool uses in the split report.

## Not duplicates

lem-pc-direct-image-qc-support-reduction vs lem-pc-direct-image-bounded-coherent: the parent item uses this support reduction as one substep, while the present item states only the reduction and direct-image isomorphism.
lem-pc-direct-image-qc-support-reduction vs lem-pc-proper-derived-direct-image-composition: the composition node gives a general functorial composition isomorphism, while the present item adds the proper-support open restriction and applies it to E.

## Second reading by F1

- Item statement: checked against Stacks Tag 08EV, label `lemma-perfect-direct-image`, support-reduction paragraph; hypotheses and canonical restriction/direct-image isomorphism agree, including boundedness and proper supports.
- Step 1: checked against Tag 08EV and `lem-weil-pbc-closed-subset-proper-over-base-union-preimage` clause (1); finite nonzero cohomology supports form a finite proper union under the stated locally-finite-type hypothesis.
- Step 2: checked against Tag 08EV, `lemma-nagata-immersion-shrink-to-closed-exists`, `pqf-lem-locnoeth-lft`, `lem-weil-pbc-locally-noetherian-quasi-separated`, and `lem-weil-pbc-qcqs-morphism-permanence`; the restricted source is now explicitly shown quasi-separated before applying permanence.
- Step 3: checked against Tag 08EV and the statements of `lem-pc-supported-open-pushforward` and `lem-pc-ringed-spaces-derived-direct-image-composition`; the supported-open isomorphism and composition orientation give the claimed canonical map.
- New nodes: none; the item remains statement-only and every non-elementary input is an existing node or recorded tool.
- Changed step 2 and `proof_deps` to add local-Noetherianity and quasi-separatedness facts, because the prior text applied qcqs permanence without establishing that `X'` is quasi-separated.
- Changed `citations.json` to quote the two added node statements verbatim and preserve the existing permanence quote.
- Small cases checked: zero complex and empty support, identity/open restriction, a field base with one coherent sheaf in one degree, and `n=0,1` finite-support unions.
