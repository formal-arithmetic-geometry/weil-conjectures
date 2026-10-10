Files written:

- `dag/nodes/sec-picard-framework/lem-sc-affine-perfect-koszul-principal-unit.json` — statement, no new child nodes, Mathlib no match.

Attachments: none.

WANTED: none; the local review packet `/home/ubuntu/c1-stacks-review/perfect.tex` supplies Section `section-koszul` and Tag 08CX.

What was checked and changed: the source checkout was searched for the blueprint tag, declaration names, and the notions "perfect", "Koszul", and "principal open"; no exact sorry-free declaration exists. The DAG was searched for Tag 08CX, the Koszul/perfectness clauses, and their key words; no existing node states this combined item. I therefore did not create a child node: a child for finite-free perfectness or a child for principal-open restriction would each restate a clause of the item. The item retains its imported statement and dependencies. Its proof now has three steps: finite bounded free terms imply strict perfectness using `def-pc-perfect-complex` and the explicit exterior-power basis in `def-weil-pbc-koszul-complex`; localization at each `f_i` gives the explicit contraction and hence the augmentation quasi-isomorphism; and the principal opens cover U, with r=0 and r=1 checked separately. The cited statements were opened and matched: the perfect-complex node defines strictly perfect complexes as bounded complexes of finite free summands, and the Koszul node gives the exterior-power terms and differential formula. `citations.json` quotes those statements verbatim. The three required Mathlib searches were run for the item: LeanFinder returned unrelated smoothness declarations and no match, Loogle returned zero hits with unknown `IsPerfect`, and Mathlib grep returned zero hits; LeanSearch was also run and recorded unavailable. No source or Lean files were modified.

## Review by G1

I read the item source in `/home/ubuntu/c1-stacks-review/perfect.tex`, including the construction at Section `section-koszul` and the principal-open assertion identified as Tag 08CX. I also read the full statements of `def-pc-perfect-complex` and `def-weil-pbc-koszul-complex` before writing the proof. Step 1 uses exactly the latter node's finite exterior-power basis and the former node's definition of a bounded strictly perfect complex; its hypotheses are the commutative ring A and the finite list of generators already introduced by the item. Step 2 uses exactly the Koszul differential formula to write the contraction after f_i is inverted; the unit equation supplies the homotopy identity, so no regularity or Noetherian hypothesis is being smuggled in. Step 3 uses only the definition of U as the union of the D(f_i), and I checked the degenerate r=0 case and the one-generator r=1 two-term complex. I removed an unnecessary citation of `def-pc-scheme` from the proof steps because the cover conclusion is immediate from the item's own definitions. The DAG and blueprint searches found no duplicate or more general existing node, and the Lean source search found no attachment. Since no new node was created, there are no additional node statements or sources to review.

## Second reading by G1

- Item statement: checked against `perfect.tex`, Section `section-koszul`, Situation `situation-complex`, and Tag 08CX; definitions of `X`, `U`, `I^\\bullet`, the augmentation, and exponent hypotheses agree, including empty and singleton lists.
- Step 1: checked against `def-pc-perfect-complex` and `def-weil-pbc-koszul-complex`; bounded finite-free terms and the affine strictly-perfect criterion are stated there, with the finite-free/direct-summand observation elementary.
- Step 2: checked against the Koszul differential formula and the source's principal-open contraction; after localization `f_i^e` is a unit and the displayed contraction identity is the direct calculation.
- Step 3: checked against the principal-open union definition and the source's local quasi-isomorphism conclusion; the local criterion is used, with `r=0` and `r=1` tested explicitly.
- New nodes: none; B1-B7 and duplicate checks are therefore not applicable. No new Mathlib leaf was made; all recorded searches are present in `searches.jsonl`.

Changes made: none to the mathematical statement or proof. The existing `created` metadata is maintainer-owned and will be preserved by `deliver.py`; the dry run passed preflight.
