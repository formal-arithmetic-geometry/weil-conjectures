# Worker report: lem-trf-universally-exact-fp-split — Q129

## Files written

- `lem-trf-universally-exact-fp-split.json`: retained the statement and supplied a three-step split; no new nodes and no Mathlib match.
- `citations.json`: verbatim statement quotations for every node cited by Steps 1 and 2.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter file was changed.

## Attachments

None. I searched the read-only slopmaster2 source for the exact item id, its blueprint tag, and declarations about universally exact module sequences. No sorry-free project declaration states this complete splitting result.

## WANTED

None. The source is available locally in `literature/stacks-project/algebra.tex` (Tags 058K and 058L).

## Not duplicates

No nodes were created. The closest existing node, `lem-trf-universal-injective-finite-test`, only detects universal injectivity from finitely presented tensor tests; it does not state the finite-presentation lifting/splitting conclusion. `lem-trf-tensor-kernel-factorization` invokes this item and therefore cannot duplicate it.

## What was checked and corrected

The imported node had the correct statement and source but no proof. I retained its hypotheses, including injectivity of `i`, surjectivity of `p`, the kernel-image equality, finite presentation of `C`, and tensor exactness for every module. The proof now follows the source's finite-presentation argument rather than citing a nonexistent Mathlib theorem. The required Q129 searches were rerun through `msearch.py`; all results were generic exactness or finite-presentation declarations and none states the item. The search log is `searches.jsonl`.

## Review by Q129

I read the complete item, `stages/1-dag.md`, the unit and chapter records, the current blueprint ancestry, and Stacks `algebra.tex` at Tags 058K and 058L. I also opened the statements of both cited definition nodes before writing the quotations.

Step 1 uses the finitely presented module definition and the tensor-product map definition. Since the hypothesis quantifies over every module, restricting to finitely presented test modules gives exactly the finite-test exactness condition in Tag 058K. No Noetherian, finite-generation, or flatness hypothesis is introduced.

Step 2 is the source's (2)→(3)→(4)→(5) lifting argument. I checked the finite presentation orientation `R^n -> R^m -> C`, the lift `h₂` using surjectivity of `p`, the factor `h₁` using `ker p=i(A)`, and the finitely presented test module `Q=coker(g₁)`. Tensor exactness makes the class of `h₁` vanish, producing `k₁`; subtracting `i k₁` makes `h₂'` descend to a section `s:C->B`. The final equality `p s=id_C` follows from surjectivity of `g₂`. The tensor identifications use only the cited universal property and the finite presentation definition.

Step 3 constructs the requested retraction directly from the section: for each `b`, factor `b-s(p(b))` uniquely through the injective map `i`. I checked linearity and `r i=id_A` on elements of `A`; this is the elementary section-to-retraction conversion in Tag 058L.

I tested the edge cases `C=0`, `A=0`, the identity split sequence, and a finite free quotient. The argument remains valid when `R` is the zero ring and imposes no finiteness on `A` or `B`. Every proof dependency is the union of the `uses` lists, and every citation quotation is verbatim.

## What could not be finished

None. The split and citation audit are complete; the required server dry run is the remaining gate.

## Repair of returned point

The original Step 2 used the presentation map (R^n\to R^m) as though its coefficient matrix directly gave the relation map in the opposite direction; this made the claimed tensor quotient and factorization of (h_1) dimensionally invalid. I replaced it with Tag 058K's orientation: if (g_1(e_i)=\sum_j a_{ij}d_j), the test presentation is (R^m\xrightarrow{t}R^n\to Q\to0), (t(d_j)=\sum_i a_{ij}e_i). The vector of (h_1(e_i)) then has image in (B^n) equal to the image of the relation map from (B^m), so its class vanishes in (B\otimes_R Q); finite-test injectivity gives the required (z_j) and hence (k_1g_1=h_1). I added the existing node `lem-trf-universal-injective-finite-test` to Steps 1 and 2 and to `proof_deps`, with verbatim citations. I reread that node's statement and Tag 058K's proof at `literature/stacks-project/algebra.tex:19818-19858` before making the correction.
