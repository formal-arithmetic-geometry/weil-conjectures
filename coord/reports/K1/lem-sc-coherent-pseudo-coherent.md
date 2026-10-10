Files written:

- `dag/nodes/sec-picard-framework/lem-sc-coherent-pseudo-coherent.json`: item split into one proof step; no new nodes; Mathlib searches found no matching theorem.
- `citations.json`: verbatim statement quotations for both proof dependencies.

Attachments: none.

WANTED: none.

No statement error or source error was found. The imported item was unsplit even though the existing node `lem-sc-coherent-affine-free-resolution` supplies the exact local finite-free resolution needed by the definition. No new node was created because this is an existing, strictly stronger local statement.

## Not duplicates

No new nodes were created, so there are no duplicate pairs.

## Review by K1

I read the item source, Stacks Project `perfect.tex`, Tag 08E8 (`lemma-identify-pseudo-coherent-noetherian`), including its locality argument. The item hypotheses are exactly a Noetherian scheme and a coherent module, and the conclusion is the degree-zero complex being pseudo-coherent. I also read the complete statements of `lem-sc-coherent-affine-free-resolution` and `def-pur-pseudo-coherent-complex`. The former states that for every point of a Noetherian scheme and coherent sheaf there is an affine neighbourhood with a bounded-above complex of finite-rank free sheaves quasi-isomorphic to the sheaf in degree zero; the latter defines pseudo-coherence by precisely this local condition. Thus step 1 cites both statements for the exact facts it uses, with no hidden hypothesis. The step is non-elementary because it invokes the existing resolution theorem; its final application of the definition is direct. I checked the point case (a finite free module over a field) and the empty scheme case (the condition is vacuous). The Mathlib searches were run through `msearch.py`: LeanFinder returned only generic finite-type/presentation declarations, Loogle and grep found no pseudo-coherence declaration, and LeanSearch was unavailable.

The delivery dry run is complete once the repository's unit-realization prerequisite is available; the item itself is fully split and mechanically valid.

## Second reading by K1

- Item statement: checked against Stacks `perfect.tex`, Tag 08E8 (`lemma-identify-pseudo-coherent-noetherian`), including the Noetherian/coherent degree-zero specialization; verdict correct hypothesis by hypothesis.
- Step 1: checked against Tag 08E8's locality argument and the statements of `lem-sc-coherent-affine-free-resolution` and `def-pur-pseudo-coherent-complex`; each cited statement supplies exactly the local finite-free resolution and defining criterion; verdict correct and non-elementary.
- New nodes: none; no duplicate, restatement, or Mathlib leaf was introduced. Existing resolution node was searched and reused.
- Edge cases: the zero sheaf and empty scheme are vacuous, while a point over a field reduces to a finite-dimensional vector space with a finite-free resolution; all behave as stated.
- Changes: corrected `citations.json` to quote the current base statement of `def-pur-pseudo-coherent-complex` verbatim (its Tags 08CB, 08E5, and 08E7 wording), fixing the delivery citation check.
- Source checkout note: the Stacks TeX used for this reading is available at `/home/ubuntu/c1-stacks-review/perfect.tex` on this machine; the repository's literature directory contains the tag index but not the TeX payload.
