Files written:

- `lem-sc-finite-length-global-submodule.json` (statement, split; no Mathlib match)
- `lem-sc-finite-maximals-over-element.json` (statement-only support node; no Mathlib match)
- `citations.json`

Attachments: none.

WANTED: literature/stacks-project/algebra.tex, Lemma 10.30.9 (Tag 00PF), because the checked-out literature bundle contains only the citation index; the proof was reconstructed from the cited lemma and its local 00PE analogue.

## Not duplicates

`lem-sc-finite-maximals-over-element` vs `lem-sc-finite-length-global-submodule`: the support node only asserts finiteness of maximal ideals containing `x`; the item asserts finite module length for `M/xM`.

`lem-sc-finite-maximals-over-element` vs `lem-weil-pbc-dim-one-submodule-quotient-finite-length`: the existing 00PE node is local and bounds the length of a quotient of a submodule of `K^r`; the new node is global and only supplies the finite set of maximal ideals over `x`.

## Review by F1

I read the item source citation (Stacks Algebra 00PF) as recorded in the node and compared every hypothesis with the statement: `R` is a Noetherian one-dimensional domain, `K` is its fraction field, `M` is an arbitrary submodule of `K^r`, and `x` is nonzero. I also read the existing 00PE node before using it; its statement is explicitly local, applies to arbitrary submodules without finite-generation, and gives finite length after quotienting by a nonzero element, so it supplies exactly the localization step and not the global conclusion. The new support statement is strictly smaller and has the same Noetherian/domain/dimension hypotheses.

Step 1 is the unit reduction and uses only the length definition. Step 2 uses the new finite-maximal-ideal statement and the 00PE local statement; localization preserves the fraction field and the dimension-one local-domain hypotheses. Step 3 spells out why a nonzero subquotient of `M/xM` is detected at a maximal ideal containing `x`, so no support outside the finite set can contribute. Step 4 uses the 00PE finite local bounds and the chain characterization in the module-length definition: each strict jump is detected at one of finitely many localizations, and each localization admits only finitely many jumps. The quotes in `citations.json` are copied verbatim from the cited statements.

I checked the edge cases `r=0`, `M=0`, `x` a unit, and a one-point quotient (for example `R=Z`, `x=2`); all reduce to the stated chain argument. I searched the whole DAG for the 00PE tag and for finite-length/submodule keywords. The local node is a genuine local theorem, so it is cited rather than duplicated. Mathlib searches for the item and the new support node were run with LeanFinder, Loogle, and Mathlib grep; no exact global theorem was found.

What was wrong in the imported item was not its statement but its absent proof split: the global localization argument and the finite set of maximal ideals were implicit. I made the localization and strict-chain counting explicit and left the supporting maximal-ideal fact statement-only as required for a one-level split.

## Second reading by F1

- Item statement: checked against Stacks Algebra Tag 00PF (`lemma-finite-length-global`, algebra.tex lines 29266-29273); hypotheses and conclusion agree, including arbitrary submodules and nonzero `x`.
- Node `lem-sc-finite-maximals-over-element`: checked against Tag 00PF lines 29275-29279 and the zero/unit cases; it is the strictly smaller finite-support assertion and has no exact Mathlib match in the recorded searches.
- Step 1: checked against the unit reduction in Tag 00PF and the module-length definition; elementary and correct.
- Step 2: checked against the localization paragraph of Tag 00PF and the full statement of the local 00PE node; the local hypotheses and fraction-field identification are the facts used.
- Step 3: checked against the support argument implicit in Tag 00PF's product decomposition; annihilators and localization detect every nonzero subquotient at a maximal ideal containing `x`.
- Step 4: checked against the final finite-filtration argument in Tag 00PF; the repaired wording partitions a strict chain by detecting maximal ideals and bounds each part by the corresponding local length.
- Citation quotes: checked verbatim against the cited node statements; no tag is used as an uncited non-elementary dependency.

Changes made: corrected both source places to Tag 00PF with exact algebra.tex lines; repaired step 4's vague “injection into a disjoint union” into an explicit partition-and-sum bound; retained the support node because it is not a duplicate or Mathlib theorem; no statement changes.
