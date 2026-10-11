Files written:
- `dag/nodes/sec-smooth-purity/lem-pur-essential-constant-cofinal-0a1s.json` (item, split; no new nodes)

Attachments: none.

WANTED: none.

What was wrong in the imported item: its statement added cone-map data and equalities that are not part of Categories Lemma 0A1S. I replaced it with the exact source statement. The proof was empty; I supplied the source's formal argument using the existing Hom-colimit and converse-criterion nodes and the existing Mathlib leaf for initial-functor colimits.

What I could not finish: nothing.

## Review by J1
I read Categories Lemma 0A1S (label `lemma-initial-essentially-constant`) and its proof, which explicitly reduces to the pro Hom-colimit characterization, the initial/cofinal colimit lemma, and the fact that opposite categories reverse initial/cofinal functors. I also read the statements of `lem-pc-essentially-constant-pro-hom-colimit`, `lem-weil-pbc-initial-functor-cofiltered-criterion`, and `lem-pur-essential-constant-pro-criterion-05py`; each says exactly the map or implication used in the corresponding step. Step 1 composes the Hom-colimit bijection for `M` with the initial restriction colimit isomorphism. Step 2 reverses that same composite for `M ∘ H`, and Step 3 applies the converse criterion to obtain essential constancy of `M`. The cofiltered hypotheses are present in the item and in the colimit node, and the category and diagram orientations are checked against the opposite-index colimits. I tested the statement on an identity initial functor and on a constant diagram, where both sides have the same value immediately. I searched LeanSearch twice (both unavailable), LeanFinder, Loogle twice, and Mathlib grep twice; only generic initiality/eventual-constancy APIs appeared, so the item is not a Mathlib leaf. No new node or duplicate was introduced.

## Not duplicates
lem-pur-essential-constant-cofinal-0a1s vs `lem-pc-essentially-constant-pro-hom-colimit`: the existing node proves the Hom-colimit formula for an already essentially constant pro-diagram; this item proves invariance of essential constancy under initial restriction.
lem-pur-essential-constant-cofinal-0a1s vs `lem-pur-essential-constant-pro-criterion-05py`: the existing node is only the converse Hom-colimit criterion for one diagram; this item compares two diagrams along an initial functor.

## Second reading by J1

- Item statement: checked against Categories Lemma Tag 0A1S (`lemma-initial-essentially-constant`) in `/home/ubuntu/c1-stacks-review/categories.tex`; the source has exactly a functor of cofiltered index categories, an initiality hypothesis, and the essential-constancy equivalence. Removed the worker's extra claim that the two values agree.
- Step 1: checked against `lem-pc-essentially-constant-pro-hom-colimit` and `lem-weil-pbc-initial-functor-cofiltered-criterion`; their stated Hom-colimit bijection and opposite-index colimit isomorphism supply the two maps used. No elementary claim is asserted.
- Step 2: checked against the same two node statements, with the colimit isomorphism inverted and the Hom-colimit bijection for the restricted diagram; the resulting map has the direction required by the converse criterion.
- Step 3: checked against `lem-pur-essential-constant-pro-criterion-05py`; its hypotheses and conclusion give essential constancy of `M` with the chosen value.
- New nodes: none; therefore B1-B7, duplicate checks, and Mathlib-leaf checks are vacuous. Existing cited nodes were searched in `dag/nodes/` and read in full.
- Small cases: identity initial functor and constant diagrams satisfy the equivalence directly; empty/cofiltered edge cases remain covered by the source hypothesis that both index categories are cofiltered.
- Changes: corrected `created.item` to this item for delivery ownership, and restored the exact source statement by deleting the unsupported value-agreement conclusion.
