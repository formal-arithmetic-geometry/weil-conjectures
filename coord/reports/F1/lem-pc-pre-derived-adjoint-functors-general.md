1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-pre-derived-adjoint-functors-general.json` (split item)
- `lem-pc-essentially-constant-ind-hom-colimit` (statement-only, no Mathlib match)
- `lem-pc-essentially-constant-pro-hom-colimit` (statement-only, no Mathlib match)
- `lem-pc-right-localization-hom-colimit` (statement-only, no Mathlib match)
- `lem-pc-left-localization-hom-colimit` (statement-only, no Mathlib match)
- `lem-pc-colimit-fubini` (Mathlib leaf: `CategoryTheory.Limits.colimitFlipCompColimIsoColimitCompColim`)

2. Attachments: none.

3. WANTED: none; the Stacks source checkout used for review was `/home/ubuntu/c1-stacks-review/derived.tex`, since the project literature directory stores citation metadata rather than the TeX source.

4. The item was the general multiplicative-system form of Derived Categories Lemma 0FND, specialized in its statement to complexes and derived categories. I searched the whole DAG and source checkout for the item tag and for each child’s localization/essential-constancy formulation; no duplicate or sorry-free project declaration states the item. The source proof was read at lines 9515--9516. Step 1 uses the ind-system essential-constancy Hom-colimit statement; step 2 uses the right-localization Hom-colimit statement; step 3 uses the Fubini colimit isomorphism; step 4 is the one-line underived adjunction bijection and is marked elementary; step 5 uses the left-localization Hom-colimit statement; step 6 uses the pro-system essential-constancy Hom-colimit statement. Each citation quote is copied verbatim from the cited node statement. The RF and LG hypotheses are used exactly at steps 1 and 6, and the multiplicative-system localization hypotheses at steps 2 and 5. I checked the degenerate one-object identity localization and identity adjunction cases: every colimit is constant and the displayed bijection reduces to the ordinary adjunction.

## Review by F1

I read the complete Stacks proof of Lemma 0FND and the abelian specialization 0DVC in `/home/ubuntu/c1-stacks-review/derived.tex`, including the six displayed equalities and the cited Categories localization/essential-constancy results. The item statement matches the source’s hypotheses and conclusion: two abelian categories, an adjoint pair, pointwise essential constancy of the ind/pro systems, and a bifunctorial Hom isomorphism. Each new node states only one prerequisite equality from that calculation, with all category objects and localization data introduced in the statement. The Mathlib child was checked against the Fubini declaration in `Mathlib/CategoryTheory/Limits/Fubini.lean`; the other four searches found no exact Mathlib theorem, while LeanSearch was unavailable and is recorded as such. I corrected the initial split to keep the underived adjunction as an elementary step rather than creating a node that merely restated a clause of the item. The citation file records one verbatim statement quote for every non-elementary use.

5. Nothing remains unfinished in the split; the required dry run is the next check.

## Not duplicates

lem-pc-colimit-fubini vs lem-pc-pre-derived-adjoint-functors-general: the child states the general categorical Fubini isomorphism, while the item is the derived pre-adjunction conclusion.
lem-pc-colimit-fubini vs lem-weil-pbc-limit-fibre-products: the child interchanges arbitrary iterated colimits, while the existing node compares scheme fibre products via limits.
lem-pc-colimit-fubini vs lem-weil-pbc-termwise-adjunction-homotopy: the child is a colimit interchange, while the existing node is a termwise homotopy-category adjunction.
lem-pc-essentially-constant-ind-hom-colimit vs lem-pc-pre-derived-adjoint-functors-general: the child is only the ind Hom-colimit equality, while the item includes both ind/pro systems and adjunction.
lem-pc-essentially-constant-ind-hom-colimit vs lem-weil-pbc-derived-square-iso-commshift: the child concerns Hom from a fixed object into an essentially constant ind-diagram, while the existing node concerns derived exchange compatibility with shifts.
lem-pc-essentially-constant-ind-hom-colimit vs lem-weil-pbc-localization-universal-property: the child computes Hom into an ind-value, while the existing node states the universal property of a localization functor.
lem-pc-essentially-constant-ind-hom-colimit vs lem-weil-pbc-termwise-adjunction-homotopy: the child is an ind-colimit Hom formula, while the existing node gives a termwise adjunction on homotopy categories.
lem-pc-essentially-constant-pro-hom-colimit vs lem-pc-pre-derived-adjoint-functors-general: the child is only the pro Hom-colimit equality, while the item includes both ind/pro systems and adjunction.
lem-pc-essentially-constant-pro-hom-colimit vs lem-weil-pbc-termwise-adjunction-homotopy: the child is a pro-colimit Hom formula, while the existing node gives a termwise adjunction on homotopy categories.
lem-pc-left-localization-hom-colimit vs lem-pc-pre-derived-adjoint-functors-general: the child is only the left-localization Hom calculation, while the item is the full pre-derived adjunction.
lem-pc-left-localization-hom-colimit vs lem-weil-pbc-derived-square-iso-commshift: the child computes localization morphisms, while the existing node concerns shift compatibility of a derived adjunction.
lem-pc-left-localization-hom-colimit vs lem-weil-pbc-localization-universal-property: the child gives the Hom-set colimit formula under a multiplicative system, while the existing node gives the universal property.
lem-pc-left-localization-hom-colimit vs lem-weil-pbc-termwise-adjunction-homotopy: the child is a localization Hom formula, while the existing node is a homotopy-category adjunction.
lem-pc-right-localization-hom-colimit vs lem-pc-pre-derived-adjoint-functors-general: the child is only the right-localization Hom calculation, while the item is the full pre-derived adjunction.
lem-pc-right-localization-hom-colimit vs lem-weil-pbc-termwise-adjunction-homotopy: the child is a localization Hom formula, while the existing node is a homotopy-category adjunction.

## Second reading by F1

- Item statement: checked against Stacks Tags 0FND and 0DVC (labels `lemma-pre-derived-adjoint-functors-general` and `lemma-pre-derived-adjoint-functors`), hypothesis by hypothesis; verdict: agrees, including the RF/LG defined-at conditions and functorial Hom isomorphism.
- Step 1: checked against the ind essential-constancy calculation in Tag 0FND and child `lem-pc-essentially-constant-ind-hom-colimit`; verdict: cited statement supplies the displayed colimit bijection.
- Step 2: checked against the right-localization calculation in Tag 0FND and child `lem-pc-right-localization-hom-colimit`; verdict: denominator orientation and Hom arguments agree.
- Step 3: checked against Categories Tag 002M and the Mathlib Fubini declaration; verdict: independent indexing categories justify the interchange.
- Step 4: checked directly from the adjunction definition on the underlying categories and induced complex Hom bijection; verdict: elementary in a few lines.
- Step 5: checked against the left-localization calculation in Tag 0FND and child `lem-pc-left-localization-hom-colimit`; verdict: denominator orientation agrees with the fifth equality.
- Step 6: checked against the pro essential-constancy calculation in Tag 0FND and child `lem-pc-essentially-constant-pro-hom-colimit`; verdict: cited statement supplies the final colimit bijection.
- `lem-pc-essentially-constant-ind-hom-colimit`: checked as a self-contained statement with its filtered category, diagram, value, and Hom map; verdict: valid. Zero and identity diagrams reduce to the identity bijection.
- `lem-pc-essentially-constant-pro-hom-colimit`: checked as the dual self-contained statement; verdict: valid. Zero and identity diagrams reduce to the identity bijection.
- `lem-pc-right-localization-hom-colimit`: checked with the one-object identity multiplicative system and the source's right-fraction orientation; verdict: valid.
- `lem-pc-left-localization-hom-colimit`: checked with the one-object identity multiplicative system and the source's left-fraction orientation; verdict: valid.
- `lem-pc-colimit-fubini`: checked against Mathlib `CategoryTheory.Limits.colimitFlipCompColimIsoColimitCompColim` in `Mathlib/CategoryTheory/Limits/Fubini.lean`; verdict: exact Mathlib leaf.
- Changes: corrected all six source-place records from the worker's incorrect `04VG`/`04VH` references to Tags `0FND`, `0DVC`, `05PY`, `05PZ`, `05Q0`, `05Q4`, and `002M`, with their labels; no mathematical statement or proof step required alteration.
