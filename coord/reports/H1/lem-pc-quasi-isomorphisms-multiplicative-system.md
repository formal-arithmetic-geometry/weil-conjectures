Files written:

- `dag/nodes/sec-picard-framework/lem-pc-quasi-isomorphisms-multiplicative-system.json`: Mathlib leaf split, no new nodes.
- `citations.json`: empty because the Mathlib leaf has no proof steps.

Attachments: none. A search of the project source for the item id, its blueprint tag, and quasi-isomorphism multiplicative-system terminology found no project declaration stating this item. The existing Mathlib leaf is therefore retained.

WANTED: none.

The item was already present as a reviewer-added leaf, but lacked the stage-1 `split_report`. I verified that the statement has the required abelian-category and derived-category notions as dependencies and that the Mathlib match covers both calculus directions and the localization clause. No child node is appropriate: the result is supplied directly by Mathlib.

## Review by H1

I read the item JSON, its source citation (Stacks Derived Categories, Lemma 05RT), and the Mathlib sources `Mathlib/Algebra/Homology/DerivedCategory/Fractions.lean` and `Basic.lean`. `Fractions.lean` lines 34 and 38 provide `HasLeftCalculusOfFractions` and `HasRightCalculusOfFractions` for `HomotopyCategory.quasiIso C (ComplexShape.up ℤ)` under `[Category C] [Abelian C] [HasDerivedCategory C]`. `Basic.lean` defines `DerivedCategory C` as the localization of cochain complexes at quasi-isomorphisms and supplies the localization functor from the homotopy category. These declarations match the three clauses of the item; the existing `def-weil-abstract-derived-category` dependency supplies the project's localization terminology.

There are no proof steps, so `citations.json` is correctly empty and no citation quote is required. I checked the whole DAG for the item id, Stacks tag 05RT, and the key phrase before retaining the existing leaf. I also checked the source checkout for a sorry-free project declaration or blueprint tag; none exists. The Mathlib search record already in the node identifies the exact file and line for both calculus instances and the localization definition. The statement remains unchanged, and no new hypotheses or conclusions were introduced.

## Second reading by H1

- Item statement: checked against Stacks `derived.tex`, Lemma 05RT (`lemma-acyclic`), including the abelian-category hypothesis, quasi-isomorphism class, saturated multiplicative system, and localization; verdict: agrees, with Mathlib's left/right calculus instances supplying the explicit calculus formulation.
- New node: the sole Mathlib leaf has no child nodes; checked B1-B7 (statement-only form, self-contained definitions via cited nodes, TeX, tag/label source, blueprint metadata, and searches); verdict: compliant after correcting ownership and search metadata.
- Mathlib match: checked `Fractions.lean` lines 34 and 38 for left/right calculus and the `DerivedCategory` localization declarations in `Basic.lean`; verdict: exact under the category, abelian, and derived-category assumptions.
- DAG/duplicate check: searched for the item id, Tag 05RT, calculus names, and blueprint ancestry; verdict: no duplicate supporting node or sorry-free project declaration requiring a different split.
- Edge cases: the zero abelian category and a field as an abelian category give the expected trivial and ordinary derived localizations; zero and identity quasi-isomorphisms satisfy the multiplicative-system clauses.
- Changes made: corrected `created.item` to this delivered item; replaced stale unlogged Mathlib search entries with the actual grep, LeanFinder, and unavailable Loogle results in `searches.jsonl`; added this second-reading audit.
