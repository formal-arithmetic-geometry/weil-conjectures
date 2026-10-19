# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/thm-fin-projective-smooth-curve-finiteness.json`: split item; no new nodes.
- `citations.json`: verbatim statement quotes for every proof citation.

## Attachments

None. No sorry-free declaration in slopmaster2 states this item exactly.

## WANTED

None.

## Review by NN

I read the item source `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/thm-fin-projective-smooth-curve-finiteness.md`, the chapter and unit records, and the statements of all four cited nodes. The statement is unchanged. Step 1 uses the existing projective-implies-proper statement, including its projective hypothesis. Step 2 uses the finite-coefficient geometric-fibre base-change statement, whose hypotheses are properness, a finite coefficient ring, and a finite module sheaf; I checked that `F = F_ell` and that step 1 supplies properness. Step 3 uses the curve Betti-cardinality statement and checked its Noetherian, smooth, projective, pure-dimension-one, and invertible-prime hypotheses against the item. Step 4 uses the exact stalk-constructibility criterion: finite geometric stalks and constructibility of every cardinality level set. I made the level-set identification explicit through the stalk isomorphisms rather than treating finite stalks alone as sufficient. Every quote in `citations.json` is copied verbatim from the cited node statement. I searched the whole DAG and blueprint for duplicate facts before deciding that no child node was needed.

Mathlib searches for the item were run with `msearch.py`: LeanFinder (no relevant match), Loogle (no hits), grep over `Mathlib/AlgebraicGeometry` (only Chevalley constructible-image declarations, not etale cohomology), and LeanSearch (service unavailable, recorded as unavailable). The source reads and the small edge cases `r=0,1,2` and `r>2` are covered by the cited Betti formula.


## Second reading by NN

- Item statement: compared every hypothesis and conclusion with `sec-smooth-purity/sk-prop-sf-cbc/thm-fin-projective-smooth-curve-finiteness.md`, order 1611; unchanged and faithful. Read the chapter and unit records; all four steps realize the node's proof paragraph without replacing its route.
- Step 1: opened `lem-pc-projective-proper` and its blueprint source, order 757; its first sentence supplies properness directly, with no smoothness or field restriction. Also read Stacks `morphisms.tex`, label `lemma-locally-projective-proper`, which states the stronger locally-projective result. The coefficient ring and rank-one constant module are finite by definition; pass.
- Step 2: opened `cor-weil-pbc-geometric-fiber-finite` and its blueprint source, order 1322; its sheaf clause supplies exactly the claimed stalk isomorphism for every nonnegative degree. Properness comes from step 1 and the coefficient ring/module are finite. Restriction of the constant coefficient sheaf is constant; pass after repairing the malformed geometric-point TeX.
- Step 3: opened `lem-fin-projective-curve-betti-cardinalities` and its blueprint source, order 1610; Noetherian base, smoothness, projectivity, pure fibre dimension one, and the invertible prime are precisely the item's hypotheses. The finite cardinalities and constructible cardinality functions are both in the statement, without using its proof; pass.
- Step 4: opened `fin4-lem-stalk-constructibility-criterion` and its blueprint source, order 1608; checked its Noetherian-base and abelian-sheaf hypotheses, finite stalks from steps 2–3, and each positive cardinality locus via the same stalk isomorphisms. Added the elementary explanation that an additive trivialization of an F_ell-module is F_ell-linear (scalars act by repeated addition), so the criterion gives the coefficient-module constructibility meant by the item; pass.
- New nodes: none; no duplicate, elementary child, Mathlib-leaf claim, or moved conclusion to review. All six citation quotes were checked verbatim against the four existing node statements. No proof uses a cited node's internal construction.
- Edge cases: an empty base is vacuous; an empty fibre has zero cohomology, hence singleton underlying groups in every degree, matching the formula with c=g=0. Over an algebraically closed field, a connected genus-zero curve has cardinalities ell, 1, ell in degrees 0, 1, 2; a disconnected fibre uses the stated c and total g. Degrees above two give cardinality one, and all groups are nonempty so n=0 never needs the criterion. No surjectivity or connected-fibre hypothesis was introduced.
- Lean attachment check: searched the read-only slopmaster2 source by item id and curve/constructibility vocabulary; no matching declaration was found. Independently ran a Mathlib grep through msearch for `RΓ|etaleCohomology|ConstructibleSheaf|higherDirectImage`; the actual result is retained in searches.jsonl, with no matching leaf asserted.

Changes: repaired backspace characters produced by JSON `\bar` escapes and put proof formulas in TeX delimiters; made the constant-sheaf restriction, nonnegative degree, positive cardinality loci, abelian-sheaf typing, and coefficient-module conclusion explicit. Retained the worker proposal in `split_report.tool_uses`: `tools/review_split.py` lines 99–100 explicitly permit this proposal (human decision, 2026-10-10 evening); accepted node-level `tool_uses` still belongs to the maintainer. The first dry run showed that removing this proposal incorrectly prevents preflight; restored it without writing the maintainer field. `cor-weil-pbc-geometric-fiber-finite` is a generic proper-base-change tool from another unit, necessary for the geometric-stalk identification; `lem-pc-projective-proper` is likewise the generic projective-implies-proper tool from the Picard unit. The curve unit supplies no substitute for either. The original worker review is preserved. No statement change or new node was necessary.
