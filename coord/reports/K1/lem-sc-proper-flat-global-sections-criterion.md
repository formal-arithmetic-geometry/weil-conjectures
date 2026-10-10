1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-proper-flat-global-sections-criterion.json`: split item with two proof steps.
- `dag/nodes/sec-abelian-varieties/lem-sc-perfect-degree-zero-fibre-criterion.json`: statement-only child, no Mathlib leaf.
- `citations.json`.

2. Attachments: none.

3. WANTED: none.

4. The item has no sorry-free Lean declaration. It is Tag 0E62. The existing sibling `lem-sc-proper-flat-global-sections` is not a duplicate: it adds geometric reducedness and connectedness hypotheses and derives the fibre H^0 condition, while this item assumes that condition directly. The only new input is the broader perfect-complex criterion underlying Tag 0E62.

## Not duplicates

lem-sc-perfect-degree-zero-fibre-criterion vs lem-sc-proper-flat-global-sections-criterion: the new node applies to an arbitrary perfect complex on an arbitrary scheme and assumes derived-fibre connectivity; the item specializes to Rf_*O_X for a proper flat finitely presented morphism and concludes a pushforward statement.

## Review by K1

I read the item and sibling nodes, the Stacks Tag 0E62 reference, and the existing perfect pushforward/base-change node `lem-pc-rf-perfect-base-change`. Step 1 uses exactly that node's conclusion for the structure sheaf and the definition of derived direct image to identify the fibre cohomology. Step 2 applies the new criterion to the assumed residue-field H^0 maps and uses its universal clause. The new criterion is strictly more general than the item because it is stated for an arbitrary perfect complex and arbitrary base change, so it is not a restatement. I ran LeanFinder, Loogle, grep, and LeanSearch for the new node; the first three found no matching Mathlib theorem and LeanSearch was unavailable. Small cases checked include the identity morphism and a proper scheme over a field with H^0 equal to the field.

## Second reading by K1

- Item statement: checked against Stacks Tag 0E62, label `lemma-proper-flat-h0`, lines 8047–8064 of `perfect.tex`; proper, flat, finite-presentation, fibre H^0, universal pushforward, and local perfect splitting hypotheses/conclusions agree.
- Step 1: checked against `lem-pc-rf-perfect-base-change` (Tag 0B91) and the structure-sheaf unit; the cited node supplies perfectness and arbitrary base change, while the added nonnegative-amplitude assertion is the degree-zero derived pushforward fact used in Tag 0E62.
- Step 2: checked against the statement of `lem-sc-perfect-degree-zero-fibre-criterion`; the fibre map is now the unit-induced map and the conclusion gives both $f_*\mathcal O_X=\mathcal O_S$ and its base-change form.
- New node `lem-sc-perfect-degree-zero-fibre-criterion`: checked against the proof of Tag 0E62, especially lines 8066–8092; B1 statement-only form, B2 self-contained scheme/complex/morphism hypotheses, B3 definition nodes for perfect complexes, derived category, pullback and Tor amplitude, B4 TeX notation, B5 tag/label source, B6 no Mathlib match, and B7 no tag-only semantic dependence all checked.
- Existing-node search: searched all DAG nodes for the criterion, perfect fibre, Tor-amplitude, and pushforward terms; no duplicate criterion was found. `lem-pc-rf-perfect-base-change` remains the generic tool use.
- Small cases: identity morphism, $S=\operatorname{Spec}(k)$ with $K=k$, and the empty scheme were checked; the hypotheses and conclusion are consistent.

Changes made: corrected the source label from `perfect-lemma-proper-flat-h0` to the actual `.tex` label `lemma-proper-flat-h0`; repaired the new criterion by supplying the missing morphism $u:\mathcal O_S\to K$ and nonnegative Tor-amplitude hypothesis, and added the local splitting that Tag 0E62 actually proves; updated step 1 and step 2 to use those hypotheses; synchronized the citation quote verbatim with the repaired node statement.
