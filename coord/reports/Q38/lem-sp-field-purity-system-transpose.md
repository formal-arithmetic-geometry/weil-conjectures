# Worker report

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-field-purity-system-transpose.json: statement, split in five steps; Mathlib searches found no match.
- citations.json: verbatim statement extracts for all fourteen step/node citations.
- No new nodes and no Mathlib leaves.

## Attachments

None. Searched the item tag and purity/coefficient/transpose terminology throughout lean/WeilConjectures, and read EtaleCohomology/Purity/Smooth/Reduction.lean, especially map_smoothPurityIso_hom_comp (lines 92 onward). That finite etale statement assumes the tensor-map compatibility hφ that this item proves and does not concern ordinary derived coefficient systems. It cannot attach this item.

## WANTED

None. The proof is explicitly agent-written: the existing blueprint provides the route, and the existing DAG nodes provide the projection and adjunction statements used.

## Audit and corrections

The item was unsplit with no proof. Its statement is retained verbatim. No repair note exists. The blueprint source read was main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md, paragraph (2), together with the chapter and unit records. This item realizes its tensor-transpose and purity assertions; it is not the unit key node, so no unit realization record changes.

The import's phrase 'same transposition arguments' is replaced by the actual calculation of both transposes. The distinction between conservativity and faithfulness of evaluation is essential: no equality is inferred from equal evaluated morphisms. I reused lem-sp-field-projection-system-square and lem-sp-field-exceptional-system-comparison rather than making new copies. The projection-square node has precisely the same R/ell^n and S/ell^n towers, source comparisons and coefficient mate as this item. Existing lem-sp-tensor-counit-exchange-calculus was also inspected; the proof below writes out its short calculation instead of creating another abstract lemma or moving the item's entire argument into one lemma.

## Searches and duplicates

Searched all dag/nodes for projection/coefficient/scalar and counit/transpose assertions and searched the whole blueprint with blueprint_refs.py for 'projection', 'tensor-map purity transpose', 'counit transpose' and 'coefficient extension'. The nearest blueprint ancestor is det-sp-field-extension-towers. No blueprint statement states this whole-system assertion separately. The broader imported field-extension node includes it as part of a much larger theorem and is an ancestor, not a usable dependency.

Mathlib searches for the item were actually run through msearch.py and logged in searches.jsonl: two distinct LeanFinder phrasings, Loogle, LeanSearch, and grep. Read the returned types: ModuleCat scalar counits are underived module formulas; the second semantic search returned module-sheaf presentations and pullback-free formulas. Smooth algebra base change and dualizing comments do not state this assertion. Existing search records inherited from Q62 were retained. There are no new nodes to compare for duplicate tags.

## Not duplicates

No new nodes.

## Review by Q38

I read the item, its blueprint source paragraph (2), the unit's finite-free/tower route, and the statements of all nine cited nodes. I also read the proper exchange/projection square in Stacks sites-cohomology.tex, Tag 0E48 (remark-compatible-with-diagram), as background for the existing projection-square node. The proof does not invoke an unrecorded Stacks theorem: the system projection square is cited by its own existing node. No SGA source is used.

Step 1 checks domains, rather than assuming arbitrary system inputs are allowed. lem-sp-field-scalar-normalized-systems explicitly preserves the normalized subcategory and uniform Tor and cohomological bounds. det-sp-tower-gamma states its tensor-transpose construction on that constructible domain and preservation by both adjoints. lem-coef-semilinear-derived-sections supplies actual tensor, scalar and pullback maps on systems. det-sp-tower-shriek-levels(2a) requires BOTH inputs finite Tor and etale-origin; the item's three supplied pairs are exactly the pairs whose projection maps are inverted. I checked that the third pair is on Y and X respectively and involves C_X omega_A, not omega_B substituted prematurely.

Step 2 uses the literal equation of lem-sp-field-projection-system-square at W=omega_A and inverts the appropriate projection arrows. Its b is the same proper-mate/open-tensor comparison. The displayed counit equation of lem-sp-field-exceptional-system-comparison, with K=J_A and C_Y J_A identified with J_B, gives exactly the second equation. Neither node is cited for mere finite-level compatibility.

Step 3 expands both transposes in the Hom bijection stated by det-sp-tower-gluing. The exceptional-comparison statement supplies epsilon_B P_B c=C_Y epsilon_A b^{-1}; naturality of b moves C_X tau_A across its inverse. Substituting tau_A's defining transpose and step 2 yields the common expression. Naturality in the second projection input moves c_J across the inverse B-projection. Both maps therefore have the same counit transpose. This step is elementary relative to those cited equations: it is substitution, naturality and injectivity of a specified bijection, with each substitution displayed. It is less than 2000 characters and hides no comparison theorem.

Step 4 checks a clause easy to overlook: tau at the coefficient unit is the identity. def-exchange-projection supplies the proper counit-adjunct word, and lem-coef-semilinear-derived-sections supplies that same construction on systems. At the tensor unit, the proper triangle identity reduces it to identity. lem-sf-open-tensor-normalization expressly extends its unit-adjunct characterization to arbitrary strict coefficient systems, so the open factor reduces to identity too. The counit is the transpose of the identity by det-sp-tower-gluing. This is the only generic off-unit proof tool; its precise use is declared in split_report.tool_uses. It handles an open adjunction normalization and does not alter the unit's proof route.

Step 5 uses det-sp-tower-gamma(2), whose literal formula is the tensor transpose composed with the diagonal orientation, and whose statement identifies finite evaluations with the specified smooth purity map. Precomposing step 3 with 1 tensor a_A gives the bracket c_J C_X a_A; the hypothesis replaces it by a_B. This proves the conditional purity assertion and preserves the actual source comparison.

Checked B1–B10: no new nodes, no self-containedness or orphan-proof issues; the original complete statement and metadata are retained; new search records describe only queries actually run. Checked C1–C8: all non-elementary input facts have named existing statements, every citation quote is a verbatim substring, dependencies do not use the ancestor theorem or the orientation-comparison conclusion, and only the generic open normalization needs an off-unit tool declaration. Checked D1–D5: the proof carries the counit argument rather than applying a replacement node that restates the item. Checked E1–E7: both coefficient rings use ell-power quotients (ramification is allowed); all three inverses have the required witnesses; tensor symmetry and unit constraints are included; no equality detection by evaluation is used. Tested identity coefficient extension, f=id and d=0, the zero complex, and empty schemes: the counit calculation reduces to identity/zero equations, with no division, nonempty assumption or chosen basis. No statement correction was necessary.

## Unfinished

None in the stage-1 split. The reused statement-only dependencies remain their own items, as stage 1 requires.
