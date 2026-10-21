## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-constructible-rational-hom-comparison.json`: statement item, now split in four steps; no Mathlib match. Statement unchanged.
- No new nodes; no Mathlib leaves created.
- `citations.json`: verbatim statements for all eight step/node citations.
- `searches.jsonl`: actual search-command records, retained without alteration.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag and for constructible compactness and rational Hom terminology. The tag is absent. `CategoryTheory/DerivedCategory/ExtendScalarsLocalization.lean` proves the special ordinary-module calculation on the free rank-one module, not the pro-etale constructible assertion for all K and L. Existing compactness modules concern localizing subcategories or explicit abstract hypotheses, and do not supply every clause of this item. No attachment claimed.

## WANTED

None. Read the local Bhatt–Scholze PDF, pp. 61–62, Lemma 6.8.12 and Proposition 6.8.14(2), including the full-faithfulness proof. No SGA source used.

## Corrections and reuse

No statement, definition, unit route, or target correction. The imported item was a statement-only node. The DAG already contains `lem-weil-pbc-integral-constructible-hom-sums`, which states its first assertion exactly, in the identical coefficient category, and whose proof cites the global-derived-Hom continuity node named in the item. Reused that node rather than creating a duplicate passage-to-cohomology lemma. Reused the existing abstract scalar-localization theorem for the second assertion.

Searched the whole DAG for bounded-below compactness, coproduct Hom, and cohomology/direct sums. Read the actual statements of all six distinct cited nodes. Ran `tools/blueprint_refs.py ancestor` and searches for `derived Hom comparison` and `rational.*Hom|Hom.*rational|6.8.14`; no blueprint node states the entire item. The nearest ancestor is `lem-per-smooth-pullback-t-exact`; read its current main-20261015 text and the parent realization node. The existing blueprint ancestry/place is retained. This item supplies the parent's actual-Hom/full-faithfulness step, rather than the unit's perverse/Fourier theorem itself, so no unit realized fields change.

The three generic off-unit tools are declared in `split_report.tool_uses`: the integral Hom-sums theorem, integral stratified-perfect characterization, and scalar-localization comparison. They provide the exact coefficient-category interfaces this realization argument needs; no node of the perverse unit supplies them.

## Unfinished work

None for this one-level split. Existing dependency nodes retain their own proof obligations. This delivery claims no completed Lean proof.

## Review by Q143

I read Bhatt–Scholze Lemma 6.8.12, which states global derived Hom continuity on a common bounded-below range (its nonnegative formulation is shifted in the existing DAG node), and Proposition 6.8.14(2), whose proof obtains full faithfulness from that lemma. The proof below expands exactly this implication using already existing nodes; it does not assert compactness for arbitrary unbounded families or essential surjectivity.

Step 1 uses the realization-functor statement for the canonical identification of the completed coefficient sheaf with continuous A-valued functions. The Hom-sums node explicitly uses this same identification, the same completed integral category with compatible witnesses, small countable families with a common lower bound, every integer q, and the shifted-coprojection map. Its statement therefore proves exactly the first assertion. I also read its four-step proof: it uses the named global-derived-Hom compactness theorem, derived-module cohomology of sums, and the internal-Hom sections model; none of those facts is silently re-proved here.

Step 2 uses the integral characterization's equivalence (i) with (iii), where (iii) explicitly says bounded, and its final sentence giving closure under shifts. No assumption that bounded reductions alone imply boundedness has been substituted. The noetherian, finite-dimensional and invertibility assumptions match, and the compatible etale-origin witnesses in (i) match the item.

Step 3 applies the scalar-localization theorem with the explicitly specified small site, A, t=varpi, R=B_X and R_t=E_X. Step 1 supplies its whole Hom-continuity hypothesis and Step 2 supplies bounded-below L. The realization-functor statement says the scalar-localization functor is exact on sheaves and induced on the actual derived module categories, and gives the same F_X. The scalar theorem explicitly gives the fraction formula, naturality and shift compatibility. Thus neither a merely abstract Hom equivalence nor an equivalence only in a constructible target is being used.

Step 4 is the short formal calculation of precomposition, postcomposition, shifts, identities and composition on fractions, followed by the definition of full faithfulness. I checked the full-subcategory clause of the completed integral definition and the same-objects/localized-Hom clauses of the raw rational category. These identify its q=0 comparison with the previously specified J_X on every object pair. Every morphism is a fraction; the composition identity includes both denominator exponents. The step uses no Karoubi completion or essential-surjectivity claim.

For B–E, no new statement-only nodes, duplicates or hidden clauses were created. All cited statements were opened, and every use has a verbatim quote in citations.json. The new proof has no step over 2000 characters. The empty family gives zero on both sides; K=0 or L=0 likewise gives zero Hom; negative q is allowed by the Hom-sums and scalar-localization statements; integral varpi-torsion objects cause no problem because the theorem localizes the actual Hom modules and does not assume torsion freeness. I checked that every dependency is an existing node rather than a new restatement, and that the elementary last step only performs fraction calculations and unpacks full faithfulness.

I ran the required searches in two natural-language phrasings, Loogle, LeanSearch and two source grep queries. The results concerned exact derived-functor construction, ordinary Ext, module completion, or localization at quasi-isomorphisms, and did not state this pro-etale constructible scalar comparison. Read the relevant existing project rank-one localization calculation and Mathlib ExactFunctor source; these are insufficient for an attachment or Mathlib leaf. Search records in the item preserve the inherited records and add the actual command queries/results of this session.
