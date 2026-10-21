# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-fix-reduction-open-etale-origin.json`: statement, split into six proof steps using existing nodes; no Mathlib match.
- `citations.json`: 20 verbatim statement excerpts, one for each citation in each proof step.
- `searches.jsonl`: actual NV msearch log. All five inherited item queries were run and their current results/digests recorded; LeanSearch returned different hits from the inherited record, which was updated.

New nodes: 0. Mathlib leaves: 0. The item statement and its statement dependencies are unchanged.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the item id and the notions, including the finite-coefficient derived files. `AlgebraicGeometry.ProEtale.plusEtaleOrigin_mapDerivedCategory_openImmersionLowerShriek` (LowerShriekBaseChange.lean:85) only proves the bounded-below open-extension clause; it does not state finite coefficient change, an [a,b] bound, or all the requested witnesses. The related `nonempty_coefficientTensorModel_of_finiteTor` and `CoefficientTensorModel.origin_of_etale_finiteTor` in lean/Sheaf/Paper/EtaleCompactSupportCoefficientChange.lean are sorried and do not finish this item.

## WANTED

None: the sources used are available as local Stacks TeX and the current blueprint.

## Corrections and issues

No statement dispute. The original item was a statement-only node; its old source attribution to 06YY alone does not prove the origin or boundedness clauses. The split explicitly cites constructible comparison, B-linear coefficient comparison, the sheaf unit, and both exact open extensions. The proof is marked agent-written because it assembles these sources; it is not attributed wholesale to 06YY.

The item's imported unit remains the trace-perfectness unit, although the current main-20261015 ancestor is located in sec-six-functors-basics/sk-def-sfb-coefficient-comparisons. I preserved the unit and chapter as required. This is a lower-level domain calculation, not the unit key node, so no unit realization record is changed. Every off-unit statement used as a general tool is declared in split_report.tool_uses.

During self-review I caught that def-weil-derived-tensor states only the pro-etale tensor construction. I added def-kun-derived-tensor for its ordinary-etale counterpart rather than using the former outside its domain (C4). Also retained the B-linear inverse-image/scalar theorem: an isomorphism of underlying A-objects alone would not supply the specified B-linear witnesses.

## Not duplicates

No new node is introduced. Whole-blueprint searches for "etale origin", "coefficient reduction", "Tor amplitude", and "bounded etale", together with DAG/source reads, found all the component tools already present. No blueprint node states this entire package as an alternative attachment. In particular the existing coefficient-pullback comparison, open scalar normalization, and exact comparison suffice, so no new flat-model or reflection lemma is created.

## Unfinished work

None in the stage-1 split. No Lean was written or compiled; the existing dependency nodes retain their own proof status.

## Review by NV

I read coord/brief-stage1.md, stages/1-dag.md, the three-level rule of SETUP.md, GOAL.md, the worker role, tools/README.md, and both copies of delivery-errors B--E. I read the chapter and unit records and the current ancestor proof (main-20261015 coefficient-comparisons, second proof paragraph and final site-comparison sentence). This split supplies their bounded-domain calculation and leaves the compactification argument above it intact.

For the mathematical sources I opened Stacks sites-cohomology.tex at 06YY (derived-base-change), 0G7E (pullback-K-flat) and 07A4 (pullback-tensor-product); sites-modules.tex at 0E8I (j-shriek-and-tensor); etale-cohomology.tex at 03S5 (describe-jshriek); and proetale.tex at 099T (fully-faithful), 09AF (jshriek-comparison), 09AK and 09AL (constructible and derived comparison). There are no new nodes needing additional sources and no SGA citation.

Step 1 uses the actual clause (ii) of lem-sf-proetale-constructible-origin: it supplies the bounded constructible etale object, not just a sheaf-level equivalence. A is precisely a finite coefficient stage and K satisfies its intrinsic constructibility hypothesis. I did not infer a derived equivalence merely from full faithfulness of schemes or from a definition.

Step 2 uses lem-pur-coefficient-pullback-comparison, whose statement actually constructs the derived scalar/inverse-image isomorphism with flat-term K-flat normalization, in the target coefficient category. The comparison geometric morphism and its constant-ring module lifts come from def-weil-pbc-site-comparison-morphism; exactness is explicitly in prop-weil-pbc-site-comparison-finite-level. Derived scalar extension is the genuine everywhere-defined K-flat functor of lem-pur-derived-change-of-rings. It applies before any boundedness of the reductions is known, so there is no circular bounded-below assumption.

Step 3 uses lem-pc-kflat-resolution for existence, lem-pur-derived-change-of-rings for the B-module computation, and lem-pur-change-of-rings-tensor-comparison for the underlying A-module tensor. The two tensor definition nodes really specify that a K-flat replacement of the first factor suffices. Scalar restriction keeps the abelian sheaf by its definition, so it preserves and reflects vanishing by the same kernel/image quotients. The Tor hypothesis is applied only to K and the degree-zero A-module B; B need not be flat. This gives the actual bound [a,b], not an unspecified boundedness statement.

Step 4 uses lem-weil-pbc-extension-by-zero-exact on the etale site and lem-cbc-proetale-extension-zero on the pro-etale site. Thus the sheaf-level natural isomorphism in lem-cbc-proetale-extension-zero-comparison can be applied termwise and descends to derived categories. It supplies exactly the comparison being used. Boundedness of E_e follows by the displayed cohomology equality; I do not assert that extension by zero along an arbitrary open preserves constructibility.

Step 5 takes only the first paragraph's B-linear isomorphism from lem-fix-open-scalar-tensor-normalization, whose hypotheses are an arbitrary open immersion and finite A,B. It does not require its extra coherence clauses. The composite with step 2 and step 4 is explicitly written. Exact pro-etale extension by zero, already cited, gives the same [a,b] bound. None of these nodes depends on the item, and the scalar/open node has no proof dependencies returning through it.

Step 6 is an elementary kernel/image calculation using the exactness and sheaf unit actually stated by prop-weil-pbc-site-comparison-finite-level. For each individual cohomology sheaf the unit identifies it with the direct image of its zero inverse image. This proves reflection without applying a bounded-below derived comparison theorem to an object not yet known to be bounded below. It never invokes geometric-stalk conservativity on arbitrary pro-etale sheaves. The displayed witness definition requires a D+ etale source; both reductions are now bounded, so that hypothesis is established before using the definition.

I checked the B1--B10 form requirements and C1--C8/D1--D5/E1--E7 against the cited statements. There are no statement-only helpers carrying hidden proofs, no restatements of the item, and no long step (every step is under 1200 characters). The only generic new-looking assertion, reflection of the interval, is written out in three equalities from the unit and exactness, so it is an elementary step rather than a node. All 20 excerpts were checked literally against the current cited node statements.

Small cases: j=id gives the scalar-origin assertion alone; j with empty source and K=0 gives zero witnesses; A=B gives the original comparison with the same Tor bound. For a genuinely nonflat map Z/ell^2 to Z/ell, taking the free A-module in degree zero gives B in degree zero; the argument uses its Tor amplitude, not flatness of B. Taking instead the residue module over Z/ell^2, whose self-Tor is unbounded, violates the finite-Tor hypothesis, so the argument correctly makes no bounded-reduction claim in that case. No quasi-compact, Noetherian, finite-type, or separatedness hypothesis was smuggled into a step.
