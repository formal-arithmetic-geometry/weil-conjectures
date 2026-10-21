# Worker report

1. Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-spectral-clopen-component-homeomorphism.json` (statement, split, no Mathlib match); `citations.json` (five exact statement quotations); this report. Zero new nodes and zero new Mathlib leaves. The existing statement, source and inherited ancestry are unchanged.
2. Attachments: none. Searches for the exact blueprint tag and clopen/component terminology in `lean/WeilConjectures/` found no declaration giving this criterion. `ConnectedComponents.isHomeomorph_lift_of_isPullback` has different, pullback-specific hypotheses. The spectral component file supplies ingredients, not the requested clopen-preimage theorem.
3. WANTED: none.
4. The original item had no proof. Its claim is correct, including empty spaces. The supplied source correctly labels it an agent consequence rather than a quoted Stacks theorem. Existing searches are retained; additional searches, including a second semantic phrasing for compact Hausdorff totally disconnected spaces, are recorded exactly from `searches.jsonl`. The broader Topology grep found discrete quotient partitions, locally constant functions and clopen decompositions; their inspected statements do not give this criterion. LeanSearch's component-map construction and Loogle's partition equivalences likewise cover only ingredients. No declaration proves the whole item in one-line specialization.
5. Nothing mathematical remains unfinished. Delivery validation is recorded below.

## Sources and route

I read the chapter record, unit record, the current main-20261015 unit text, and the parent `lem-sfb-normal-generic-continuous-sections`, particularly its step 4. The item serves the passage from a generic clopen bijection to the normalized homeomorphism of component quotients. It does not replace the coefficient or normality arguments above it. The inherited `blueprint.from.node` is null; `tools/blueprint_refs.py ancestor` explicitly returns None, so I preserved that field and its via list. The inherited named detailed-proof file was not found in the current blueprint snapshot; the unit and live parent locate the obligation. Searches across all blueprint nodes for `clopen`, `connected component`, and `component homeomorphism`, and a scan of current blueprint text for a clopen bijection, found no duplicate of this criterion.

I read `literature/stacks-project/topology.tex`: Tag 0906 (`lemma-spectral-pi0`), Tag 005F (`lemma-connected-component-intersection`), Tag 0900 (`lemma-pi0-profinite`, especially clopen saturation), and Tag 08ZZ (`lemma-profinite-refine-open-covering`). The item's argument is an agent deduction from these sources, not a claimed verbatim source proof. The existing node `lem-pe-spectral-components-profinite` gives exactly the compact Hausdorff totally disconnected conclusion needed. The existing Mathlib leaf `lem-weil-pbc-profinite-clopen-basis` states the pointwise basis property, and I checked pinned Mathlib `Topology/Separation/Profinite.lean` lines 43–79, including `isTopologicalBasis_isClopen` at line 66 and the pointwise version at line 76.

The spectral-component node is a generic off-unit tool and is declared in `split_report.tool_uses`. It does not change the unit route. The clopen-basis node is already a Mathlib leaf.

## Not duplicates

No new nodes. I reused the existing spectral-component and profinite-clopen-basis nodes rather than introducing copies. The quasi-compact component intersection node is not needed as a direct dependency because the statement of the spectral-component node already supplies the requisite topology on the quotients.

## Review by O2

I checked sections B–E of delivery-errors against the actual item, both cited node statements, and the Stacks passages listed above. There is no new statement-only node to audit, no relocated clause of the item, no definition copied from Mathlib, and no unsearched lemma. The six steps give the argument rather than citing a new version of the same assertion. Every step is below 2000 characters.

Step 1 constructs the map from connectedness directly: a separation of an image pulls back, so a component maps inside a component. Its continuity and normalization follow from the quotient topology, and uniqueness follows from quotient surjectivity. This uses definitions only, not an unstated general functoriality lemma.

Step 2 uses the statement of `lem-pe-spectral-components-profinite` twice, with precisely the spectral hypotheses present for T and S. It then applies the statement of `lem-weil-pbc-profinite-clopen-basis` to the two compact Hausdorff totally disconnected quotients. These are the exact conclusions/hypotheses in the quoted node statements; no spectral assumption on f beyond continuity is introduced. This is the sole non-elementary reduction step.

Step 3 proves clopen saturation and the quotient clopen bijection in full. A connected component meeting both sides of a clopen partition would be disconnected; quotient openness on both sides then proves descent. The equation from step 1 gives the actual inverse-image square, so the hypothesis on f transfers to the actual map h, with no unspecified identification. This argument applies to arbitrary component quotients and is a few lines from their definitions, so it is kept as an elementary step rather than made into a node.

Step 4 cites only the pointwise clopen-basis statement, applied to the open complement of a singleton in Hausdorff P. Surjectivity on clopens produces a separating inverse image and hence injectivity on points. Step 5 uses the same cited basis statement in Q, and the compactness established in step 2. A finite union of clopen neighbourhoods excludes a proposed missing point while having full inverse image; injectivity on clopens contradicts this. The finite-subcover argument is written out; it does not hide a compact-image-closed theorem or a Stone-duality theorem.

Step 6 again uses exactly the clopen-basis statement on P. Bijectivity on points identifies the image of each inverse-image clopen with the original clopen; unions prove openness and therefore continuity of the inverse. It does not invoke an uncited compact-to-Hausdorff homeomorphism theorem. Every citation has a verbatim statement quotation in citations.json, checked as a literal substring.

I tested the empty domain/codomain cases: an empty P uses an empty finite subcover in step 5, forcing Q empty; an empty Q admits a map h only when P is empty. The empty T and S then give the unique empty homeomorphism. I also checked connected nonempty spectral spaces (both quotients are singletons), finite discrete spaces (the condition forces a bijection), and a singleton mapping to one point in a two-point discrete space (the clopen inverse-image hypothesis fails). No false edge case or missing hypothesis was found. No statement correction or STATEMENT-DISPUTED marker was needed.
