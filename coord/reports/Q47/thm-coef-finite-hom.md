# Stage-1 worker report: thm-coef-finite-hom

## Files written

- `dag/nodes/sec-six-functors/thm-coef-finite-hom.json` — repaired item split; statement, Lean record, and the retained route are unchanged.
- `dag/nodes/sec-six-functors/lem-coef-etale-hom-thick-locus.json` — new statement node; Mathlib searches found no match.
- `dag/nodes/sec-six-functors/lem-coef-etale-open-tensor.json` — new statement node; Mathlib searches found no match.
- `dag/nodes/sec-six-functors/lem-coef-etale-locally-closed-shriek.json` — new statement node; Mathlib searches found no match.
- `dag/nodes/sec-six-functors/lem-coef-internal-adjunction-pairing-change.json` — new statement node; Mathlib searches found no match.
- `dag/nodes/sec-six-functors/lem-coef-monoidal-square-hom-transport.json` — new statement node; Mathlib searches found no match.
- `citations.json` — verbatim statement quotations for every item-step citation.
- `report.md` — this report.

## Attachments

None. The source checkout has no sorry-free declaration tagged `(blueprint: thm-coef-finite-hom)`; the item remains a stage-1 statement split.

## WANTED

The master blueprint proof file is present at `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md`. The corresponding source paper/document named by its expanded proof is unavailable locally; the proof origin therefore remains marked as agent-expanded from the blueprint. No new external document was downloaded.

## What was wrong in the returned node

The item’s imported statement and Lean metadata were correct. The return identified four proof steps whose inline arguments exceeded 2000 characters and concealed independent lemmas. I kept the statement and its route, retained the other proof steps, and replaced the four long steps with short applications of five new statement-only nodes. The new nodes are smaller than the item and do not restate any item clause. The existing `det-sf-flat-model-generation` statement was found in the DAG and reused for the étale finite-stratification/generation argument rather than creating a duplicate. No statement correction or `STATEMENT-DISPUTED` marker is needed.

## What could not be finished

No Lean code or compiler was used, as required for this stage. The five extracted nodes remain `unsplit` for later stage-1 work.

## Review by Q47

I reread the item against the complete master blueprint file, the sec-six-functors chapter record, the `sk-prop-sf-biduality-general` unit record, and every cited node used by the repaired steps. The item’s finite-field datum, quotient rings (A\to B), separated finite-type scheme, both site alternatives, finite-Tor hypotheses, evaluation-defined map, naturality, composition, and quotient cocycle all remain verbatim. I checked that the four returned steps now have lengths 788, 1260, 1034, and 1202 characters.

For step 1 I read the statements of the derived change-of-rings, flat constructible model, K-flat criterion/change-of-rings, finite-type Noetherianity, ringed-topos tensor pullback, and exact inverse-image nodes; they give exactly the model transport and tensor comparison used there. Step 2 cites the dimension bound, constructible internal-Hom bound, K-flat and K-injective resolutions, Hom-complex/tensor adjunction, and global-sections identification; each cited statement supplies the displayed adjunction or boundedness assertion.

The repaired step 3 now cites `lem-coef-etale-hom-thick-locus`, whose statement explicitly covers the same evaluation-defined transformation, its reversed triangle maps, shifts, cones, and summands, and `det-sf-flat-model-generation`, whose clauses explicitly generate the étale finite-Tor constructible category by the stated (Rg_*j_!L) objects. I checked the empty-scheme case in that generation node and checked that its notation (g_*j_!) is the generator used in the item. Step 4 cites the finite-Tor-to-finite-projective statement; I checked that (A\) is finite local and that the degree-zero flat module case gives a finite-free local model.

For step 5 I reread the finite-type dimension, unconditional open-complement, and closed-exceptional Tor statements. The hypotheses used are exactly: (k\) separably closed, finite coefficient ring killed by a power of \(\ell\ne p\), quasi-compact complement, and the dimension bound (d\). Step 6 uses the stated finite-constructible Hom bound, the local finite-free Hom model, restriction of internal Hom, a flat constructible model, and geometric-stalk conservativity; the local rank-zero case is explicitly included.

The repaired step 7 cites `lem-coef-etale-locally-closed-shriek`, which states the same factorization (s=gj), the closed exceptional transpose, the compact-support comparison, and the exceptional-counit identity. I checked its hypotheses against step 5 and the finite-Tor object (Q\) from step 6. The cited `prop-asd-internal-adjunction` states the compactifiable Noetherian internal adjunction, and `lem-coef-finite-direct-image` states the coefficient comparison used for (c_{s,Q}\). Thus the step only takes the three displayed isomorphisms from those statements. The repaired step 8 cites `lem-coef-etale-open-tensor` for the étale projection/counit normalization, `lem-amb-proper-coproducts-projection` for the proper closed factor, `lem-coef-internal-adjunction-pairing-change` for the exact pairing equality, and the locally closed shriek node for its exceptional-counit hypothesis. Its conclusion is precisely that the composite is the specified evaluation transpose, rather than merely an endpoint isomorphism.

Steps 9–12 were retained after rereading their elementary closure, evaluation, naturality, composition, and successive-quotient arguments. Step 13 was checked against the finite-level site-comparison morphism, exactness, inverse-image flatness, and ringed-topos tensor-pullback statements. The repaired step 14 cites the two constructible-origin/Tor-amplitude statements and finite-stage duality site comparison, then `lem-coef-monoidal-square-hom-transport`. That new node states the square formula, evaluation identity, naturality, composition, and the successive coefficient cocycle under coherent strong-monoidal identifications; its hypotheses match the site-comparison maps established in step 13. The empty and zero generator cases, nonflat quotient (A\to B\), and both site choices were checked while reading the statements.

Before creating each new node I searched the whole DAG and blueprint for existing statements. The only matching existing result for the generation argument was `det-sf-flat-model-generation`, which is cited instead of duplicated. I ran and read the required LeanFinder/LeanSearch, Loogle, and Mathlib-source grep searches for every new node; the logs are in `searches.jsonl`, with generic condensed/monoidal hits rejected because their hypotheses do not specialize to these derived sheaf comparisons. `citations.json` quotes each cited statement verbatim, and all item proof dependencies are the union of the step uses. No new node cites the item or another new node in a cycle.

## Repair of immutable-head return 1ffb522d9552

The returned head was reviewed as stage 2, but it contained a stage-1 split. This delivery uses the stage-1 lane (`deliver.py`, not `deliver2.py`). H1 and H3–H10 therefore do not describe an attempted Lean delivery: there is deliberately no Lean module, Lean record, or compiler run. GOAL.md and the dispatcher's human decision authorize only stage 1; a later stage-2 delivery must separately supply every clause and the stage-2 report and compilation evidence requested in the return. Nothing here claims to complete that later work.

For H2, comparison with the current shared node shows only the five intended stage-1 fields differ: proof, proof_deps, status, split_report, and proof_origin. The statement, statement dependencies, imported metadata and maintainer fields are retained. These proof changes are submitted to stage-1 review instead of being passed off as stage-2 changes.

For A2/A3 and C1/B3, all five lem-coef-* JSON files named above are present under dag/nodes/sec-six-functors in this sandbox and included in the stage-1 dry-run receipt. They are self-contained statement-only nodes with the objects, coefficient rings and site conventions introduced explicitly, their definition dependencies, blueprint ancestry and logged searches. Steps 3, 7, 8 and 14 cite these actual files. I rechecked all 42 step/node citation entries: each quote occurs verbatim in the cited statement, and there is exactly one entry for every step citation. The new nodes remain unsplit, with empty proofs and proof dependencies. This repairs the missing-node snapshot rather than assuming the absent nodes were available.

On resumption I reread the full four-paragraph master proof, the chapter and unit records, B–E of delivery-errors.md, the retained search results, all five supporting statements and the cited item dependencies. The evaluation and exceptional-counit maps in steps 7–8 have the displayed sources and targets; step 14 uses the generic monoidal-square statement only after the site comparisons have been made invertible. The direct-image comparison is used on the étale finite-Tor object Q, not on an arbitrary pro-étale object. The nonflat quotient is allowed throughout. All 14 steps are under 2000 characters. The server check_dag check passed with only the already-declared generation tool-use advisory; the complete stage-1 dry run passed at cb5da0826c before this report clarification. The final dry run will include this clarification as well.
