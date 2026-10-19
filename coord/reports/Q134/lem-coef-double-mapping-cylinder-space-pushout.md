## Worker report

Files written: `dag/nodes/sec-six-functors/lem-coef-double-mapping-cylinder-space-pushout.json` (repaired split) and `dag/nodes/sec-six-functors/lem-coef-singular-span-bar-cylinder-gluing.json` (new unsplit statement node). The returned `lem-coef-singular-hocolim-bar` node was removed because its indexing object and coherent faces were ill-formed and it duplicated the existing Bousfield–Kan formula. `citations.json` records verbatim quotes for every cited node and `searches.jsonl` records the searches for the new node. No Lean, compiler, Lake or build tool was run.

Attachments: none. A search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no completed declaration tagged `(blueprint: lem-coef-double-mapping-cylinder-space-pushout)` or stating the item. The read-only master checkout was not used as proof evidence.

WANTED: an archived source for the singular walking-span bar-to-double-mapping-cylinder weak-equivalence comparison in `lem-coef-singular-span-bar-cylinder-gluing`; the blueprint paragraph supplies the route but no numbered theorem. The node is therefore statement-only with an agent-formulated source description. The unarchived HTT and Kerodon material is not treated as a finished Lean attachment.

## Existing nodes and duplicate checks

The split now cites `lem-coef-bousfield-kan-comparison-calculus` for the strict BK faces, degeneracies, functoriality and diagonal comparison; `lem-coef-simplicial-bar-projective-resolution` for the projective bar replacement and strict coend; `lem-coef-model-colimit-localization-comparison` for passage from the model colimit to the coherent colimit; `lem-cbc-realization-singular-unit-weak` for the realization--singular weak equivalence; and `lem-coef-simplicial-realization-cylinder` for the interval realization homeomorphism.

## Review by Q134

I read the current item, the returned review, the unit `sk-prop-sf-biduality-general`, and paragraph 2 of `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`. I also read the full statements of every cited node and checked each quote in `citations.json` verbatim.

Step 1 now constructs a strict ordinary walking-span diagram by applying `Sing` to the two continuous maps. The values are Kan simplicial sets and hence cofibrant for the Kan model structure. The projective bar-resolution node supplies the cofibrant replacement, its strict coend `R_W(V)`, the augmentation, and functoriality. The model-colimit-localization node supplies the coherent colimit cocone and its maps. The BK node is cited directly for the strict degreewise formula, faces, degeneracies, and functorial reindexing, so no coherent diagram is incorrectly treated as a simplicial set.

Step 2 is explicitly non-elementary. The new node `lem-coef-singular-span-bar-cylinder-gluing` states the comparison map from `|R_W(V)|` to the displayed quotient, its weak homotopy equivalence, endpoint counits, interval map, empty cases, and naturality. Its statement is a topological gluing lemma and does not assert the item’s coherent colimit clause. The step also cites the existing realization--singular unit theorem and the simplicial-cylinder homeomorphism, so the required counit weak equivalence, product with `[0,1]`, and quotient gluing inputs are named rather than hidden in an elementary calculation. The old bad node’s literal `\\n`, `\\to` outside math, undefined simplicial-set nerve convention, and strict-face claim for coherent diagrams are gone.

Step 3 uses the strict functoriality of the bar replacement and BK construction, the coherent cocone maps from model localization, and the new node’s naturality. I checked that a strictly commuting map of continuous spans induces a strict map of the singular diagrams and therefore commutes with endpoint maps, the bar augmentation, and the interval homotopy. Empty `A`, `B`, or `C` are covered by the new node and by the bar-resolution statement.

## Not duplicates

`lem-coef-singular-span-bar-cylinder-gluing` vs `lem-coef-bousfield-kan-comparison-calculus`: the existing node gives the strict BK/KB formulas and weak-equivalence comparisons for arbitrary ordinary-category diagrams of simplicial sets; the new node specializes to a walking span of singular realizations and adds the topological map to the double mapping cylinder and its weak-equivalence/gluing assertion.

`lem-coef-singular-span-bar-cylinder-gluing` vs `lem-coef-simplicial-realization-cylinder`: the existing node proves only the homeomorphism `|K×Δ¹|≅|K|×[0,1]`; the new node compares a full walking-span bar realization with a quotient and proves weak equivalence, including endpoint counits and naturality.

`lem-coef-singular-span-bar-cylinder-gluing` vs `lem-cbc-realization-singular-unit-weak`: the existing node proves the realization--singular unit for one simplicial set; the new node assembles three such units through a span bar and the double-cylinder quotient.

What was wrong in the returned split: the previous new node used a “small simplicial indexing set” as though it were an ordinary category and wrote an undefined `N(K)`, claimed strict faces for coherent data, and duplicated the already existing BK formula. Step 1 then took endpoint and 1-simplex data absent from that node. Step 2 silently identified a coherent colimit with a strict topological realization and omitted the singular-unit and gluing weak-equivalence arguments. Step 3 likewise lacked a cited weak-equivalence comparison. These defects are repaired by deleting that node, citing the existing strict/model-localization nodes, and adding the narrower topological comparison node.

What I could not finish: no archived literature source for the new topological comparison was available, so it remains an unsplit statement-only node and is marked WANTED. All required stage-1 files and citations are otherwise complete.

## Validation

The required server check and delivery dry run are run after this report is written; the delivery output is authoritative.
