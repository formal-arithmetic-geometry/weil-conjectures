# Q95 — lem-pur-compactification-b-projection-reduction

## Files written

- `dag/nodes/sec-poincare-duality/lem-pur-compactification-b-projection-reduction.json`: statement, split into eight proof steps using existing nodes; no Mathlib match.
- `citations.json`: verbatim statement excerpts for every cited node of every proof step.
- `searches.jsonl`: real search-command log, retained alongside the original searches in the item.

New nodes: 0. Mathlib leaves: 0. The sandbox also contains the reproducible local `write_split.py` working script; it is not a DAG delivery file.

## Attachments

None. Searched the live `lean/WeilConjectures` tree for the blueprint tag and for reconstruction, tower/reduction projection and completed projection. The finite pro-etale `ProjectionFormula.lean` and the etale `ProjectionFormula/Reduction.lean` concern finite/discrete coefficient maps. They do not assert this equality for the entire semilinear system, completed operations, and the pinned compactification reconstruction map. Thus no exact finished project declaration was found. No Lean was written or compiled.

## WANTED

None. The current blueprint and the existing DAG statements suffice for this assembly. No SGA source is used.

## What needed attention

The imported item had no proof. Its central requirement is normalization by a specified natural map b, not merely compatibility of evaluated objects. The statement remains verbatim. I kept the complete/ordinary distinction explicit before applying the existing ordinary projection-descent theorem. That theorem requires two invertible system factors, not merely an invertible composite: the existing tower compact-support projection theorem states the invertibility of both factors separately.

The source field is historical provenance from the item that created this node. The proof sources and proof origin use `literature/blueprint/latest/`, currently main-20261024 at ef6f9619fdbffa59e88528fb56483d76c70258c8. I read the chapter and inherited sk-lem-finite unit; this item is not its key node, so no unit realization file is changed. The generic coefficient and adjunction tools are explicitly listed in split_report.tool_uses for the maintainer's route review.

## Not duplicates

No new node was created. I searched the entire DAG and the blueprint reference index for projection, completed tensor, pinned whole-system and projection mate. The existing `lem-sp-complete-projection-mate-descent` is the useful more general theorem, with ordinary operations and additional completeness/comparison assumptions, rather than a missing lemma to recreate. Its dependency graph does not reach this item. I also checked that the ordinary-operation, tower-projection and reconstruction tools do not reach this item. The item itself is not the blueprint's statement of that descent theorem: it specifies completed operations, a pinned b, tensor order and an inverse equation.

## Mathlib searches

The six Q95 command searches are logged in searches.jsonl and appended without rewriting the item's Q43 search history. Both natural-language phrasings were read. The first LeanFinder search returned compactly supported continuous-function integrals; the second returned general monoidal adjunction counit formulas and condensed solid counits. Loogle returned general monoidal adjunction and monoidal-closed Hom formulas. LeanSearch returned locally constant/condensed counits and a total-left-derived counit. Neither grep found a matching projection/reduction/tower comparison. None of these signatures gives the actual compactification reconstruction comparison in this item's system category. No new Mathlib absence claim is used to create a node.

## Review by Q95

I read the latest tower-geometric-gamma proof, particularly (2), which uses the inverse compact-support projection in the tensor transpose, and the latest integral-adjunction-direct-image proof (1)-(3), which supplies the intended direct-image/reduction route. I read the latest integral-adjunction-bijection normalization paragraph, and the latest ordinary integral tensor and pullback proofs to check that the completion comparison is the canonical map, rather than an arbitrary equivalence. The proof is marked agent-written: the blueprint's loose limit argument is not cited as a ready-made coherence theorem. There are no new nodes whose sources remain to be checked.

Step 1 uses the statements of det-lem-int-tensor-pullback (both preservation and its actual c_K comparison), det-lem-int-tensor-product (ordinary tensor remains integral constructible), det-sp-integral-direct-image-tower (canonical direct-image reconstruction, normalization and the Tor widening), det-sp-normalized-equivalence (actual reduction/limit adjunction and normalized domains), lem-sf-pullback-tor-amplitude and lem-sf-tensor-ctf (the finite intervals). All their scheme and coefficient hypotheses hold: f is smooth separated with fixed dimension, the base is the specified algebraic closure, and the finite level at index n is the allowed uniformizer level en. The bounds are independent of n. In particular I did not conflate a finite module over an Artinian quotient with a perfect one; the Tor bounds are part of the given input and of the cited preservation theorems.

Step 2 uses the actual balanced quotient formulas of lem-sp-reduction-derived-monoidal-tower, the defining completed operations, the normalized adjunction and the canonical pullback comparison. I checked the direction: ordinary tensor maps to L of the tensor reduction system by L(mu) followed after the actual unit. Applying reduction and the actual counit recovers the stated comparison by the triangle identity. The comparison therefore has exactly the quotient/counit normalization requested by the item. It includes tensor transitions before any limit is taken.

Step 3 checks the actual projection transformation. det-lem-int-tensor-shriek puts j_!M in the same complete constructible category on the compactification; the pullback and tensor theorems apply there too. The definition def-exchange-projection specifies the proper map as an adjunct and the open map as the inverse unit projection. I checked the two Hom transposes: the proper one is the same counit tensored with identity under the completion-unit identifications, and the inverse open one is the same open unit tensored with identity. The open normalization lemma states full faithfulness and the adjunct formula, and the derived monoidal-comparison lemma states the monoidality and adjunction compatibility of the compositor. This is a short comparison of the displayed defining formulas; no replacement purity or trace theorem is being hidden in it.

Step 4 uses the quasi-compact-open triangle lemma with T=X, Y=the middle compactification, B=the target. Its composite is quasi-compact and its second map is proper and therefore quasi-separated. The compactification/limit realization statement gives the actual augmentation-normalized natural alpha, not just its levels. det-sp-integral-direct-image-tower (2) and lem-sp-integral-reconstruction-comparisons identify the actual b used by this problem with its reconstruction transpose. This checks the strongest hypothesis of the descent theorem and prevents a change of b by a tower automorphism.

Step 5 uses the full statement of lem-sp-tower-compact-support-projection-formula, which states both arrows are isomorphisms and specifies their respective counit/unit transposes. Its inputs have common constructible/Tor bounds by Step 1, and its compactification is this same c. I checked every other assumption of lem-sp-complete-projection-mate-descent: complete M,K,H,U,V, bounded-below reductions, and both canonical comparisons for N=M,H. The theorem concerns ordinary ringed coefficient sheaves, just as the temporary operations in Steps 1-3 do.

Step 6 takes the actual morphism equality from that descent theorem, not any assertion found only in its proof. The derivation after applying r is written out using naturality of e and the triangle identity. The source is rV and the target is rU; the coordinate a is on H, while b_H has target F rH, so F(a)b_H is composable. This yields the unswapped projection square as an equality in the derived category of whole systems.

Step 7 uses naturality of b from lem-sp-integral-reconstruction-comparisons, the symmetric monoidal derived comparison statement, and lem-pur-completed-operation-tower-substitution, whose statement explicitly includes the Koszul symmetry, actual coherent reduction, compositor and substitution normalization. I checked the tensor order: the input becomes K tensor PM; H is changed to f^*K tensor M; and the source coordinate is (1 tensor b_M)tau, exactly s. No equality of arbitrary system morphisms is inferred by evaluation. Step 8 is elementary cancellation of isomorphisms with the same source and target; I checked the directions of Pi and Pi-bullet and used functoriality for r(Pi).

I checked delivery-errors B-E point by point. No fresh statement-only node, duplicate, clause relabeling, unrun search, change of target, or cycle is introduced. Every step's uses has a verbatim statement excerpt in citations.json; I read the statements rather than borrowing constructions from proofs. The only elementary step is explicit inversion. All other facts have cited nodes. Every step is below 2000 characters. For small cases I checked identity f with trivial compactification (the square becomes monoidal reduction coherence), open-only and proper-only factorizations (one projection factor disappears), zero inputs, relative dimension zero, shifts (canonical Koszul symmetry retained), and ramification e>1 (levels are en and the existing descent theorem already uses ell-powers). None requires an added hypothesis or a statement correction.

## Unfinished

No mathematical part of this one-level split remains. The existing cited unsplit lemmas retain their own queue work; they are not claimed proved by this delivery. The required server dry run and push are performed after this report is written.
