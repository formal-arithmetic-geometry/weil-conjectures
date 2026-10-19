# Worker report

1. Files written: `dag/nodes/sec-six-functors/lem-coef-marked-sharp-anodyne-restriction.json` is the existing item, split into seven proof steps with no new nodes or Mathlib leaves. `citations.json` records a verbatim quotation for every cited step-node pair, and `searches.jsonl` records the Q124 Mathlib searches.
2. Attachments: none. Exact-id and notion searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` found no project declaration stating this item; `dag/lean_names_upstream.json` has no entry. No upstream sorry declaration was treated as a finished proof.
3. WANTED: Jacob Lurie, *Higher Topos Theory*, Section 3.1.3 (mapping formulas), Proposition 1.2.5.3 (Kan core), and Corollary 3.1.4.4 (sharp parameters), for `lem-coef-marked-sharp-anodyne-restriction`. The source is not archived in the supplied literature; attempts to read the author-hosted PDF returned HTTP 429. The proof is therefore marked `proof_origin.by = agent` and reconstructs the argument from the existing cited DAG statements and the pinned Mathlib pushout-product source.
4. The imported statement is unchanged and is well-typed. Its blueprint ancestry and unit binding are retained. The chapter and unit records and the ancestor proof file `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md` were read. No source error or duplicate node was found.
5. Nothing remains mathematically unfinished. No Lean files were written and no compiler, Lake, or build was invoked.

## Review by Q124

I checked the statement against its explicit marked-simplicial-set definitions. Since both factors of `K^sharp × (Δ^n)^sharp` mark every edge, marked maps into `C^natural` are exactly maps whose edges are equivalences, hence they factor uniquely through the core `C^≃` defined by `def-cbc-enhanced-diagrams-cones`; this verifies step 1 and its degree-zero case. Step 2 uses the same precomposition maps on both sides for simplicial operators and restriction, and a quasicategory map preserves inverse edges and their two triangle witnesses, so postcomposition preserves the core. The definition node says each of these facts.

For step 3 I read `lem-cbc-enhanced-functor-cone-calculus` in full. Its statement supplies exactly that the core of every quasicategory is Kan, with no nonemptiness hypothesis; this is declared as the generic off-unit tool use in `split_report.tool_uses`. For step 4 I read `lem-coef-kan-quillen-right-proper` and `lem-coef-sset-anodyne-pushout-product` in full. The former turns the degreewise injective weak equivalence `j` into the required trivial cofibration/anodyne map, and the latter gives the anodyne pushout product with each boundary inclusion. I also read `Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/PushoutProduct.lean:95–103`, which is the existing Mathlib leaf used there.

Step 5 explicitly performs the simplicial exponential adjunction: a boundary square for `Fun(L,E) → Fun(K,E)` is the compatible map from the pushout-product domain, after switching product coordinates, and step 4 extends it. Step 6 applies the boundary characterization in `lem-coef-kan-quillen-right-proper` and identifies this exponential restriction with the marked restriction from steps 1–2. I checked `n=0`, empty `K` and `L`, empty `C`, identity inclusions, and a point quasicategory; no extra hypothesis is needed. Step 7 checks that subsets, finite simplices, products, pushouts, and map sets remain in the input universe using `def-weil-size-convention`.

I checked delivery-errors B–E: every non-elementary fact is cited; every cited node says the clause used; no item clause was moved into a new node; no duplicate or dependency cycle was introduced; no SGA source was used; and no hypothesis is silently added. All seven steps are below 2000 characters and none hides a separate lemma. The two LeanFinder phrasings, LeanSearch, Loogle, and grep searches in `searches.jsonl` returned only generic unmarked Kan/quasicategory/model-category declarations, so the complete marked assertion is not a Mathlib leaf.

## Not duplicates

No new nodes are proposed. The existing core-Kan and unmarked pushout-product results are cited directly rather than duplicated.

## Validation and delivery

The prior delivery reached the review-preparation stage but its fetch timed out. This repaired sandbox is ready for a fresh single dry run.
