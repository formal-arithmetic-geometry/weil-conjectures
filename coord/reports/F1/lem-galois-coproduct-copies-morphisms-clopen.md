# lem-galois-coproduct-copies-morphisms-clopen

## Files written

- `dag/nodes/sec-curve-estimates/lem-galois-coproduct-copies-morphisms-clopen.json`: five-step split, no new nodes and no Lean edits.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint tag, coproducts, clopen morphisms, fibre opens, and continuous-map gluing. `Scheme.EtaleTorsor.exists_fiberOpens_comp_sigmaι` in `AlgebraicGeometry/Morphisms/EtaleTorsorDescent.lean:75` gives the forward decomposition for a morphism into a coproduct; `Scheme.glueOfContinuousMap` in `Mathlib/AlgebraicGeometry/Gluing.lean:728` constructs a morphism from a locally constant map. Neither states the claimed bijection with all of its uniqueness, base-map, and empty-index clauses. `Etale.constantSheafIsoContinuousMapSheaf` is an abelian-group sheaf theorem, not this set-valued scheme correspondence. No exact declaration is attached.

## WANTED

None. The local `literature/stacks-project/` checkout is absent in this worktree, but the cited Stacks documents were read at their official tag pages: Schemes 01JB and 01HI, Groupoids 03YW, and Etale Cohomology 03P5.

## Source and blueprint

Stacks Groupoids Example 03YW states that the base change of a coproduct of copies of the base represents locally constant maps to a discrete group. Its construction uses only the indexing set for this functor-of-points assertion. Schemes Lemma 01JB gives the two mapping properties of a scheme glued from open pieces; taking empty overlaps gives a disjoint union. Schemes Lemma 01HI supplies restriction through an open subscheme. The source omits the proof of 01JB's mapping properties, so the split writes the argument and marks `proof_origin.by = agent`.

The item is a created node under blueprint ancestor `thm-galois-lc-etale`, via `lem-galois-constant-sheaf-sets-representable` and `lem-galois-flc-representable`. `blueprint_refs.py search 'locally constant maps'` and `search 'coproduct of copies'` found no blueprint node with this assertion. The existing `blueprint.from.place` and `same_as: []` remain correct. Its unit is `sk-prop-h2`; this helper is not the unit's key theorem and does not change its recorded route.

## B-E self-check

- B1-B10: no new nodes. The existing statement introduces the arbitrary set, schemes, coproduct, structure map, clopen pieces, and empty case; its definition citations are present. Its previous LeanSearch, LeanFinder/Loogle, and Mathlib source searches record no exact match. Mathlib `Limits.lean` provides the general coproduct, `OpenImmersion.lean` the lift through an open, and `Gluing.lean` the gluing lemma, each through an existing public DAG leaf. No exact sorry-free slopmaster2 declaration was found.
- C1-C8: Step 1 uses the public coproduct-family statement for component geometry and the codiagonal. Step 2 takes inverse images and the complement union. Step 3 uses the public open-factorization statement and the component isomorphism; composing with the codiagonal forces the restriction. Step 4 invokes the public morphism-gluing statement for existence and uniqueness and checks both inverse composites. Step 5 is the elementary equivalence between an indexed partition and a function, plus the constant and empty cases. All cited statements assert the facts used; all off-unit citations are Mathlib leaves. There is no new cycle.
- D1-D5: no child restates the item. The proof supplies the previously omitted mapping-property argument and the inverse correspondence, including uniqueness.
- E1-E6: no quasi-compactness or finiteness assumption enters; an infinite index set is allowed. For `E = ∅`, the coproduct is empty and the only admissible `W` is empty. For `W = ∅` and nonempty `E`, the empty decomposition and unique morphism agree. For `U = ∅`, any `W → U` already forces `W = ∅`. For one index, the only decomposition is the whole `W`, and the morphism is `ι_e ∘ s`. Empty overlaps are handled by the gluing lemma, including the empty family.

## Verification and outstanding work

- `python3 tools/review_split.py lem-galois-coproduct-copies-morphisms-clopen`: PASS, zero new nodes.
- `python3 tools/blueprint_refs.py check lem-galois-coproduct-copies-morphisms-clopen`: PASS.
- `python3 tools/check_dag.py`: zero cycles and self-loops; exit 1 on seven unrelated reachability and eleven unrelated route errors in the current base, all outside this item.
- `git diff --check`: PASS.

No item hypothesis, source, or blueprint statement required correction. The local Stacks checkout is absent; the official tagged source pages were available and checked.

## Review by F1

I read Stacks Schemes `lemma-glue` (01JB) and `lemma-restrict-map-to-opens` (01HI), and Groupoids Example `example-constant-group` (03YW). In 01JB the two mapping properties explicitly identify morphisms into a disjoint gluing with an open partition and maps on its pieces; 03YW specializes this to locally constant maps into a discrete index set. The group operation in 03YW is irrelevant to the underlying set-valued correspondence. The item's statement keeps arbitrary E and scheme U, and its empty-index, empty-domain and constant-map clauses follow from the same construction.

I checked the public statements of `lem-weil-pbc-scheme-coproduct-family`, `lem-weil-pbc-morphism-factors-through-open-subscheme`, and `lem-weil-pbc-scheme-morphism-gluing`. Step 1 takes exactly the disjoint open summands and coproduct mapping property from the first; step 2 forms their open inverse images and proves closedness by the union of the other opens. Step 3 uses the open-factorization node to identify each restricted map, and the codiagonal equation forces its value to be `s`. Step 4 uses the gluing node's existence and uniqueness on the disjoint open cover, and checks both directions of the inverse correspondence. Step 5 is elementary set partition algebra and handles E empty without asserting a map from a nonempty scheme to the empty scheme. This supplies the mapping-property verification that 01JB leaves to the reader, with no reliance on an unstated construction inside a cited node.

There are no new nodes, so B1-B10 require only the item's self-contained statement and existing definition citations; the worker's blueprint/DAG and read-only Lean searches found no exact duplicate. The related source declarations cover only one direction or a constructor, not the full bijection. I checked A-F, including the infinite-E case (no finiteness enters), E singleton, W empty, and U empty. The five steps are a noncircular proof of the full assertion, not relabelled clauses, and all off-unit inputs are existing Mathlib leaves. `review_split.py` and the cycle check pass; the unrelated global route findings do not involve this item.

