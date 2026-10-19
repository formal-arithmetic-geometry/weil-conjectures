1. Files written:

- `dag/nodes/sec-six-functors/lem-coef-open-cover-weak-equivalence.json` — statement, split proof, no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-open-cover-singular-excision.json` — statement-only node, no Mathlib match.
- `citations.json` — verbatim citations for every non-elementary node use.

2. Attachments: none. No sorry-free declaration in the read-only Lean source states this item exactly.

3. WANTED: an archived source for the arbitrary-space singular-complex excision theorem used in `lem-coef-open-cover-singular-excision` (May, *A Concise Course in Algebraic Topology*, Chapter 10 §7, final excision theorem, printed pp. 80–82).

4. What was wrong or incomplete: the imported item had no proof and its existing downstream double-cylinder node cites the item, so citing that node here would create a cycle. I therefore used the acyclic singular-complex route and added the smaller excision node. The statement was checked on empty opens, empty intersections, a point, a disjoint union, and the identity map; no hypothesis was added or dropped. Mathlib's open-cover gluing declarations give ordinary homeomorphisms only, and its singular-set declarations give the functor/adjunction only, so neither is a Mathlib leaf for the new node.

## Not duplicates

- `lem-coef-open-cover-singular-excision` vs `lem-coef-double-cylinder-weak-equivalence-gluing`: the new node concerns the singular subcomplex pushout associated to an open cover; the existing node concerns invariance of a double mapping cylinder under a weak-equivalence map of arbitrary spans, and its proof depends on this item.
- `lem-coef-open-cover-singular-excision` vs `lem-coef-singular-span-bar-cylinder-gluing`: the new node is the open-cover singular excision map; that node compares a walking-span bar realization to a double mapping cylinder for arbitrary simplicial spans.
- `lem-coef-open-cover-weak-equivalence` vs `lem-coef-double-cylinder-weak-equivalence-gluing`: the item is descent of weak equivalences from an open cover, while the existing node is homotopy invariance of a specified double mapping-cylinder construction.

## Review by Q09

I reread the item, its unit `sk-prop-sf-biduality-general`, chapter `sec-six-functors`, the blueprint paragraph in `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, and the full statements of every cited node. Step 1 uses the new singular-excision statement exactly for the covers of `Y` and `X`; it supplies the canonical pushout-to-singular maps and explicitly allows arbitrary spaces and empty cases. Step 2 uses the singular counit statement for its natural evaluation maps and all component and homotopy-group isomorphisms, and uses the realization criterion to translate the resulting realization weak equivalences into the simplicial weak-equivalence convention. Step 3 checks that the overlap inclusions are monomorphisms and applies exactly the first clause of `lem-coef-sset-gluing-filtered-equivalences`, whose hypotheses are three commuting component weak equivalences and monomorphic first legs. Step 4 uses naturality of the singular subcomplexes and cancellation in the square with the two excision maps; every map named there is supplied by the cited statements. Step 5 uses the natural evaluation square and cancels the two counit equivalences and the realization of `Sing(h)` to obtain the cubical weak-equivalence definition in the item. I verified that all hypotheses include the subspace topologies, that inverse images of the opens are open, and that no separation, compact-generation, connectedness, or nonemptiness condition entered. The `proof_deps` union and every `citations.json` quote were checked against the node statements. I did not use the downstream double-cylinder node, so the dependency graph remains acyclic.

5. What I could not finish: no local archival copy of May's cited excision theorem is present; this is recorded as WANTED. No Lean code or compiler/build tool was used, as required for stage 1.
