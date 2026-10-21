## Worker report

Files written: `dag/nodes/sec-smooth-purity/lem-sf-cbc-localized-strict-tensor-descent.json` (item, statement, split into eight steps), `citations.json`, and this report. The sandbox also retains the actual search log and the sandbox-only writing script. No repository, launcher, or Lean file was changed. No compiler was run.

## New nodes

None: 0 new nodes, 0 Mathlib leaves. Existing general ringed-site and localization results suffice. In particular, I reused `lem-sf-ringed-open-total-tensor-kflat` rather than creating a new extension-preserves-K-flat lemma, and `lem-trf-site-one-sided-tensor-normalization` rather than duplicating its one-sided representative theorem.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, localized strict tensor descent, and strict coefficient towers produced no declaration stating this item. Existing generic tensor computations do not assert its strict diagram, scalar-linearity, unit, and representative-normalization clauses together. No sorry declaration was treated as finished.

## Literature and blueprint

No WANTED document. I read `sites-modules.tex` Tag 0E8I (`lemma-j-shriek-and-tensor`, including the five Hom identifications), the extension-presheaf and module-sheafification interfaces at Tags 03DI and 03CY, and `sites-cohomology.tex` Tags 06YS (`lemma-K-flat-resolution`), 06YT (`lemma-derived-tor-quasi-isomorphism-other-side`), 06YU (`definition-derived-tor` and its preceding construction), 0G7D (`lemma-factor-through-K-flat`), and 0GL1 (`lemma-j-shriek-and-tensor`). Tag/label pairs were checked in `tags/tags`. The strict-diagram and all-representative refinement is marked agent-written: 0GL1 alone, whose proof omits details, does not state that refinement.

I read the chapter and unit records and the current `main-20261015` text and proof of `fix-lem-exchanges`. This item realizes its construction Step 1 (the extension-by-zero identification in the open factor) and its Step 2 (coefficient naturality). It uses ordinary, unbounded ringed-site categories, as the imported statement requires. No adic completeness, finite quotient, étale-origin, or discrete coefficient restriction was introduced. No SGA source was used.

Blueprint searches: `ancestor lem-sf-cbc-localized-strict-tensor-descent`, and whole-blueprint searches for `K-flat`, `extension tensor`, `0E8I`, `strict tower`, and `tensor-product-pullback`. There is no blueprint node with the full arbitrary-algebra-tower normalized statement. The nearest ancestor remains `fix-lem-exchanges` through `lem-sf-cbc-extension-zero-completion`.

## Mathlib searches

The inherited searches of the item were retained; every new search recorded on it is copied from this sandbox's actual `searches.jsonl`. I ran LeanFinder with both the strict coefficient-tower formulation and the derived projection-formula/coefficient-ring formulation, Loogle with `"SheafOfModules", "tensor"` and `"SheafOfModules", "extend"`, LeanSearch for extension by zero and derived scalar extension of strict inverse systems, and two source greps through `msearch.py`. All services answered. The tensor hits are presheaf tensor definitions and maps; the sheaf hits concern free sheaves or sheafification/pullback; the remaining hits concern flat ordinary modules, function extension by zero, Ext zero maps, or algebraic localization. None is the asserted ringed-slice derived strict-tower comparison. No unavailable service was recorded as a negative result, and no search not run was added.

## Problems and corrections

The imported statement was retained verbatim, as were its statement dependencies, provenance, and inherited search records. There was no statement dispute. Its proof was empty. The split now supplies the argument behind the normalized map and the strict transition equations, rather than inferring a derived strict-diagram isomorphism from unrelated isomorphisms of its evaluations.

A potential citation error was ruled out while preparing the proof: `lem-weil-pbc-module-pullback-tensor` is about scheme structure sheaves and cannot justify arbitrary diagram-site evaluation. The split instead cites `lem-pur-cochain-pullback-tensor-coherence`, whose statement is for arbitrary morphisms of ringed topoi on small sites, and `lem-weil-pbc-diagram-site-realization`, which explicitly makes each evaluation such an inverse image. Likewise the ordinary-ring-only `lem-pc-kflat-tensor-quasi-iso` is not used as a sheaf theorem. The small-site one-sided normalization node supplies exactly the needed assertion for arbitrary coefficient complexes.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs.

## Tool uses

The generic off-unit statements are declared in `split_report.tool_uses` for maintainer judgement, with reasons. They are foundational sheafification, exact extension, diagram-site, total-tensor, and localization tools. They do not use proper base change, purity, Picard duality, or Künneth as geometric theorems and do not replace the unit's route. No top-level `tool_uses` approval was written.

## Review by Q05

I reviewed delivery-errors B–E against the actual statements, the source formulas, and all eight proof steps. There are no new unsplit statements requiring independent sources or Mathlib verdicts, and no clause of the item was moved into a new node. All proof dependencies were opened as statements; `citations.json` records verbatim statement text for every step/dependency pair. I checked their transitive dependency closures and found none leading back to this item.

Step 1 uses the actual site-general `lem-pc-kflat-resolution`, exact slice extension/restriction, exact-functor localization, and `lem-sf-ringed-open-total-tensor-kflat`. That last statement explicitly applies to arbitrary unbounded ringed-site complexes and asserts K-flat preservation. Its statement does not assert flat terms, so the step proves this separately from the sheaf projection isomorphism and the definition of flatness, applying two exact functors around tensor by each flat term. It uses no constant-ring or subterminal-object hypothesis.

Step 2 uses precisely the geometric-morphism evaluation clause of `lem-weil-pbc-diagram-site-realization` and levelwise exactness of `lem-weil-tower-category-levelwise-abelian`. The ordinary cochain pullback theorem supplies the tensor comparison including direct sums and differential, and left-adjoint preservation supplies coproducts. The rest is the explicit acyclic-tensor test: evaluate, use K-flatness of P, and detect zero cohomology componentwise. The same short argument on exact sequences proves flatness of the diagonal terms. There is no claim that an arbitrary family of derived objects forms a strict tower.

Step 3 uses the exact scope of `lem-trf-site-one-sided-tensor-normalization`: its first factor is flat-term K-flat, whereas its second factor can be arbitrary. Thus the coefficient tower need not be flat, surjective, or bounded. The termwise extension on towers is exact by the cited levelwise theorem and the actual exactness of slice extension. The cited exact-derived-factorization statement says its unchanged termwise complex computes the derived functor, which is what the step needs.

Step 4 writes both generator maps and both composites, using the direct-sum extension presheaf, tensor's sheafification definition, bilinear extension existence/uniqueness, and the module-sheafification interface. It therefore proves the normalization formula rather than taking a formula absent from the projection node's statement. For an object (W,u) of the slice, its restricted coefficient sections are exactly S(W), so the inverse formula is typed correctly. The same sectionwise action identifies extension before and after forgetting coefficients. The maps are S-linear, and that linearity is not inferred from mere R-linearity.

Step 5 is elementary after Step 4 and the cited two-variable naturality: the differential is d_P tensor 1 and each transition is 1 tensor s_n. The transition equation and the map of algebra towers are written explicitly. The scalar-unit equation is the same generator calculation at s=1. Since all calculations occur on the strict complexes, this step does not attempt to detect an equality of derived tower maps merely by evaluating them.

Step 6 uses the actual statement of `lem-weil-pbc-site-derived-tensor-descent`, which identifies the localization of flat-term K-flat homotopy complexes with the whole ordinary derived category. The localization theorem explicitly descends natural transformations uniquely and respects composition. Both the comparison and its inverse are descended. Homotopies are respected by h tensor 1, since the coefficient complex is concentrated in degree zero. Thus the natural transformation is defined on the representative homotopy category, not just on chosen objects.

Step 7 uses the same fully faithful localization statements to compare two choices of representatives and to descend the coefficient naturality square. The formula conjugating by q makes the precise canonical comparison explicit. This proves uniqueness among natural transformations with the stated normalization without claiming uniqueness of all possible derived natural isomorphisms.

Step 8 uses exact evaluation's localization comparison and the already established ordinary tensor comparison. The identity-topos specialization of `lem-weil-pbc-ringed-topoi-derived-pullback` really allows arbitrary ring maps and computes derived scalar extension on flat-term K-flat input. The exact slice-extension lemma also applies with ring S_n, so its output is computed on the displayed complex even when that complex is not termwise flat after restriction to R. Exact scalar restriction from `lem-weil-pbc-restriction-derived-products` is used only for its explicitly stated exactness, not its product conclusion. The generator map from Step 4 is S_n-linear before localization, providing the required linear derived map with the evaluated underlying R-map. The normalization and localization faithfulness identify maps, not only objects.

For edge cases I checked zero K, zero coefficient algebras, identity slice extension when V is final, and a site where several arrows W to V index distinct summands. The latter is why the proof uses [p]_u rather than pretending the slice is always an open subset. On the one-point site with V final, R=Z and S_n=F_2 (constant tower), the formula is the identity of the ordinary derived tensor computed from P, and does not assert ordinary tensor is exact for F_2. Non-surjective transitions, such as the endomorphism x to x^2 in the constant algebra family Z[x], still satisfy the written naturality equation. For unbounded P the argument uses direct-sum totals and the cited unbounded K-flat theorem; no bounded-above flattening argument is substituted. All eight steps are shorter than 2000 characters, and each comparison used as a black box is the statement of an existing node.

Nothing remains unfinished in this stage-1 split. The required server dry run and push are the delivery checks; this report does not claim a Lean proof.
