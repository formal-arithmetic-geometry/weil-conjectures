## Worker report

Files written:
- `dag/nodes/sec-trace-formula/lem-trf-infinite-product-integral.json`: existing statement, now split into six proof steps; not a Mathlib leaf.
- `citations.json`: eleven literal statement excerpts covering every node citation in the steps.
- `searches.jsonl`: six actual msearch calls, retained with their results/digests.

New nodes: none. New Mathlib leaves: none. The proof reuses the existing product-existence, affine-morphism, spectrum, open-immersion, integral-morphism and integral-closure nodes.

Attachments: none. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item tag, integral products/limits, and IsIntegralHom found no declaration stating the item. `AlgebraicGeometry.isIntegralHom_of_iSup_eq_top` in `AlgebraicGeometry/Morphisms/Finite/Limit.lean:36` is a local criterion, not a theorem about arbitrary products. The finite-approximation theorems are also not this statement. No upstream master sorry declaration is treated as a finished proof.

WANTED: none.

The original statement agrees with Stacks Limits Tag 0CNK (`lemma-infinite-product-integral`). It is retained verbatim, with all original hypotheses and statement dependencies. There was no imported proof to retain. Stacks omits the proof and hints at integrality of an arbitrary tensor coproduct. This delivery supplies that argument in the item's own steps. `proof_origin.by` is `agent` because the explicit coproduct/integral-closure argument fills the omitted proof. It does not introduce a new node restating the ring version of the item.

Nothing remains unfinished in this one-level split. The pre-existing product-existence node remains its own stage-1 item; it is used only for existence, the product universal property, and the affine projections actually stated there.

## Sources and searches

Read `literature/stacks-project/limits.tex:160–216`: Tag 0CNI gives existence and affine projections to all finite subproducts; Tag 0CNK gives exactly the item's statement and its affine-algebra hint. Read `algebra.tex:7442–7455` (Tag 00GI), `7542–7555` (Tag 00GO), and `7569–7578` (Tag 00GP): integral elements satisfy monic equations, and they form an A-subalgebra, not just a set. Read `morphisms.tex:10957–10971` (Tag 01WH): integral means affine plus integral coordinate maps on every affine open. Read `schemes.tex:841–856` (Tag 01I1) for the spectrum morphism correspondence; only its affine-source special case, already in `def-weil-affine-spectrum`, is used.

Read the chapter and `sk-i-curve-zero` unit records and the current blueprint's `lem-trf-local-term-locality` statement and proof. The item is a descendant tool, through the recorded refinement chain, rather than that unit's key node. The recorded blueprint place is the integrality of products in the final paragraph of Tag 0CNZ; no chapter, unit, ancestry, or route is changed.

Searched the whole DAG for Tag 0CNK, integral algebras, tensor/colimit integrality, affine product/limit statements and integral closure, and ran `tools/blueprint_refs.py ancestor lem-trf-infinite-product-integral` and blueprint searches `integral product`, `product integral`, `integral closure`, `integral`, and `affine limit`. The existing integral-closure node explicitly includes the subring assertion (its lead note confirms that this is part of its Mathlib match). Thus there is no reason to create a closure-of-integral-elements lemma or a coordinate-product lemma.

The actual item searches are appended to its inherited search records. LeanFinder was tried in two formulations: arbitrary products of integral morphisms, then limits of finite fibre products. Both returned only binary coproduct, pullback, composition and related instances. LeanSearch returned ring binary products and products of integral elements, not an arbitrary scheme product theorem. The Loogle query rejected `CategoryTheory.Limits` as an unknown identifier; it is recorded as invalid and supplies no evidence of absence. Both semantic searches ran successfully, and two Mathlib grep searches ran successfully in AlgebraicGeometry. Read `Mathlib/AlgebraicGeometry/Morphisms/Integral.lean:35–80,104–110` to distinguish binary pullbacks/coproducts from the item. No search was invented; no unavailable service was reported as a negative result.

## Review by Q72

I checked the item against Tag 0CNK with the source open: S is an arbitrary scheme, J is a small set, and every factor map is integral. There is no nonemptiness, no finite-type, no Noetherian, no separation, and no base-affineness hypothesis. The conclusion is integrality of the structure map to S. The item has not been corrected or weakened.

Step 1 uses `def-weil-finite-integral-morphism` for both the affine hypothesis on each factor and the integral coordinate maps over U. I opened its statement: both assertions are explicitly present. The other theorem used is `lem-trf-affine-infinite-product-existence`: its statement includes affine projections to every finite subproduct, so it applies to the empty finite subset, whose subproduct is S. This gives affineness of the structure map itself, not merely of projections to individual factors. `pqf-def-affine-morphism` then supplies affineness of each inverse image of U, and `def-weil-affine-spectrum` supplies the notation for its coordinate ring. These are exactly the parts quoted in citations.json. No theorem about arbitrary pullback preserving integrality is needed.

Step 2 checks restriction of the product to an open base by the universal property, rather than citing a base-change theorem that the existence node does not state. For V over U the product gives a unique map to T over S; its image lies in q inverse U because its composite is the specified V to U to S. Restricting the continuous map's codomain and its sheaf map gives the factorization through that open subscheme. This follows directly from `def-weil-open-immersion`, whose statement identifies an open immersion with the open subscheme carrying the restricted structure sheaf. Uniqueness follows from uniqueness in the original product. The same argument applies to each factor. This step is elementary and is written out rather than made into a new node.

Step 3 uses `def-weil-affine-spectrum`, whose statement actually gives every morphism between spectra as a unique ring homomorphism, with contravariant functoriality. All sources and targets here are affine by Step 1, including the test object Spec D. Thus this is enough: the general adjunction for maps from arbitrary schemes is not assumed. Requiring the morphisms to be over U corresponds exactly to requiring the ring maps to be A-linear. Step 2 then gives the coproduct universal property for B. This short application of the spectrum correspondence is marked non-elementary and cited.

Step 4 explicitly applies each factor map to a monic equation. The coefficients remain images of the same elements of A because the factor maps are A-algebra maps. This uses the monic-polynomial definition in `def-weil-pbc-integral-closure` only; no uncited integrality transport theorem is hidden. No injectivity of A to B_j or B_j to B is used.

Step 5 uses the non-elementary fact that the integral elements form a subring containing A. I checked the actual statement of `def-weil-pbc-integral-closure`, including the explicit subring sentence, and read Stacks Tag 00GO; the existing node and its Mathlib match do include this fact. The A-algebra structure on C is therefore valid. Step 4 gives actual maps B_j to C, and Step 3 gives r:B to C. This is not a new restatement of the item: it is the argument establishing the omitted affine algebra fact inside the item.

Step 6 checks the equation e r = identity on B by composing with every coproduct injection, using the uniqueness already proved in Step 3. The equality implies that every element of B belongs to the integral-closure subset C. Since U was any affine open, and affineness of q was obtained before any choice of U, the exact definition of an integral morphism finishes the proof. This is an elementary universal-property calculation and application of the cited definitions.

I tested J empty: B is the initial A-algebra, the uniqueness assertion still applies, and T is S. For a singleton the reasoning recovers the factor's own monic equations. I tested zero rings and empty schemes: no existence of points or primes is used, and equations, subalgebras and the coproduct property still make sense. No chosen factor, faithful map, finite generating set or bounded equation degree is assumed. Smallness is inherited from J and the project's size convention; no large category is used as an index of a colimit.

Against delivery-errors B–E: no new statement-only nodes or duplicate nodes are introduced; all cited notions already exist; the unchanged statement is self-contained. Every non-elementary fact used is explicitly in the statement of a cited node, with literal excerpts in citations.json. There is no citation to an internal proof of another node. There is no new dependency back to this item and no off-unit non-Mathlib tool beyond the product-existence node in the same unit. The proof carries the actual argument rather than moving the item into a new lemma. Each step is below 2000 characters (longest 746), and the coproduct comparison and integral-closure calculation are explicitly written. The route uses only Stacks and the existing blueprint ancestry, with no SGA source. No Lean source, live repository, or launcher file was changed, and no compiler was run.

## Not duplicates

No new nodes, hence no new/existing-node pairs requiring comparison.
