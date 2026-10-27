# Stage-1 delivery: lem-sfb-derived-scalar-mate-thick-locus

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-derived-scalar-mate-thick-locus.json`: statement, split into eight proof steps; no Mathlib match for the full item.
- No new nodes and no new Mathlib leaves.
- `citations.json`: an entry for every cited node in every proof step, quoting its statement verbatim.

## Attachments

None. Searched the project Lean source for the blueprint id, scalar mates, scalar comparison and thick loci. The existing scalar pullback/restriction mate declarations in `WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/Derived/ExtendScalars/RestrictScalarsMate.lean` concern constant ordinary coefficient rings, with a Noetherian hypothesis in the derived extension setup. They do not state this lemma for arbitrary commutative ring sheaves, nor its complete thick-locus assertion. They are not attachments for this item.

## WANTED

None. The item is explicitly an agent-extracted expansion of the blueprint, rather than a theorem claimed to appear verbatim in the literature. The proof is marked `proof_origin.by = agent`.

## Audit of the imported item

The imported item had no proof. Its statement is well typed and true as written: the geometric coefficient maps are the specified inverse-image identifications, so geometric module pullback is exact even if the coefficient change is not flat. The original statement, source, created record, chapter, unit and blueprint provenance are preserved. No statement dispute or route departure was necessary.

The unit is `sk-thm-sf-ctf-stability`; this node expands a technical subargument of paragraph (3) of `det-thm-sf-ctf-stability-direct-images`. It is not the unit's key statement, so no unit realization file is edited. The imported blueprint ancestor is null; `blueprint_refs.py ancestor` likewise reports None. Its precise existing `from.place` and via chain have been retained. Whole-blueprint searches for scalar mate, derived scalar, thick isomorphism, projection and triangle-morphism found no blueprint node stating this full item in another form, so `same_as` remains empty.

A number of nearby nodes are restricted to constant finite coefficients or coefficients pulled from condensed rings. In particular `lem-sp-proetale-scalar-tensor-normalization` is not applied to arbitrary ring sheaves, and `lem-sfb-internal-scalar-mate-projection` is not treated as a general ring-sheaf theorem. Instead the proof constructs the tensor identification, compares the balanced chain maps, and computes the actual adjunct. Likewise the full item is not replaced with a new node stating its clauses.

## Mathlib searches

The sandbox `searches.jsonl` records the actual command results. Ran LeanFinder twice, Loogle, LeanSearch, and grep through the prescribed msearch command. The two natural-language formulations describe the normalized scalar direct-image mate/projection and its exact thick locus. Hits are ordinary sheaf adjunctions and ordinary scalar extension; Loogle finds the general shift-compatible adjunction structures. The grep for scalar-extension/shift/projection combinations returned unrelated Lie, matrix and C-star algebra results. No result states the complete item. Existing imported search records are preserved, and this delivery adds only the searches actually logged for Q58. No new node requires searches.

## Review by Q58

I read the current blueprint direct-images proof, especially paragraph (3), and its scalar-pullback proof paragraph (1). Neither is presented as a proof of the entire extracted lemma. I read the supporting local Stacks source: sites-modules.tex, the change-of-rings construction and `lemma-adjointness-tensor-restrict`, and Tag 03EL (`lemma-tensor-product-pullback`); sites-cohomology.tex, Tags 06YY (`lemma-derived-base-change`), 06YU (`definition-derived-tor`), 07A4 (`lemma-pullback-tensor-product`), 07A6 (`lemma-adjoint`) and `lemma-adjoints-push-pull-compatibility`; derived.tex, Tags 014A (`lemma-third-isomorphism-triangle`) and 0A8D (`lemma-adjoint-is-exact`); and sites-cohomology.tex Tag 0FPT (`lemma-symmetric-monoidal-derived`). There are no new nodes with additional sources to audit.

For step 1, I opened the statements of the ordinary scalar/tensor comparison, derived change of rings, ringed projection exactness, and resolving tensor descent. The ordinary comparison really permits a general map of ring sheaves; derived change of rings computes on K-flat representatives with no flatness assumption on the map. Projection exactness explicitly permits computation by resolving one tensor factor. Tensor descent supplies the resolving localization equivalence. Thus the construction does not incorrectly suppose that the restricted target ring is flat or K-flat. The inverse maps on tensors are written, and localization makes the identification natural.

For step 2, I opened the statements of the normalized K-flat scalar comparison, restriction/change adjunction, and derived tensor pullback. The normalization node identifies the inverse of the displayed ordinary comparison with the scalar mate, fixing the orientation of lambda. The pullback theorem states preservation of flat-term K-flat complexes. The two composites are checked on the same balanced generators; the extension of the equality uses the cited resolving equivalence, not an unstated independence-of-model assertion. Neither coefficient ring needs to be constant.

For step 3, the ring-sheaf change-adjunction statement explicitly identifies the adjunct after restriction, including both b and d and their directions. I use that exact equation, then naturality of e at the A-counit, and the equality proved in step 2. The first-variable projection node defines its arrow as the adjunct of precisely the remaining expression. The pro-etale operations node provides the actual geometric derived adjunction. This establishes equality with the specified projection map, without relying on equality of object values or on unnormalized uniqueness of left adjoints.

For step 4, the shift-compatibility uniqueness statement supplies the unit/counit-compatible right-adjoint shift structure. I checked its hypotheses on both geometric adjunctions; inverse image and scalar restriction are termwise exact functors here. The tensor-constraint statement supplies signed symmetry and the resolving equality criterion for tensor/shift transformations. The coefficient in degree zero accounts for the absence of a hidden sign in e. Taking adjoints of the d shift square reduces it to the b square and the compatible counits; this explains the shift identification rather than just asserting transport.

For step 5, derived change of rings and the geometric operations supply exactness, restriction is exact in the ring-sheaf adjunction statement, and the first-variable projection node states both exactness of the normalized restricted functors and the shift equation in the K variable. I used the first-variable result, not the projection theorem in its other variable. The connecting square is written explicitly using naturality at w and the shift equality. The triangulated-category definition states what exactness and a distinguished triangle mean; it is not being used as a replacement for a triangle-isomorphism theorem.

Step 6 uses conservativity exactly as stated in the ring-sheaf adjunction node. The zero, conjugation, positive and negative shift, and diagonal biproduct arguments are short consequences of steps 3–5 and the cited exactness. They are marked elementary and do not become redundant new nodes. Step 7 cites `lem-sf-triangle-morphism-iso`: its statement really requires all three squares, which step 5 has provided, and distinguished source and target triangles, supplied by exactness. Restriction conservativity then returns the conclusion to the B-derived category. Step 8 writes both products of the proposed inverse using the two naturality equations. It requires a given retract, not a general existence theorem splitting every idempotent.

I checked the delivery-errors B–E against the actual node statements and sources. Every non-elementary ingredient is a cited existing node; no source tag stands in for a DAG citation. No citation takes data from another node's proof. All eight steps are below 2000 characters; the comparison calculations are explicit and hide no appeal to a standard comparison lemma. Every step's uses occur in proof_deps, and citations.json quotes the exact statements. I checked the small cases K=0, the identity f, identity coefficient change, the zero target ring, an arbitrary shift, finite sums including the empty sum, and a nontrivial split retract. In particular A=Z to B=Z/2 illustrates why the proof must allow a nonflat coefficient map; no flatness or invertibility of the projection formula is used. Zero coefficients cause no failure: both scalar-extension outputs are zero. The ordinary unbounded derived categories and their small-site universe hypotheses agree throughout; no completed category or finite Tor restriction is introduced.

Generic categorical and ring-sheaf tools outside the unit are declared in split_report.tool_uses. They supply the normalization, adjunction, tensor localization, shift and triangle facts needed within the unit's existing route, rather than replacing its finiteness argument. Before delivery the server review_split check passed, reporting no new nodes and only the pre-existing absence of a realization for the unit. The final deliver.py dry run will run all required preflight checks before the push.

## Not duplicates

No new nodes. Reused the existing general ring-sheaf, localization, adjunction, projection and triangle-isomorphism nodes; nearby constant/condensed coefficient specializations are discussed above.

## Unfinished work

None at stage 1. This delivery writes no Lean and runs no compiler, Lake or build command. Downstream proof obligations remain with the existing dependency nodes.
