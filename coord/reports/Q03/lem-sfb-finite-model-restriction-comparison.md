# Stage-1 report: lem-sfb-finite-model-restriction-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-model-restriction-comparison.json`: statement, split; eight proof steps, using existing nodes only. Mathlib verdict: no exact match or one-line specialization.
- `citations.json`: one verbatim statement quotation for each of the fifteen step citations.
- `report.md`: this report. `searches.jsonl` is the unmodified output log of the prescribed search command.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, finiteModelRestriction, finite_model_restriction, finite exact cochain and finite cochain model, then the category-theory and homology source for the finite-cochain and restriction-comparison concepts. The hits describe other tensor, sheaf or scalar comparisons; no project declaration supplies this statement, its finite-model hypotheses, and every normalization clause.

## WANTED

None. All sources used are available in the read repository.

## What was wrong or incomplete

The item had no proof. Its statement is retained verbatim, including the orientation of gamma, the inverses in alpha, its unit normalization, and the absence of injective preservation by U. Its existing statement dependencies are retained. There is no statement dispute.

The essential issue is that UJ need not consist of injectives. The proof does not apply the finite-model lemma to UJ as an injective resolution. It instead uses the existing finite-strip augmentation theorem to prove G(UJ) to Tot F(UJ) is a quasi-isomorphism, using theta and V(e'_J) on each row. The other axis augmentation is a quasi-isomorphism because it is identified with V(c'_t) by theta. The two explicit squares with Tot F(beta) then prove G(beta) is a quasi-isomorphism.

The blueprint source is its current main-20261015 paragraph (3), the algebraic tool below the tame-boundary coefficient calculation, rather than a theorem claiming that arbitrary restriction preserves injectives. Its nearest-ancestor command reports `blueprint.from.node = None`; this is already the item's metadata, and I retained it and its full via chain instead of inventing an ancestor. The unit is not this item's key statement, so no realized fields were changed.

## What could not be finished

Nothing in the mathematical split remains. Delivery validation is run after this report is written.

## Not duplicates

No new nodes were created. Searches of existing nodes for Tags 013P and 0133 and for lift, homotopy, exact-functor homology, finite-strip augmentation and finite cochain models found the statements needed. In particular I reused lem-weil-pbc-lift-along-injective-quasi-iso, lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, lem-weil-pbc-exact-functor-complex-cohomology, lem-sc-finite-strip-row-augmentation and lem-sfb-finite-exact-complex-derived-model. The general injective-resolution lift node is too narrow for UJ, which is why the lift-along-monic-quasi-isomorphism node is used. The finite-row comparison node and the finite-strip cone-filtration node are unnecessary once the two axis augmentations have been identified. Blueprint searches for `restriction comparison` and `cochain model` returned zero matches.

## Mathlib searches

Retained the item's five existing 2026-10-22 search records. Added only the six actual 2026-10-23 msearch invocations in searches.jsonl: LeanFinder in two phrasings, Loogle for `"rightDerived", "comp"`, LeanSearch for the finite-complex restriction comparison, and two source regex searches. All six services returned successfully. Read every returned hit. Read Mathlib/CategoryTheory/Localization/DerivabilityStructure/PointwiseRightDerived.lean, in particular the comparison definition at line 64 and the additional IsRightDerivabilityStructure hypothesis at line 88 before the invertibility instance. Also read the termwise exact-functor localization comparisons in Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean. Those results give infrastructure, but not this statement as a one-line specialization: the finite-model argument proving the restricted-resolution comparison invertible is still needed. The resolution-map formulas returned by both semantic searches concern a single derived functor, not this comparison between two categories with non-injective UJ.

## Review by Q03

I read the item, its chapter and unit, the current direct-images blueprint proof paragraph (3), and the existing normalized finite-exact-complex model statement. I checked its algebraic application against Stacks homology.tex, Tag 0133 (lemma-double-complex-gives-resolution), including the second-variable variant and the finite-diagonal hypothesis. For the resolution maps I read derived.tex Tags 013P (lemma-morphisms-lift) and 013S (lemma-morphisms-equal-up-to-homotopy), and for the normalization I read the right-derived section Tag 0156 and Tag 05TH (lemma-injective-acyclic). I also read homology.tex Tag 010N (lemma-exact-functor). The proof is marked agent-written: the blueprint specifies the coefficient-comparison use, and the displayed total-complex and unit equations are my assembly of these existing ingredients. No SGA source was used.

Step 1 uses exactly the cohomology comparison of lem-weil-pbc-exact-functor-complex-cohomology to show that Ut is a quasi-isomorphism. Its degree-zero monicity follows from the nonnegative resolution, and U preserves kernels by its exactness. I checked that lem-weil-pbc-lift-along-injective-quasi-iso assumes injectives only in its target I and allows a non-injective source UJ, so it gives strict beta Ut = s. The uniqueness node likewise only requires a bounded-below injective target and a quasi-isomorphism Ut. Applying G to the displayed homotopy equation uses only additivity. The derived-category definition explicitly permits localization of the homotopy category, so it identifies the resulting maps.

Step 2 uses the statement, not the proof, of lem-sfb-finite-exact-complex-derived-model. It provides both axis quasi-isomorphisms for each genuine injective resolution and the precise normalized lambda formula. The double-complex definition provides the commuting-differential and total-sign convention. Both instances of the model lemma have their enough-injective and exact-degree hypotheses from the item. It is not applied to UJ here.

Step 3 is a component calculation from the finite total definition and supplied natural isomorphisms. I checked both differential directions: theta commutes with d_F because it is an isomorphism of complexes, and with d_J by naturality. Additive V commutes with each finite biproduct by the explicit inclusion/projection maps. This needs no infinite coproduct preservation. The augmentation identity is used on the a = 0 axis; naturality on Ut is used on the b = 0 axis. Both signs are 1 there. These yield the literal equations Theta b = V(b'_t) gamma_J and Theta c = V(c'_t) theta_X'.

Step 4 uses the exact-functor cohomology statement to preserve the quasi-isomorphisms e'_J and c'_t under V. The statement of lem-sc-finite-strip-row-augmentation gives the quasi-isomorphism of b from precisely these row quasi-isomorphisms, without any vertical boundedness or injectivity hypothesis. Its strict bound is p < r+1, not p < r; I used parameter r+1. Negative resolution degrees are zero, and there are only finitely many diagonal terms in every degree. The normalized-model statement supplies c'_t; the equation from step 3 then proves c is a quasi-isomorphism. No term UJ^b is assumed injective.

Step 5 writes both squares for k rather than saying that a comparison merely transports them. Their equations follow componentwise from naturality of e and beta Ut = s. Applying cohomology to kc = c_s and kb = b_s G(beta) proves all necessary inverses by cancellation of isomorphisms; no extra comparison theorem is hidden. The derived-category definition supplies the localization. Step 6 substitutes those two equalities, the two equations with Theta, and the exact lambda formulas from the existing normalized-model statement. I checked the right-to-left order: alpha lambda = V(lambda') theta. This is an identity in the derived category, not only a per-degree claim.

Step 7 takes the resulting expression V(lambda') Q(theta) lambda^{-1}. The same existing model statement asserts independence and naturality of both lambdas, while theta is natural by hypothesis. Thus this expression establishes all choice independence and the naturality square for alpha. Step 8 uses the unit natural transformation of def-sfb-right-derived-functor and the stipulated normalized resolution comparison. I checked the cancellation using s = beta Ut, and obtained alpha^{-1} = RG(Q(Ut))^{-1} eta_UJ Q(gamma_J)^{-1} D(V)(rho'_t). Every factor is typed in that order, and this is the precise unit comparison claimed. Its identification does not infer uniqueness from agreement on degree-zero objects alone.

I tested the split at r = 0, at X' = 0, with identity functors, and in a case where U actually fails to preserve injectives. For the latter take A' to be F_2-vector spaces, A = B = B' = abelian groups, U the forgetful functor, V = identity, G = identity, G' = U, F = G[0] and F' = G'[0], with identity augmentations and comparisons. The vector-space object F_2 is injective in A' while its underlying group is not injective. The construction nevertheless has b an identity, c a quasi-isomorphism, and beta an ordinary group-resolution augmentation, as required. At r = 0 the strip parameter is 1 and includes the sole nonzero column. Zero objects create no missing diagonal summands or undefined inverses in the derived category.

Against delivery-errors B-E: there are no new unsplit nodes, invented notions, duplicate nodes or new leaves to audit; TeX has single escaped mathematical commands in the parsed strings. Every non-elementary input is an existing statement whose required sentence was copied to citations.json and checked as an exact substring. The proof does not cite another node's proof or move an item clause into a child. The only off-unit non-leaf tools requested in split_report.tool_uses are the generic finite-strip augmentation and homotopy-uniqueness results; neither replaces the unit's geometric route. Every step is shorter than 2000 characters. I corrected the tempting but invalid use of the injective-model theorem on UJ by using the finite-strip theorem there instead. No source statement, target statement or definition was changed.
