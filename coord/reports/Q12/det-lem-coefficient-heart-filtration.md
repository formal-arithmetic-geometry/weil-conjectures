# Worker report: det-lem-coefficient-heart-filtration

## Files written

- dag/nodes/sec-six-functors-basics/det-lem-coefficient-heart-filtration.json: retained repair, split; statement unchanged against current live repository.
- dag/nodes/sec-six-functors-basics/lem-sfb-subobject-inclusion-cokernel.json: new statement-only comparison of the cokernel of the chosen subobject inclusion with that of a map between monomorphism sources; status unsplit, no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-image-subobject-of-monomorphism.json: new Mathlib leaf, CategoryTheory.Limits.imageSubobject_mono, Mathlib/CategoryTheory/Subobject/Limits.lean:425.
- citations.json: regenerated from the actual current statements, covering every step/node pair.
- searches.jsonl: retained previous worker's logged searches; results read before reuse.

## Attachments

CategoryTheory.Subobject.cokernelOfLEMkIso belongs to lem-sfb-subobject-inclusion-cokernel; lean/WeilConjectures/ConstructibleSheaf/Devissage.lean:56. Its definition is sorry-free and assumes only zero morphisms and cokernels, so specializes to the abelian category in the node. The maintainer's closure check must verify dependencies. The new node remains statement-only as requested for this delivery.

The item itself is not an attachment: AlgebraicGeometry.ProEtale.coefficientHeart_filtration in lean/Sheaf/Paper/CoefficientHeartFiltration.lean:113 ends with sorry. Upstream Devissage is for ordinary etale finite locally constant modules, not the E/Qlb pro-etale coefficient categories in this item.

## Wanted

None.

## Repair and comparison with current live

The live item has already adopted the Q33 repair, citing the existing open-filtration-successor and locally-closed-extension-coherence. The human's deliberate re-split note still requires a new argument node. This delivery retains the interrupted Q12 work and adds the generic representative-change argument, rather than duplicating either existing geometric theorem. The main statement, statement dependencies, coefficient categories, and closure factorization are unchanged. The previous sandbox had no report.md and stale citations for the image node, and the new statements contained doubled TeX backslashes; these are corrected here. Existing searches and their real results have been retained, not reconstructed or repeated.

The quotient comparison is not the target or one of its geometric clauses: it concerns arbitrary monomorphisms in any abelian category, with an optional isomorphic replacement of the first source. It removes the genuine issue that a cokernel of d between extension objects is not definitionally the cokernel of Subobject.ofLE between chosen representatives. Its argument is change of representatives by the underlying isomorphisms, cancellation against the second monomorphism to identify the resulting arrow, then cokernel invariance under isomorphisms. The separate Mathlib leaf identifies each image subobject with the subobject represented by its monic counit.

## Not duplicates

lem-sfb-subobject-inclusion-cokernel vs lem-sfb-open-filtration-successor: the existing node supplies a natural transformation between open-extension objects and its functor cokernel; it says nothing about chosen representatives of their image subobjects or Subobject.ofLE.
lem-sfb-subobject-inclusion-cokernel vs lem-sfb-locally-closed-extension-coherence: factorization-independent geometric extension functors do not compare cokernels of represented subobjects.
lem-sfb-image-subobject-of-monomorphism vs lem-sfb-subobject-inclusion-cokernel: the former identifies one image subobject with its monomorphism class; the latter compares the cokernel of a map between two chosen representatives. No shared Stacks tag is introduced by these new nodes. Whole-DAG keyword/declaration searches and whole-blueprint searches for cokernel subobject and image subobject found no node stating either fact.

## Review by Q12

I read the current main-20261015 filtration statement and both paragraphs of its proof, the coefficient-heart unit and six-functors-basics chapter. The route is still successive open localization followed by the mixed locally closed factorization comparison. I read every cited node's statement. I read the new comparison's mathematical realization at Devissage.lean:54-66 and the exact Mathlib image statement at Subobject/Limits.lean:425; neither new node contains proof steps or a proof sketch in its statement. The source for both new nodes is the precise passage from counit objects to subsheaves and their quotients in the filtration proof. These are agent-extracted arguments, not assertions falsely attributed to a Stacks tag.

Step 1 takes the untwisted coefficient-ring isomorphism from cartesian-coefficients (1), not the Tate-twist clause, so no invertibility of ell is needed. The Noetherian-open node explicitly gives both locally Noetherian and quasi-compact; the locally-Noetherian quasi-separated node supplies quasi-separatedness. An affine inverse image for an inclusion of these opens is an open of a Noetherian scheme; hence it is quasi-compact. Open-immersion diagonals are isomorphisms. This checks the hypotheses for both localization and the nested-open successor theorem.

Step 2 uses precisely localization (3), whose map is explicitly the adjunction counit, to obtain monomorphisms. The successor statement explicitly supplies the composite counit identity. Cancellation then gives monicity and the subobject inequality. At the empty open the module category is the zero category, so its left adjoint sends the zero object to zero; at the whole open the counit is the identity up to the identity-open adjunction. This verifies both endpoints without a strict-inclusion assumption.

Step 3 uses the successor's stated cokernel, with S_k the closed stratum in V_k, and its specified natural map d. The image leaf explicitly gives imSub(epsilon)=[epsilon]. The new quotient-comparison statement explicitly allows alpha=1 and phi=d and requires f=g composed with phi composed with alpha; this is exactly the successor counit identity. Thus it applies to the actual Subobject.ofLE cokernel, not an arbitrary mono with the same endpoints. Both counits are monic by step 2. Module sheaves form the ambient abelian category already used by localization. Restriction composition identifies c^*v_k^*F with F restricted to S_k.

Step 4 takes the precise sentence in locally-closed-extension-coherence comparing a=v_k c with a=i u, giving v_k! c_* isomorphic to i_* u_!. Its Noetherian and commutative ring-sheaf hypotheses hold; step 1 supplies its pulled-back rings. No equality of functors is asserted from support alone. Step 5 takes the finite constant local-model/finite free characterization in the closure node, so adaptedness gives lisseness for the specified coefficient fields. Every citation has a verbatim entry in citations.json.

For the new generic cokernel statement I checked alpha's direction A to A', the equality f=g phi alpha, and the chosen representative arrows. The comparison is valid also for zero objects, f=g, phi an isomorphism, and a proper strict subobject; in f=g, alpha=1, phi=1 the cokernels on both sides are zero. For the image leaf the monomorphism hypothesis is indispensable and stated. I checked F=0, X empty, repeated/empty strata, the first step W empty, m=1, and nonreduced closed strata in the item. These require no strictness, reducedness, or nonzero-rank hypothesis. All non-elementary geometric arguments in the old proof remain in the existing successor/localization/coherence nodes; the missing representative-change argument now has its own new node. No step exceeds 2000 characters and the assembly is below 3000 characters. No Lean was written, compiled, or built.

## Unfinished

None in the stage-1 delivery; new statement-only nodes deliberately have no proof steps. Delivery validation follows below.
