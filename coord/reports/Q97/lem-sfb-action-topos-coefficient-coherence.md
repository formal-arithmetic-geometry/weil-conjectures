# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-action-topos-coefficient-coherence.json: statement, split into eight steps, unchanged statement; not a Mathlib leaf.
- citations.json: verbatim statement excerpts for every step/node pair.
- searches.jsonl: actual searches performed by the required search wrapper.

No new nodes and no Mathlib leaves were created. No Lean was written or compiled. The repository and launcher were read only. The sandbox initially contained only dispatcher markers; there was no previous split, report, search log or running delivery to reuse.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, internal-action/classifying-topos terminology, normalized invariants and coefficient coherence. No declaration there states all clauses of this item. General coefficientMap_comp and scheme coefficient-coherence results concern other categories and do not attach this item.

## WANTED

WANTED: exact non-SGA reference for the internal condensed-action coefficient/inflation normalization, for lem-sfb-action-topos-coefficient-coherence. The current blueprint paragraph (3) supplies the application context rather than this lemma. The proof is explicitly agent-formulated from the existing normalized-action statements and the ringed-topos theorem below; no source was downloaded.

## Findings and changes

The live item was unsplit, with no proof. I retained its statement and existing ancestry, including the null blueprint ancestor returned by tools/blueprint_refs.py ancestor. The whole-blueprint searches for ringed topos composition and scalar restriction returned no equivalent imported blueprint statement. The DAG search found the general ringed composition theorem, its cocycle theorem, the restriction-of-scalars ringed morphism and normalized action comparisons. They suffice; introducing copies would duplicate nodes or just repackage clauses of this item.

The important distinction is between exact scalar restriction and preservation of K-injectives. The latter is not assumed. For an A'-K-injective I', the potentially non-K-injective sI' is replaced by J over A. Ringed composition proves f_*(a) is a quasi-isomorphism, giving theta inverse, rather than theta. After quotient invariants, T(a) is a quasi-isomorphism by that same theorem; it is then a legitimate resolution for the second full-invariant projection because T(J) is K-injective. This addresses the possible hidden acyclicity gap in a naive coefficient argument.

Tool uses outside the item's unit are declared in split_report.tool_uses: general ringed-topos composition, its cocycle, scalar restriction as direct image, and K-injective derived-map computation. These are categorical tools, not replacements for the blueprint's direct-image constructibility route.

## Mathlib searches

The searches actually run are in searches.jsonl and appended to mathlib_searches with exactly the logged tool and query. LeanFinder was tried with two different descriptions. LeanSearch returned ordinary representation invariants and continuous topological-module invariants. Loogle returned rightDerivedNatTrans_comp and abstract localization comparison results. Read Mathlib/CategoryTheory/Functor/Derived/RightDerived.lean around lines 110-138: this is abstract derivation of natural transformations, and supplies neither internal condensed actions nor the normalized coefficient/inflation assertion. The grep found SheafOfModules.pushforwardComp (PushforwardContinuous.lean:139) and restrictScalars (ChangeOfRings.lean:36). Read lines 125-155 and 25-52 respectively: these are underived sheaf-module constructions, not the item's derived theorem. Constant-ring CondensedMod constructors returned by the second semantic query likewise do not state the result for internal condensed rings. Therefore no exact or one-line Mathlib specialization covers the item.

## Not duplicates

No new nodes. Existing lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lem-pur-ringed-derived-composition-cocycle and the normalized action-model nodes are cited directly. The additional nodes found for diagram coefficient restriction and global sections are less suitable specializations of the same generic composition tool, so neither was copied.

## Review by Q97

I read the current blueprint direct-images proof paragraph (3), the recorded chapter and unit, the item, every cited node's statement, and literature/stacks-project/sites-cohomology.tex, label lemma-derived-pushforward-composition, Tag 0D6E (verified in tags/tags). Its hypotheses are arbitrary morphisms of ringed topoi and unbounded derived categories; its proof derives composition by the derived adjunction and uniqueness of adjoints. There is no flatness hypothesis. The item's internal-action realization and resolution normalizations are extra agent-formulated infrastructure, so I did not attribute them verbatim to Stacks and marked proof_origin as agent. The source also does not justify an SGA trace route, and none is used. There are no new statements whose sources or hypotheses need separate review.

Step 1 uses the actual action-topos theorem for the internal sheaf of groups, not the ordinary abstract-group special case of a classifying topos. Its statement includes the precise action-site restriction and coefficient squares. The internal-action-site node provides the module equivalence. The open-normal-model node states the quotient adjunction and identities. The elementary identification of a map out of a trivial action with a map into fixed sections proves that the direct image is the required invariant functor. The quotient projection uses K normal and open, exactly as in the model node; no arbitrary quotient lifting is assumed.

Step 2 uses the ringed scalar-restriction theorem for its actual direct-image assertion, the action-calculus statement for exactness of s, and the exact-functor Mathlib leaf for termwise derivation. The action-topos theorem states equality of the structural ring squares as well as equality on sheaves. Thus the two factorizations used in step 3 are the same ringed morphism, not merely equal underlying functors.

Step 3 applies the full ringed composition theorem, whose statement explicitly gives quasi-isomorphism of g_*(j) for a K-injective input and replacement after the first direct image. Here its first morphism is the coefficient morphism, its second is the projection, and j=a. I checked this order to obtain theta inverse. The other factor is computed with the identity replacement of f_*(I'), justified by the open-normal-model statement's K-injective preservation for T and full invariants. Exactness of scalar restriction does not enter as an injective-preservation assertion.

Step 4 uses the statement of the cocycle node, including its final clause about coefficient morphisms on identity underlying topoi and its unit laws. The argument cancels adjacent inverse composition comparisons in the same common ringed composite. Thus its coefficient composition claim is supported by an actual theorem, not by a definition of derived composition.

Step 5 uses the open-normal-model statement for exact r, K-injective preservation, UT=Gamma_K r and beta's identity on invariant complexes. The action calculus supplies exact scalar restriction and the unchanged underlying fixed sections. Applying step 3 to rI' and the resolution r(a) is allowed since r is exact and preserves K-injectives. Both routes really are the same map (ra)^K.

Step 6 checks that T(a) is a quasi-isomorphism by step 3 before treating it as a resolution; applying a left-exact functor to an arbitrary quasi-isomorphism would be invalid. The open-normal-model statement supplies K-injectivity of both quotient-invariant targets. The inflation-resolution node's statement gives c as the identity on I^(G times L)=(TI)^(Q times L) and identifies it with the conjugate normalization. The two maps Gamma_G(a) and Gamma_Q(T(a)) agree section by section, including residual quotient action.

Step 7 uses the inflation-resolution statement's actual unit representative T(i) and its equation c inf=R Gamma_Q(eta). The written equality T(a) sT(i')=T(a s(i')) verifies the scalar square of the computation unit. The inclusion equality a iota=iota Inf(Ta) verifies the representative normalization for inflation, in addition to proving the derived square from the displayed equation. The only module restriction is the degree-zero domain of eta and inflation stipulated by the item.

Step 8 uses the full-derived naturality clauses of the open-normal and inflation-resolution statements, then the scalar-interchange statement for the identification with the prescribed c_J. The K-injective map-computation theorem states compatibility with composition and transitions of resolutions for arbitrary derived morphisms; it justifies using these representative equalities without imposing a choice of resolution on v. I checked every proof citation against its statement and recorded the relevant verbatim part in citations.json. No step uses a construction hidden only in a cited proof.

I checked B--E of delivery-errors: statements retained, all objects introduced, no new definition or unsearched leaf, no new-node restatement, no dependency cycle through the generic tools, and no missing non-elementary invariant/exactness claim. All non-elementary steps are below 1000 characters, and the small inline equalities are composition, functoriality or equality of fixed-section subsets, not hidden independent comparisons. Edge cases: trivial groups and K=1 make the invariant maps identities; K=G (when allowed by openness) gives the full-invariant specialization; zero complexes give zero maps; identity coefficient maps give identity comparisons by the cocycle unit; arbitrary non-flat coefficient maps are admitted because a is resolved over A and f_*(a) is justified by ringed composition. None of these tests requires preservation of K-injectives by scalar restriction. I corrected no mathematical statement; the repairs made while writing were the orientation of theta and the explicit intermediate-resolution check for c.

## Unfinished work

None for this one-level split. Generic and action-specific dependency nodes remain the existing DAG's work, rather than new duplicates. The required server dry run and delivery follow this review.
