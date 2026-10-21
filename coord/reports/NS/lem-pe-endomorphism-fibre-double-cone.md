# Worker report: lem-pe-endomorphism-fibre-double-cone

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-pe-endomorphism-fibre-double-cone.json`: statement, now split into six explicit elementary matrix calculations; no exact Mathlib match.
- `citations.json`: a verbatim statement quotation for both definition nodes cited in each of the six steps.
- `report.md`: this report. The prescribed search tool maintains `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. The item's statement, source, chapter, unit, creation record and blueprint ancestry are unchanged. The original Mathlib search records are retained and the five searches actually run in this session are appended.

## Attachments

None. I searched the current `lean/WeilConjectures/` for the exact blueprint id and for double cones, mapping fibres and endomorphism fibres. No declaration states the whole item. The cone diagram and unrotation results concern other configurations; they do not provide this endomorphism-fibre comparison with its specified augmentation identity. No Lean was written or compiled.

## WANTED

None. All sources used are present locally.

## What was wrong or incomplete

The imported item had a precise statement but an empty proof. The blueprint's Cones paragraph asserts that the fibre construction commutes with mapping cones and that canonical maps give a morphism of triangles, without the component checks. This split supplies those checks, including the minus sign on the fourth coordinate and the negative cone boundaries. I found no statement dispute or route error. The coordinate notation is explicitly interpreted as biproduct morphism matrices, so it does not assume that an arbitrary abelian category is concrete.

The proof is recorded as agent-written: the blueprint supplies the required assertion and Stacks supplies the definitions and sign conventions, rather than an existing proof of this exact double-cone formula. No assertion about exactness of products, a derived limit, or localization is used here. Those belong to the parent Roos argument.

## Source reading and searches

I read `GOAL.md`, the worker and stage-1 rules, the three blueprint levels in `SETUP.md`, both copies of delivery-errors B--E, the item's chapter and unit, and the current main-20261015 first-reduction proof. The latter's Cones paragraph is the exact blueprint place served by this item. This item is not the unit's key statement, so no unit realization fields were changed.

For signs I read `literature/stacks-project/derived.tex`, Tag 014E, `definition-cone`, and Tag 014Q, `definition-distinguished-triangle`, including the following paragraph specifying the distinguished cone triangle with boundary minus the projection. I also read `homology.tex`, Tag 011G, `definition-shift-cochain`, including its action on morphisms. The tag-to-label mapping was checked in `tags/tags`.

Before considering extra nodes I searched the DAG by these tags and by double-cone and endomorphism-fibre terminology, and used `tools/blueprint_refs.py search` for `double cone`, `mapping cone` and `endomorphism`, as well as `ancestor` for this item. I read the statements of `lem-pe-endomorphism-fibre-coordinate-calculus`, `lem-amb-signed-fibre-cone`, `lem-amb-signed-fibre-shift`, `lem-amb-signed-fibre-complex`, and `lem-pe-roos-cone-calculus`. The coordinate-calculus sibling is unnecessary as a dependency because the small well-definedness and shift computations needed here are written out. The signed-fibre lemmas for additive functors into Ab do not state this general endomorphism-fibre assertion for arbitrary abelian categories. The Roos node is the parent and cannot be cited without a cycle.

The five new Mathlib queries are recorded exactly as issued by the prescribed msearch command: grep, Loogle, LeanSearch and two differently phrased LeanFinder queries. All services answered successfully. I read the candidate source in `MappingCocone.lean` lines 29--65 and 209--242, `MappingCone.lean` lines 590--655, `Pretriangulated.lean` lines 418--468, and `Triangulated.lean` lines 34--90. The additive-functor cone comparison applies a functor to objects degreewise; this fibre mixes adjacent degrees and depends on a chain endomorphism. The composable-cone comparison is a homotopy equivalence for a different diagram. Neither specializes in one line to all clauses of this item.

## Not duplicates

No new node is created, so there are no new/existing pairs to justify. Existing signed-fibre and coordinate-calculus nodes were read as described above; no result has been recreated as a subordinate node.

## Review by NS

I checked the source and every cited node's actual statement with the node files open. `def-sp-abelian` explicitly supplies preadditivity and finite biproducts, which justify interpreting the formulas as finite biproduct component morphisms and distributing composition over sums and negatives. `def-weil-abstract-derived-category` explicitly defines integer cochain complexes, chain maps, the shifted differential, the cone differential, the inclusion, projection and the negative cone boundary. These are the only mathematical inputs besides the item's hypotheses. Both are already Mathlib leaves. Full verbatim quotations are supplied in `citations.json`; no use relies on a cited node's proof or on a stronger unstated lemma.

Step 1 uses those two definition statements to expand the reordered fibre differential, check its square is zero, and check diagonal maps are chain maps under the intertwining equation. The separate calculation for c uses exactly fs=tf and the facts that s,t,f are chain maps. It assumes no general exactness theorem. Step 2 substitutes the four coordinates into both explicit differentials: the second target component is -db'-tb-fa' and the fourth is -da'+sa on both sides. This is the crucial sign check and is written out, rather than citing a functorial cone theorem.

Step 3 uses only the same definitions and the result already proved in step 2. The two degreewise composites with the stated inverse are identities; multiplying the differential identity by the inverses proves that the inverse is a chain map. For naturality I checked all three required square equations: beta f equals f-tilde alpha, alpha intertwines s, and beta intertwines t. Both four-coordinate composites are displayed, so no naturality assertion is being imported from a source with weaker hypotheses.

Step 4 uses the shift and cone conventions from the derived-category definition and additive biproduct arithmetic from the abelian-category definition. I computed the differential on K(A[1]) and on K(A)[1] separately. The signed shift comparison intertwines them, and its square is the identity. I checked that the inclusion and minus projection intertwine the appropriate endomorphisms before applying K. The inclusion composites both give (b,b',0,0); the two boundary composites both give (-a,a'). In particular, omitting either the fourth-coordinate minus in Phi or the second-coordinate minus in sigma would fail this check.

Step 5 again uses only the definitions: the map eta is a chain map because rL=0, not because a general lifting or exactness lemma is assumed. I used sJ=0 and tJ'=0 for the two initial augmentations, fJ=J'g for their strict square, then computed the cone differential to check J_C is a chain map and cJ_C=0. These establish that the third augmentation is defined and is a chain map under precisely the stated hypotheses. Step 6 checks directly that the induced cone map is a chain map using that strict square, then evaluates both augmentation composites to (J'm',0,Jm,0). There is no omitted compatibility with a connecting morphism.

For small cases I checked zero complexes; f=0; s=t=0; degree-zero copies of Z with f=s=t the identity; and characteristic two. With zero endomorphisms the augmentation example J=J'=id and g=f satisfies all hypotheses, and the displayed augmentation equality remains literal. The degree-zero Z example with a'=1 tests the nontrivial sign: the source differential has third component -f(a'), and the target gets the same component from f(-a'). In characteristic two the negations become identities on both sides consistently. None of these checks requires boundedness. Every step has its entire component argument in the node, each is under 2000 characters, and no separate non-elementary subclaim is hidden in it. Thus B--E's checks need no new nodes or corrections to the statement.

## Unfinished work

None in the requested one-level split. The delivery is subject to the maintainer's independent review.
