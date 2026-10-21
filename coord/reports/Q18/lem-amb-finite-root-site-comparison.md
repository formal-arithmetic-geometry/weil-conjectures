# Q18 stage-1 delivery: lem-amb-finite-root-site-comparison

## Files written

- dag/nodes/sec-smooth-purity/lem-amb-finite-root-site-comparison.json: statement, split into six proof steps; no Mathlib match for the complete statement.
- citations.json: one verbatim statement quotation for every proof-step citation.
- report.md: worker report and self-review.

New nodes: 0. New Mathlib leaves: 0. The sandbox was initially empty of node files, reports and search logs. I retained the item's statement, statement dependencies, blueprint provenance and inherited Mathlib searches, and appended the five searches actually performed by Q18. searches.jsonl holds their tool-produced results. write_split.py and finalize.py are sandbox-only preparation scripts.

## Attachments

None. I searched the project's WeilConjectures sources for the exact blueprint id and for roots-of-unity, comparison and pullback names. The id has no declaration. I read TateTwist/RootsOfUnity.lean and the relevant docstrings/statements in EtaleCohomology/TateTwist/RootsOfUnityPullback.lean and FiniteKummerLevelBaseChange.lean. Their etale-root pullback and etale finite-tensor base-change statements do not state the pro-etale comparison on all weakly etale tests or its full collection of coherence equations. They are not an attachment for this item.

## WANTED

None: the source needed here is available in literature/stacks-project/.

## Audit of the imported item and route

The statement is unchanged. It is well typed with m >= 1, mA = 0, and m invertible on T; invertibility pulls back to every test and every T'. In particular the scheme map is arbitrary, not merely an isomorphism. The existing root inverse-image isomorphism node proves invertibility only for scheme isomorphisms, so I did not use it for that stronger conclusion. Instead the commuting square and the etale root pullback prove invertibility of d for arbitrary scheme maps.

The imported item had no proof. I filled that gap using existing DAG statements; no statement dispute or change to the chapter/unit route was needed. I read the smooth-purity chapter, the sk-prop-an unit record, and the current main-20261015 vector-bundle theorem and proof. This item realizes the finite Tate coefficient in the integration formula, not vector-bundle purity itself. It is not the key node of its unit, so I did not edit the unit's realized fields.

I searched the whole DAG by 0GLZ, 03EL, roots, tensor inverse image and comparison/pullback terminology, and searched the whole imported blueprint with blueprint_refs.py for roots of unity, finite root, site comparison and tensor product pullback. The general section-comparison node and the generic normalized tensor node already provide the non-elementary tools, so none was recreated. No blueprint node states this entire package in another form; blueprint.same_as remains empty. The existing lem-pur-finite-kummer-level includes additional coefficient and ramification restrictions and is not an exact attachment or a replacement for the arbitrary m/A statement here.

The Mathlib search services all answered. LeanFinder's first phrasing returned ring roots and cyclotomic-character facts; the second returned definitions and full-faithfulness of the etale site. LeanSearch returned etale algebra and ring-theoretic Kummer facts; Loogle returned zero hits. The Mathlib grep located Sites/Proetale.lean and ElladicCohomology.lean, whose relevant sections I read: they define the topology and coefficient objects, rather than this comparison theorem. Thus none gives the complete item or a one-line specialization. The exact query texts and actual logged summaries, including directories, are preserved in mathlib_searches.

## Unfinished work

None for this one-level split. The dependencies remain their own DAG items. No Lean was written and no compiler, Lake or build tool was run.

## Not duplicates

No new nodes were created. The section-comparison, normalized inverse-image tensor, torsion-module and bilinear-universality results are cited under their existing ids. In particular I did not create a root-comparison clause as a purported smaller replacement for this item.

## Review by Q18

I read Stacks proetale.tex, Tag 0GLZ (lemma-describe-pullback-from-etale), including its section formula, restriction argument and adjunction construction, and sites-modules.tex, Tag 03EL (lemma-tensor-product-pullback), including its Hom/bilinear proof. The proof is marked agent-written because it combines these general results with the root normalizations and explicit compatibility calculations; it is not a claim that Stacks states the complete package verbatim. There are no new nodes whose separate source needs checking.

For step 1 I opened the full statements of lem-cbc-comparison-pullback-sections, lem-asd-etale-finite-twist-pullback, def-pur-roots-of-unity-sheaf and lem-pur-torsion-sheaf-constant-module. The first really identifies inverse image with etale terminal sections on every weakly etale test, rather than just constructing an unrelated functor. The second really gives root pullback for any scheme map with invertible exponent, and its composition compatibility. Their combination gives the actual units on W and their restrictions. The root definition specifies the same functor and its m-torsion; the torsion-module theorem gives linearity for every abelian-sheaf map. No affine, Noetherian, finite-type or connectedness hypothesis is introduced.

For step 2 the same section-comparison statement explicitly specifies the comparison adjunction unit on etale objects and naturality in the coefficient sheaf. The root definition specifies the power transition. Restricting that unit along W -> U gives f-sharp(z), and pullback of units commutes with powers as a ring-homomorphism identity. This is a direct calculation from the cited statements, not an assertion that the unit formula follows just from an abstract isomorphism.

For step 3 I checked def-weil-pbc-site-comparison-morphism, def-weil-pbc-algebraic-inverse-image, lem-weil-pbc-algebraic-inverse-image-tensor-comparison and clause (1) of lem-sf-comparison-pullback-exact. The comparison is a geometric inverse image with finite products, and the algebraic presentation transports ring and module operations exactly as required by the tensor theorem. That theorem supplies an isomorphism with a generalized pure-tensor equation; the exactness node identifies constant rings and module inverse image, not a derived coefficient object. Both coefficient rings Z/m and A are finite and commutative. The A-action is on the second factor, and naturality in its multiplication proves A-linearity. This uses no flatness of A over Z/m.

For step 4 I checked the statements of lem-weil-pbc-comparison-pullback, both inverse-image definitions used there, def-weil-pbc-composite-adjunction, lem-weil-pbc-conjugate-iso-unit-equation and def-pur-roots-of-unity-inverse-image. The comparison-pullback node is written in the reverse orientation to kappa in this item; the proof explicitly uses its inverse. I did not take a unit-normalization theorem from that node's proof: the separate conjugate-unit theorem supplies precisely that equation, and the composite-adjunction definition supplies the composite unit. The right direct images evaluate on the same scheme T' x_T U with the same restrictions. Both root-square adjuncts therefore send z to the same projected unit. The pro-etale root map is exactly the adjoint prescribed in its definition, rather than an independently chosen isomorphism.

For step 5 I opened prop-weil-pbc-proetale-constant-ring-map, the normalized tensor-comparison statement, def-weil-pbc-constant-sheaf, lem-pc-sites-sheaf-tensor-bilinear-universal and the composite-adjunction statement. The constant-ring theorem applies to arbitrary scheme maps and preserves constant sections; it includes the empty scheme. The tensor theorem covers all geometric inverse images after transporting module operations. The bilinear universal property really tests morphisms out of a sheaf tensor, not merely objectwise presheaf tensors. I compare adjuncts on the etale site, where their common source is E, and only then use that test. Thus the proof does not assume that every pro-etale section is a pullback from one etale object or that all sheaf tensors are globally pure. Local scalar sections are covered by the constant-sheaf construction. The displayed equation gives invertibility of d because all other factors are already isomorphisms.

For step 6 the identity/composition clauses are explicitly in the etale finite-twist and comparison-pullback statements, and the root definition really specifies the exponent transition. I wrote the maps on root/scalar tensors: iterated scheme pullback is pullback of the same unit, and the exponent map is semilinear for Z/m' -> Z/m. Equality on tensor maps is justified by the same bilinear universal property. This is an elementary assembly of earlier steps, not an omitted compatibility lemma. All six steps are below 2000 characters and none hides a separate comparison theorem.

I tested m=1 (necessarily A=0), A=0 for any m, the empty scheme, a disconnected scheme with nonconstant locally constant scalars, m=m', and m=2,m'=4,A=Z/2. The power arrow has the right direction z -> z^2 and is balanced over the reduced scalar ring. I also checked an arbitrary non-etale scheme map: only its induced etale inverse image and root pullback are used, so no illicit assumption that the scheme map is a site object occurs. A non-affine weakly etale test is allowed throughout by 0GLZ. No primitive root is chosen, and no limit or flatness claim is needed.

Against delivery-errors B--E: there are no new unsplit nodes, duplicate nodes, Mathlib leaves or clause relabellings. Every non-elementary tool is an existing cited statement, with a verbatim quote in citations.json; proof_deps is exactly the union of uses. I traversed the proposed dependencies and none reaches this item, so the citations introduce no cycle. Off-unit generic tools are declared in split_report.tool_uses with their purpose. No SGA source is used. The substantive addition is the complete proof of the existing item, and the statement and all hypotheses remain intact.
