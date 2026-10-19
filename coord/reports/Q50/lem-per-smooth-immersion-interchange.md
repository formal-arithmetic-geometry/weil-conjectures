# Q50: lem-per-smooth-immersion-interchange

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-smooth-immersion-interchange.json: statement item, now split into eight proof steps; not a Mathlib match.
- No new nodes and no new Mathlib leaves.
- citations.json records a verbatim statement quotation for every node used by every proof step. searches.jsonl is the actual msearch command log. The sandbox also retains the source PDF text extracts and working scripts; these are not delivery files.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 source for the exact blueprint tag, Gysin terminology, smooth/immersion interchange, and orientation terminology. The affine-line orientation declarations do not assert either of these two identities for general regular schemes. The item has no attached finished project declaration. No compiler was run.

## WANTED

None. Both cited PDFs and the current blueprint are present locally.

## Findings and corrections

The imported statement is retained verbatim. The item was unsplit, with an empty proof. Its original source has the two claimed identities in Expose XVI, Lemmas 2.5.7 and 2.5.8; Lemmas 2.5.9 and 2.5.10 give the affine and projective-line section normalization. I read the displayed identities, their proofs, the preceding product convention (Definition 2.5.6), and the regular-immersion product discussion. I also read Scholze's Theorem 7.19 and following discussion of the diagonal class and deformation identification, together with the statement and proof of the existing ordinary-smooth-orientation node.

I replaced the source's external smooth-trace input with the ordinary compact-support adjunction, its exceptional base-change mate, and the existing base-change-compatible diagonal/deformation orientation. Accordingly proof_origin is agent, with the source lemmas identified. The unit's route and all target statements are untouched. This node supports the regular Gysin normalization below the arbitrary-field duality in Step 3 of lem-per-artin-gabber-affine-curve; it is not a unit key node, so no unit record is changed.

During drafting I removed use of lem-per-regular-gysin-calculus: that is the parent whose proof needs these identities. Its composition theorem would conceal the argument and be circular. The final proof instead writes the supported-class naturality equation and its two adjunction transposes explicitly. I also removed an unnecessary derived tensor projection comparison: applying the trace base-change identity with M=Ri_*Lambda and using the exact closed sheaf equivalence gives the required supported trace directly. No general Gysin factorization-independence or regular-map composition theorem is assumed.

## Mathlib and blueprint searches

The item's earlier recorded searches are retained. New searches were run using msearch.py only, and the logged exact tool/query records were appended to the item. Semantic searches returned scheme immersion, smooth base-change, projective-spectrum, and unrelated normalization declarations; none states the supported etale identity. The source grep returned only a section heading in Mathlib/AlgebraicGeometry/Normalization.lean. Loogle's first mixed-word pattern was rejected by its parser and is recorded as such; the replacement quoted Gysin query was valid and returned no hits. A second semantic phrasing likewise found no etale Gysin identity. The logged results are retained in searches.jsonl; an unsuccessful parser query is not treated as evidence of absence.

Searched the entire DAG and blueprint for Gysin, smooth-immersion interchange, section regularity, closed-section geometry, and supported/trace comparisons. The blueprint's regular immersion theorem has field/smoothness hypotheses absent from this item, so it cannot replace this arbitrary-Noetherian-base assertion. Reused the existing ordinary Kummer, P1, affine trace, closed-support, smooth-chart and adjunction nodes. No new statement is proposed, and blueprint.same_as remains empty.

## Review by Q50

I read coord/delivery-errors.md B through E in full and checked the proof against the statements of its actual dependencies, rather than any dependency's proof. The main source is the Gabber volume, Expose XVI 2.5.7-2.5.10; the prescribed smooth normalization is Scholze 7.19 as already made precise by lem-per-ordinary-smooth-orientation. There are no new nodes requiring separate source or small-case audits.

Step 1 uses lem-sbc-smooth-relative-dimension-permanence for q', lem-pc-smooth-flat for flatness, and precisely the flat pullback clause of lem-per-immersion-class-calculus for j, its codimension and its supported class. That node allows nonregular intermediate schemes, so taking a regular-sequence flag later does not add a regularity assumption on its partial zero loci. The proof keeps support throughout: pulling an unsupported zero class back would not give this argument.

Step 2 uses the natural isomorphisms and Noetherian-base-change clause in lem-per-ordinary-smooth-orientation. prop-asd-smooth-base-change explicitly defines the exceptional exchange as the transpose of the pulled-back counit. With thm-cbc-finite-torsion supplying the actual compact-support exchange, the formula of def-weil-pbc-adjunction-mate converts these into the displayed equality of traces. lem-weil-pbc-mate-pasting and lem-amb-etale-compact-comparisons supply the compatibility of the actual composition maps. I checked that the coefficients are the finite constant ring F_ell on ordinary small-etale D+, and ell is invertible on every base.

Step 3 applies that equality to M=Ri_*Lambda_X, not merely to the constant object on Y. thm-cbc-finite-torsion gives the closed-immersion exchange needed to identify its source. lem-kun-04ca gives full faithfulness and i^{-1}i_*=id on abelian sheaves. lem-pur-etale-supported-kernel-adjunction gives exactness of i_*; prop-weil-pbc-inverse-image-modules-exact gives exact inverse image and the module adjunction. Applying these exact functors to complexes preserves the same unit/counit, so their closed equivalence extends to the derived categories. The ring action is carried componentwise. This proves the equality of supported traces without assuming a projection formula or an unstated smooth trace theorem.

Step 4 writes naturality at the actual supported morphism c_i. lem-per-immersion-class-calculus identifies its pullback with c_j and identifies the signed immersion adjoint. def-weil-pbc-composite-adjunction explicitly states that the hom bijection is the composite of the two bijections, so the two transposes are exactly the two star products, with the common (c)[2c] removed. All class shifts are even. This step is elementary once Steps 1-3 and the cited definitions are in place.

Step 5 uses lem-weil-pbc-section-separated-closed-immersion with the given separated p. Both S and P are smooth over S, so lem-pur-smooth-pair-local-coordinates applies to their closed immersion and explicitly supplies the regular-sequence chart. The subspace has relative dimension zero because its source is an open part of S. Alternatively the coordinate subtraction and lem-weil-pbc-etale-section-clopen-immersion isolate the desired zero fibre; the proof specifies scheme-theoretic inverse image, not mere inclusion of sets. After taking affine charts the etale morphism is separated of finite type; all schemes are Noetherian. lem-amb-etale-adjoint-locality therefore applies. lem-per-etale-section-deformation-comparison is used only for the normalized comparison it actually states, in the frame induced by the equations, with n=1. Its compactifiability requirements are met for these affine charts, their trivial normal bundles and the affine extended-Rees deformation. The ordinary orientation supplies the needed etale restriction compatibility.

Step 6 uses the equality c_D u_D=c_1(O(D)) in lem-asd-ordinary-supported-kummer. For a homogeneous linear section on P1 its divisor line is O(1), as seen from the coordinate transition. The inverse-image units compose to the identity since the section followed by the projection is the identity. Thus its pushed supported class is exactly h in lem-asd-ordinary-finite-p1-adjunction, and that statement gives t_q h=1. lem-amb-affine-space-top-trace explicitly defines the affine-line adjunction by restriction of this P1 adjunction, so the composite-adjunction formula gives the affine supported trace value. I checked this as a statement about maps, not just dimensions of cohomology groups.

Step 7 uses the supported regular-sequence flag product from lem-per-immersion-class-calculus and the ordered affine projection adjunction from lem-amb-affine-space-top-trace. The smooth orientation's composition clause and the composite-adjunction counit formula allow consecutive one-coordinate cancellations. This is an explicit induction, with identity base case d=0; it does not assume regularity of every partial flag or the parent general Gysin composition theorem.

Step 8 uses etale locality and mate pasting for the chart comparison. The clopen-section lemma identifies the unique etale sheet on the zero fibre, where its sum counit is the identity. The resulting maps are endomorphisms of the constant sheaf in degree zero. lem-sc-connective-single-hom, applied to the abelian category of etale Lambda-modules and a single degree-zero target, identifies these derived maps with sheaf maps. Images of the unit are sheaf sections, so open-cover descent detects equality here. This is not an assertion that arbitrary derived morphisms are detected by local restriction.

I tested d=0, c=0 (including open-and-closed immersions), the empty fibre, the affine zero section in dimensions one and two, and the identity smooth map. Empty components give the unique map on the zero category; codimension statements are only needed on nonempty components. The one-dimensional calculation gives +1 with the Kummer O(1) normalization; no residual sign or invertible scalar is introduced. All base-change uses have Noetherian bases and bounded-below inputs, and no field perfection assumption occurs.

Every proof citation has a verbatim supporting statement in citations.json. The off-unit generic tools are declared in split_report.tool_uses, with the relevant interface, and no maintainer-owned tool_uses field is set. The proof dependency list is exactly the union of step uses. A direct dependency traversal found no path back to this item from any of its dependencies. None of the eight proof steps exceeds 2000 characters; the formal trace comparison and the affine flag induction were nonetheless checked for hidden facts and their interfaces are cited explicitly. There are no statement changes, statement disputes, new definitions, clause-renaming nodes, duplicate nodes or Mathlib leaves to reconcile.

## Not duplicates

No new nodes. Existing supported Kummer and ordinary smooth-orientation nodes are cited directly.

## Unfinished work

None in the requested one-level split. The cited unsplit lemmas remain their own DAG items.
