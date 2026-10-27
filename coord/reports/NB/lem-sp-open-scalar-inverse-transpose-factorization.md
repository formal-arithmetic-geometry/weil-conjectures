# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-open-scalar-inverse-transpose-factorization.json`: statement item split into six steps; unchanged statement; no exact Mathlib match.
- `citations.json`: one verbatim statement quotation for each citation in each proof step.

New nodes: 0. Mathlib leaves: 0. No unit record changed: this item is not the unit's key statement.

## Attachments

None. Searched the actual read-only `lean/WeilConjectures/` tree for the item id, its blueprint tag, inverse-transpose factorization, open scalar comparisons, and compact-support coefficient/counit terminology. The inverse-transpose hits concern Frobenius or matrix lifts. The existing etale coefficient-change modules concern other coefficient comparisons; none supplies all of this item's actual pro-etale counit/composition/refinement clauses. No source declaration is claimed as a finished attachment.

## WANTED

None.

## What needed repair

The imported item had no proof. Its statement is retained verbatim. In particular, the generic coefficient-coherence node's statement is only about etale-origin pro-etale inputs. I did not apply it directly to an arbitrary intrinsic finite-Tor input. Step 2 uses the already existing full finite-Tor comparison equivalence, and Steps 4 and 6 explicitly cancel the naturality square at an input isomorphism. The conditional assumption of an equivalence in det-sp-et-proet-adjunction-transfer alone would not prove essential surjectivity; the cited lem-sp-etale-ctf-chart-domain actually states it for every standing scheme and both finite rings.

No statement dispute, source error or outstanding mathematical gap was found. Nothing remains unfinished within this one-level split.

## Existing nodes and Mathlib searches

No new node was needed. The generic composite-adjunction definition is already a Mathlib leaf, def-weil-pbc-composite-adjunction; I used it rather than creating a node for the counit formula. I read Mathlib/CategoryTheory/Adjunction/Basic.lean lines 562--585, in particular Adjunction.comp at 567 and comp_counit_app at 580. These give the formal counit clause, but do not identify the geometric coefficient comparisons, so the entire item is not a Mathlib leaf.

The item was searched afresh using the prescribed msearch.py command with LeanFinder (two different phrasings), Loogle, LeanSearch, and grep (including a focused Adjunction search). Every result was read, and the recorded queries are exactly the queries run; searches.jsonl preserves their results. The semantic hits concern ordinary ringed-space inverse naturality, module scalar extension, or abstract adjunction composition. None gives the specified finite-coefficient pro-etale compact-support refinement square. The original item's earlier search records are retained.

DAG and blueprint searches found the existing coefficient composition/refinement statement, the finite-Tor chart-domain equivalence, the normalized direct-image comparison definition and the composite-adjunction definition. Ran blueprint_refs.py ancestor for the item and searches for inverse-transpose, coefficient comparison, and finite Tor comparison. The ancestor is det-sp-reduction-exceptional. No imported blueprint node states this item's whole three-part factorization in another form; same_as remains empty. Elementary inverse-naturality and cancellation arguments remain proof steps, not new nodes.

## Review by NB

I read the current main-20261015 sk-lem-sp-reduction unit statement, the sec-smooth-purity chapter record, and det-sp-reduction-exceptional.proof.md, particularly its Locality paragraph. The proof follows that paragraph's left-adjoint route and does not invoke smooth purity or an exceptional scalar mate. I also read the direct-image proof's Step 1 defining the proper-counit/open-tensor map and Step 4 on naturality; Stacks categories.tex, Tag 0DV0, label lemma-compose-counits; and more-etale.tex, Tags 0F7J (lemma-shriek-composition) and 0GL6 (remark-Rf-lower-shriek-change-of-rings). The latter tags describe compactification composition and coefficient change, rather than asserting the whole normalized site/refinement square: that stronger square is explicitly taken from the existing DAG lemma that states it. No SGA source is used. For the domain issue I read the current finite-Tor chart-domain statement and proof, together with the current blueprint statement and proof for det-pe-finite-tor-comparison-noetherian. The finite-ring domain lemma covers arbitrary finite commutative ell-primary rings, rather than only quotients of a DVR.

Step 1 cites def-weil-pbc-composite-adjunction. Its statement explicitly gives the composite counit epsilon_2 composed with H(epsilon_1), so substituting J_R, U_R, F_f,R and G_f,R gives exactly the first displayed equation, for both coefficient rings and every H. The item's assumed adjunction-preserving comparisons justify use of the actual counit. This is an elementary substitution, not a claim that a definition proves an additional geometric theorem.

Step 2 cites lem-sp-etale-ctf-chart-domain. I checked that its statement includes both the equivalence on finite-Tor full subcategories for every standing scheme and R=A,B, and preservation by the scalar and compact-support functors. Thus Q has an etale finite-Tor antecedent E, and E_B is also finite-Tor. The coefficient-coherence theorem's bounded finite-Tor etale input condition is met. Schemes here and all selected compactification middle schemes are standing separated finite-type schemes over the arbitrary characteristic-p field. The ring map is unital and both finite rings are annihilated by the given N. No algebraic closure, smoothness, coefficient flatness or finite projective dimension is introduced.

Step 3 cites def-sp-reduction-direct-image-comparison. I read its actual definition of gamma as a transpose, the open normalization by beta and r, and b=Rp_*(e) gamma. Identity proper direct image has identity comparison under the identity unitors, since its defining counit is identity. This identifies the coefficient-coherence lemma's j comparison with the actual specified b_j. This is a calculation from the construction, not the use of an unspecified tensor isomorphism.

Step 4 cites lem-sp-et-proet-coefficient-compatibility. Its statement explicitly provides the composition formula for the named q=b on etale-origin pro-etale objects. I substituted inner j and outer f, with exactly the canonical compact-support compositors in the item. Both candidate maps have source S=T_Y F_g,A and target V=F_g,B T_U. I wrote the naturality equations at s:nu*E -> Q and cancelled the invertible S(s); this gives equality of actual maps at Q, independent of how the etale antecedent is chosen. No faithfulness of restriction of scalars on derived morphisms is being assumed.

Step 5 uses only the preceding equations and the natural isomorphism b_f already specified in the statement. I checked the direction of its naturality at v_A,M:J_A L -> M, inverted the two appropriate components, and substituted the composite counit. The listed intermediate objects show that every arrow is composable. Thus this is elementary categorical algebra, with no unlisted lemma: the last formula is a map from F_g,B T_U L to T_Y K.

Step 6 again cites lem-sp-et-proet-coefficient-compatibility. Its statement explicitly includes the refinement equation, its common-refinement version, and coherence with identity and composition. The same written naturality cancellation extends this equation from etale-origin inputs. Because the statement stipulates counit-preserving adjunction identifications, the first formula is the transported actual composite counit in every presentation; Steps 3--5 then apply with those coefficient squares. This covers the common-refinement clause without silently extending the original lemma's domain.

For C1 and C4 I opened each of the four cited node files and copied exactly the part of its statement used by the proof into citations.json (the longer definitions/domain statement are quoted whole to include all used clauses). The proof_deps list is exactly the union of uses. The off-unit coefficient-coherence lemma is declared in split_report.tool_uses as a generic existing tool; no unit proof route is replaced. The composite-adjunction node is already a Mathlib leaf. No new-node duplicate, hypothesis or statement-only checks arise.

I tested the formulas for j the identity (all open factors and v become identities), U empty (the source factors through the zero category), K=0, and the identity coefficient map (the coefficient comparisons become identities). The formulas reduce respectively to the outer counit identity, the unique zero-source map, zero maps, and the composite counit formula. Nonflat examples such as Z/ell^2 -> Z/ell remain allowed: the only use of tensor is its given derived functor and the existing coefficient-coherence theorem, with no ordinary-tensor replacement. A zero coefficient ring, if allowed by the ring convention, also gives only the zero-category identities. All non-elementary proof steps are shorter than 2000 characters and none hides a new comparison lemma.

This is the self-review authorized by the direct-delivery brief; the maintainer's independent review remains the next reader.
