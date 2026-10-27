## Worker report

Files written:
- dag/nodes/sec-purity-real-sheaves/lem-a1-groupoid-source-pullback-translation.json: existing statement, now split into four steps; no Mathlib match for the whole item.
- citations.json: a verbatim statement quote for each citation in each proof step.
- searches.jsonl: actual msearch.py calls and their results, retained with the delivery.

New nodes: 0. New Mathlib leaves: 0. The proof reuses the existing Mathlib leaf lem-weil-pbc-finite-flat-rank-iso.

Attachments: none. I searched lean/WeilConjectures for the exact blueprint id and for groupoid/translation terminology. There is no declaration of the project giving the two source-pullback morphisms and all the rank clauses. Ordinary groupoid facts and translations of Artin--Schreier covers do not state this item.

WANTED: none.

The assigned node had no proof. Its statement was mathematically correct; I normalized its doubled TeX backslashes only. There is no mathematical statement correction or STATEMENT-DISPUTED issue. I preserved all inherited node metadata. Nothing remains unfinished in this one-level split.

## Sources and blueprint searches

I read literature/stacks-project/groupoids.tex, groupoid axioms before definition-groupoid (Tag 0231), lemma-diagram (Tag 02YE), and lemma-finite-locally-free-disjoint-free (Tag 03BI). The first source explicitly leaves the groupoid diagram argument as an exercise; steps 1 and 2 supply the morphisms and both cancellation computations. The latter source compares the two base-changed source fibres at z; step 3 implements that comparison using the rank lemma instead of inserting an extra fibre-degree node. I also read morphisms.tex, definition-finite-locally-free (02KA), lemma-finite-flat (02KB), and lemma-finite-locally-free (04MH).

I read dag/chapters/sec-purity-real-sheaves.json, dag/units/sk-p-real-rankin.json, and the latest blueprint proof of lem-a1-affine-hc0. The inherited ancestor place describes an older fourth-paragraph affine quotient route. The latest ancestor proof now uses locally constant finite-level sections and compact supports directly, and contains no groupoid paragraph. This is a historical provenance mismatch, not a reason to change the assigned auxiliary theorem or the fixed chapter/unit. The split_report.blueprint records this explicitly; no ancestor, unit or chapter is edited.

I ran tools/blueprint_refs.py ancestor on the item and search for 'groupoid', 'source pullback', and 'degree base change'. I searched the DAG for 02YE, 03BI, source translation, finite locally free degree/rank, and base change. The existing affine rank-strata parent needs this item and cannot be cited back; the invariant-open-restriction node restricts structure maps on an already invariant open and does not give translation. The affine coordinate-identities node assumes affine schemes and gives ring identities, not this isomorphism. The rank-filtration statement is a different closed filtration for finite groupoids, not translation. No new nodes are needed.

The item retains its previous searches. The five new msearch.py calls (two LeanFinder phrasings, Loogle, grep, LeanSearch) returned open-cover pullback isomorphisms, scheme group-object base change, and ordinary groupoid inverse identities; none states the item. I read Mathlib/CategoryTheory/Groupoid.lean, the relevant pullback declarations in Mathlib/AlgebraicGeometry/Pullbacks.lean, and Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean. The latter supplies the exact existing leaf used: Scheme.Hom.finrank_of_isPullback at line 165 and Scheme.Hom.isLocallyConstant_finrank at line 226. The leaf's statement identifies rank with the fibre-coordinate dimension and has all hypotheses the proof requires.

## Not duplicates

No new nodes were created. Generic rank/base-change work is already covered by lem-weil-pbc-finite-flat-rank-iso, so I cite it instead of creating a duplicate of its rank clauses or a new node restating a clause of the item.

## Review by Q92

I checked the source and every cited node's statement with the four proof steps open. This is the author's direct-delivery review; the maintainer still supplies independent review.

Step 1 uses def-pc-fibre-product, which states existence and uniqueness of a morphism with compatible projections, and def-a1-groupoid-scheme, which gives sc=s pr_1, si=t, ti=s and the source/target compatibility. These really give the three displayed lifts: (c,p_2), (q_1,i q_2), and (c h,q_2). In particular the last lift goes to P, not Q. Both maps preserve the second projection by construction. No affine or flat hypothesis was used.

Step 2 uses the actual associativity, unit and inverse formulas in def-a1-groupoid-scheme. I checked the endpoints: c(b,i(b))=e(t(b)) is the correct identity for the first cancellation, and c(i(b),b)=e(s(b)) for the second. The conditions s(a)=t(b) and s(d)=s(b) make those compositions defined. Testing the identities on every H and then evaluating at the identity of P or Q proves equality of scheme morphisms; it is not an argument from geometric points alone and needs no extra Yoneda theorem. These two steps are elementary evaluations of the cited definitions, not postponed lemmas.

Step 3 uses def-pc-fibre-product for the defining cartesian square, def-pc-finite-locally-free for finite+flat+locally-finite-presentation, and clause (2) of lem-weil-pbc-finite-flat-rank-iso. I read that leaf's whole statement: it gives rank under arbitrary base change, not just field extension or constant-degree base change. The second square is proved cartesian with the explicit unique lift G(d,b); it is not asserted by a reference to the item's conclusion. Thus the same p_2 has rank d(t(z)) and d(s(z)). The finite, flat, locally-finite-presentation hypotheses are exactly the available s hypothesis; no such hypothesis is used before this step. I avoided citing the line-bundle degree node lem-pc-degree-base-change, whose notion of degree is different. The cited rank leaf is Mathlib and is a generic tool permissible across units without changing the unit route.

Step 4 uses clause (1) of the same rank leaf, whose statement explicitly says the rank strata are open and closed. The remaining argument is elementary membership in inverse images. Equality as open subschemes follows because both carry the restriction of O_R on the identical open subset. The converse uses r=d(s(z)), so the asserted equivalence is proved as well. Citations.json quotes each statement verbatim; none of these steps relies on the proof of a cited node.

For edge cases I checked U=R=empty (all identities hold, all strata empty), the identity groupoid on arbitrary U (F,G are identity after the diagonal identifications), a nontrivial group scheme over one object (R to U need not define a monomorphic relation), and a nonreduced finite flat group scheme such as mu_p in characteristic p (the argument uses all test schemes, so nilpotents are retained). Rank zero is allowed in the formulation and in the rank leaf; on a nonempty groupoid base it cannot occur because the unit gives a point in each source fibre, but the proof does not need that extra fact. Nothing requires connectedness, quasi-compactness, separatedness or constant rank.

Against delivery-errors B--E: there are no new statement-only nodes to audit or search; the existing statement is self-contained with its definition citations, and its TeX escaping has been normalized. Every non-elementary fact used is the rank leaf's stated clause. No new node absorbs an item clause; construction, cancellation, and cartesianness are written in the proof itself. There is no cyclic parent citation, no missing finiteness hypothesis, and no identification based only on images of points. All four steps are below 2000 characters, and none hides an additional comparison theorem. The repairs made while drafting were to use the exact rank leaf (rather than the unrelated line-bundle degree node) and to spell out the cartesian lift and equality of open subscheme structures.
