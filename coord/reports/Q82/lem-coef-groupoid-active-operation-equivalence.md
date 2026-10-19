# Worker report: lem-coef-groupoid-active-operation-equivalence

## Files written

- `dag/nodes/sec-six-functors/lem-coef-groupoid-active-operation-equivalence.json`: statement, now split into eight proof steps; not a Mathlib leaf. Its statement, chapter, unit, ancestry, source metadata, and inherited searches are retained.
- No new DAG nodes and no Mathlib leaves. The earlier proposed `lem-coef-path-space-endpoint-equivalence` is redundant with `lem-coef-space-path-fibration-replacement`, specialized to the identity of a Kan complex. Its entire saved file is retained as `saved-path-space-attempt.json` outside the delivered node directory, rather than submitted as a duplicate.
- `citations.json` records a verbatim statement passage for each of the 28 step/node citations. `searches.jsonl` contains searches actually made in this continuation. These are local evidence, not extra DAG changes.

## Attachments

None. Searches for the exact blueprint tag and for active-operation, pair-color, operad-groupoid and path-space notions in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` found no declaration stating this item. No source declaration has been treated as a finished proof and no compiler was run.

## Wanted sources

WANTED: Gepner–Haugseng, *Enriched infinity-categories via nonsymmetric infinity-operads*, arXiv:1312.3178, Definitions 4.2.2, 4.2.4, 4.2.6, Theorem 4.2.7 and Erratum Corollary E.0.1, for lem-coef-groupoid-active-operation-equivalence. Read the online HTML at https://arxiv.org/html/1312.3178; an archival copy is not in literature/. The proof is therefore marked agent-written, as the standing brief requires.

The discarded path lemma cited Kerodon 00UB. That URL failed to load in this continuation. This is not evidence against its statement and is not needed for the delivered proof, which uses the existing path-replacement node.

## Corrections and scope

The saved item had no proof or report. The extra saved node was marked unsplit but carried a proof and proof dependencies, contrary to B1, and its cited searches had no local search log. I retained the file outside the delivery, ran its four saved search questions for real, and then found the existing general path-replacement statement. No new node is needed for the explicit min/max contraction.

No statement dispute or correction is necessary. The important distinction is between the corrected operation space, where source changes have identity arity, and the larger active slice in the original proof. We use the corrected operation space throughout and do not invoke the uncorrected localization corollary. The chapter and unit are unchanged; this is the extracted ordinary-operadic-replacement calculation below the integral exceptional-adjoint ancestry, not a change of the six-functors route. No SGA source is used.

## Not duplicates

No new nodes are submitted. The proposed path-space endpoint lemma is a specialization of the existing `lem-coef-space-path-fibration-replacement`: for the identity of X its mapping-path object is precisely Fun(Delta^1,X). Its endpoint retractions follow from that equivalence or from the saved min/max homotopies. Blueprint searches for `path` and `groupoid`, DAG keyword searches for constant paths, endpoint evaluation and path spaces, and a full-statement scan for arrow/groupoid/nerve comparisons found the existing general tools now cited. The blueprint ancestor command confirms `prop-coef-integral-exceptional-adjoint`; the item's `same_as: []` is retained. There is no blueprint node stating this operation-space computation in another form.

## Review by Q82

I read the node and its four statement dependencies, the unit `sk-prop-sf-biduality-general`, chapter `sec-six-functors`, the current snapshot's integral exceptional-adjoint material, and the online definitions and proof of Gepner–Haugseng Theorem 4.2.7, together with its erratum. The source's formula gives n+1 factors, not n, in the string fiber, and n+1 joining arrows in a positive-arity pair operation. The source supplies both the inversion on the first endpoint and the identity internal arrows of Phi. The item faithfully extracts these formulas with the corrected restriction to identity-arity source changes; its nullary clause is checked separately. I opened every proof dependency's statement, not just its source or proof.

Step 1 uses the operation-criterion node only for the definition of the corrected operation space, not for its localization conclusion. The slice-right-fibration node states the full coherent slice and its mapping-space fibers. Pullback and restriction to the one discrete active base-map component explain its application here. The operator-nerve statement gives the string fiber; its operator mapping formula and the groupoid-operator node give the product of unary pair-color groupoids. The coherent-nerve comparison supplies Kan nerves and the mapping-set comparison, while transport classification supplies the contravariant mapping-space functor with precomposition. Thus no passage from components to a whole operation space is being asserted without a node.

Step 2 uses the string mapping formula to retain just the first and last arrows, leaving the n-1 internal objects free. Inversion turns the first incoming arrow into an arrow starting at x. The coherent-nerve comparison is explicitly natural and composition-compatible, and the transport node identifies the fixed-source and fixed-target arrow fibrations. The product identification is justified by independent tuples over the same source data; it does not assume discrete source objects.

Step 3 checks the hypotheses of the corner-map theorem with the injective boundary inclusion and the Kan fibration X to a point. This makes two-endpoint evaluation a Kan fibration. The pinch-comparison statement identifies its fiber with the specified right-pinched mapping space. The transport node states precomposition and postcomposition, including their higher compatibilities; the displayed square gives exactly h beta s-inverse. These statements justify the full internal arrow-space factor, not only its set of paths. This intermediate comparison is a specialization of existing general tools, so no new comparison lemma is created.

Step 4 checks the actual operator-map statement, whose product is G(x,a0), the internal G(bi,ai), and G(bn,y). Substitution by independent unary arrows yields alpha=r0 alpha-prime, beta=ri beta-prime si, gamma=gamma-prime sn. Writing hi=ri-inverse identifies exactly the squares of Step 3. Each source variable belongs to exactly one endpoint/path factor, which proves the product description via the cited coherent transport. Step 5 uses the same operator-map node's explicit Phi formulas, including the first inverse and the internal identities; on source changes its pairs are (u-inverse,u). Therefore the comparison of product spaces really is the constant-path map with identity endpoint factors, coherently. No assertion of equivalence has been hidden inside a new restatement of the item.

Step 6 applies the path-replacement node with f equal to the identity of the Kan space X. Its statement explicitly supplies the constant-path weak equivalence. The coordinatewise inverse is endpoint evaluation, so finite products require only the displayed coordinatewise homotopies. The saved contraction formula supplies these homotopies directly if desired. I checked its min/max orientations: min joins c e0 to the identity; max joins the identity to c e1, which is sufficient. No additional non-elementary product theorem is used.

Step 7 uses the string formula with n=0, where both selected endpoints coincide. The coherent-nerve and transport nodes give spans with simultaneous source changes and all higher compatibilities. The normalization arrow is a:z to x: its two triangle equations are id a=a and (b a-inverse) a=b. Naturality under a span change follows from a-prime u=a and b-prime u=b, with coherent composition supplied by the cited nodes. The pinch comparison relates fixed-endpoint arrows to the mapping-space convention of the statement. Step 8 uses the operator formula at the empty input list; it leaves the single factor G(x,y) and Phi is exactly b a-inverse, as the zero-length-block clause states. Thus the normalization is the induced map, and the inverse h to (x,id,h) is verified rather than asserted by transport language alone.

The finite arities n=0, n=1 and n=2 were tested separately. For n=1 no internal factor remains. For a discrete groupoid, operations occur precisely for the matching endpoint data and the two positive-arity descriptions coincide. If x,y lie in different components, the nullary spaces are both empty; no connectedness or nonempty mapping-space hypothesis was used. A one-object groupoid with nontrivial automorphisms tests why coherent quotient data must be retained: the nullary answer is the full automorphism mapping space, not its quotient by conjugation. An empty G has no x,y and the assertion is vacuous. All groupoid inversions and compositions used commute with simplicial operators; local Kan fibrancy is used before each comparison with spaces.

I checked B--E in the delivery-errors list against these statements. There are no new nodes requiring B1--B9 checks; the potential B1/duplicate failure was removed by reuse. Every non-elementary fact is a cited general statement (C1), and each quote in citations.json is copied from that statement (C4). No step uses a cited proof as its interface. The imported statement and definitions were not weakened, and no route was replaced. Generic tools from other units are declared in split_report.tool_uses where applicable. Every step is below 2000 characters; I also checked the path-space and normalization comparisons for hidden independent lemmas and used the existing general nodes for their non-elementary content.

## Search evidence and saved work

The item already contains five queries and their full returned results. I read those results and reran the corresponding first semantic question, Loogle pattern, grep and LeanSearch question because this sandbox had no search log. The second semantic phrasing is also checked. The hits are ordinary groupoids, ordinary nerves, strict Segal simplicial sets and enriched-category infrastructure; none states the full coherent fixed-arity calculation. I read the indicated Mathlib enriched-functor and simplicial-nerve sources and the strict Segal definition. In particular the latter encodes strict decompositions, not this infinity-operadic comparison. The item remains a split, not a Mathlib leaf.

The abandoned path-node queries return abstract model-category path objects and unrelated paths. The saved Loogle query `SSet, Fun, Delta 1, Kan` is rejected for unknown identifier Fun, rather than a successful absence result. All actual calls are in searches.jsonl; no unsupported searches have been added to a new delivered node.

The saved proof remains in saved-path-space-attempt.json. Its first step explicitly contracts paths by min/max, and its second cites `lem-cbc-simplicial-homotopy-equivalence-weak`. The delivered item preserves the min contraction as an optional explicit inverse homotopy in Step 6, while using the stronger existing path-replacement statement. There was no saved report or citations file to discard.

## Unfinished work

No mathematical subtask remains for this one-level split. All referenced general nodes already exist; their own further splitting is outside this item. The required server dry run and delivery are run after writing this report. No claim of successful delivery is made until the delivery command exits successfully.
