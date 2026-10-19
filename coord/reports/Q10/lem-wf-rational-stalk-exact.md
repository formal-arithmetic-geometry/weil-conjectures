# lem-wf-rational-stalk-exact

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-wf-rational-stalk-exact.json: statement, split; Mathlib has no exact match. No new nodes, no Mathlib leaves.
- citations.json: seven entries, one for every cited node in every proof step, copied verbatim from its statement.
- searches.jsonl: the search command's own log. make_split.py and bhatt-scholze.txt are sandbox working material, not DAG deliveries.

## Attachments

None. Searched WeilConjectures in the read-only slopmaster2 source for the item id, the blueprint tag, rational/stalk/exactness terms, and shortExact/stalk combinations. Read WeilSheaf/LocalFrobenius.lean: it implements ordinary cohomology-sheaf stalk operators rather than this rational derived point-fibre assertion, and does not supply the whole exactness theorem. Its embedding-conjugacy declaration is sorried and is not an attachment.

## WANTED

None.

## Corrections and scope

The item statement is retained literally. Its empty proof is replaced by three steps. The existing stronger lem-dl-a1-constructible-fibres-exact already gives exact finite-dimensional coefficient fibres in the same heart, including the Weil forgetful case. Creating another fibre-exactness lemma would duplicate it. The proof's additional content is the explicit intertwining calculation for the normalized local operator. In particular, the geometric point returns after e Frobenius iterations through g_Y^e xbar = xbar g_s^e; it is not literally fixed as a scheme morphism.

The coefficient-fibre lemma names def-weil-constructible-heart itself, as does this item; its coefficient fibre is explicitly derived pullback followed by def-weil-finite-coefficient-point. This invocation uses that shared heart and fibre interface, and does not identify arbitrary sheaves on the pro-etale site with the rational category. No invariant integral Weil lattice is assumed. The realization iota in the affine-line conventions plays no role in the cited lemma's coefficient exactness assertion or this application.

The off-unit tool uses are declared in split_report.tool_uses: constructible coefficient-fibre exactness, point-transport naturality, and natural composition of the integral pullbacks used by the local operator. These are generic categorical tools, not replacements of the weight-energy unit's argument. Read sk-l-dl-a1-energy and its chapter and compared the main-20261015 lem-wf-l2-upper proof: this item supplies the Frobenius-stable stalk filtration implicit in its opening punctual bound.

## Not duplicates

No new nodes were created. The DAG searches found lem-dl-a1-constructible-fibres-exact, which is cited directly. Whole-blueprint searches for exact stalk constructible, rational-stalk-exact, fibres exact, constructible fibres and Frobenius natural produced no additional blueprint node stating this item. The item's existing ancestry to lem-wf-l2-upper and same_as [] are retained.

## Review by Q10

I read Bhatt--Scholze section 6.8 in the local PDF, particularly Corollary 6.8.5 (kernels/cokernels of lisse rational sheaves), Lemma 6.8.7 (constructible kernels/cokernels), Proposition 6.8.14 (rationalization and finite coefficient stages), and Remark 6.8.15 (closed-immersion pullback is naive inverse image). I compared these with the current stronger coefficient-fibre node and its explicit heart/fibre convention. These sources support the coefficient framework; I mark the assembled proof agent-written because the normalized Frobenius calculation is expanded here rather than copied from the PDF. I created no lemma requiring an additional source.

Step 1 uses the exactness and finite-dimensional-vector-space clauses of lem-dl-a1-constructible-fibres-exact and its explicit Weil forgetful clause. I checked its full statement, not its proof. Its separated finite-type Y_0, geometric point Spec(k), and ell distinct from p match this item's assumptions, and its named heart is def-weil-constructible-heart. I read that definition: the heart is the standard heart in the raw rationalization/common-stage category, not an arbitrary sheaf category. The finite-dimensionality conclusion is supplied by the cited lemma, not inferred from ordinary stalk exactness.

Step 2 uses only the morphism equation of def-weil-weil-sheaf-complex and the recurrence of def-weil-local-frobenius-trace. I checked the recurrence's composition direction and wrote the n=1 base and n to n+1 calculation. Functoriality and associativity suffice, so this step is elementary. In particular the operators go from Frobenius pullback toward the original object, with the same direction as the source definition.

Step 3 uses def-weil-local-frobenius-trace for the formula P(theta^[e]) J and the source reparametrization; lem-weil-frobenius-point-transport-natural (2) explicitly supplies naturality at all four coefficient types, including Qbar, and compatibility with scalar extension. I opened its statement to verify this is a theorem, since the transport definition explicitly does not assert naturality. I also opened lem-pod-integral-pullback-composition: its statement gives a natural comparison for the actual integral derived pullbacks used by the local-operator definition. The latter definition specifies their rational scalar localization, so their naturality identities still hold stagewise and in the common-stage category. This avoids substituting a different completed-pullback construction. Composing these squares gives J's naturality. The displayed four-equality calculation then proves commutation on the point complex and hence on H^0, which is the sheaf fibre. I checked the types of both sides P(u) F_K = F_L P(u), then applied this to each of the two sequence maps.

Small cases checked: zero sheaves give the zero exact sequence and zero fibre; a rank-one constant sheaf with any invertible Weil scalar gives the same scalar on its fibre; for e=1 the induction is exactly the Weil morphism equation; for e=2 the recurrence gives theta T(theta) and the calculation moves u across those two factors in order. A nonsplit two-dimensional Jordan extension still yields an exact sequence of Frobenius modules; semisimplicity and purity are never used. No statement correction or extra hypotheses were needed.

Against delivery-errors B--E: no new statement-only/definition/Mathlib-leaf issue arises; every cited node's statement was read and its relevant sentence/formula copied to citations.json; all proof uses are in proof_deps. A dependency traversal confirmed none of the three theorem tools reaches this item. No argument is hidden behind a new clause-restating node; the equivariance induction and identity are written out. All steps have fewer than 2000 characters. Searches were actually run through msearch.py (four tools and a second LeanFinder phrasing), their hits read, and their exact queries and result names appended to the preserved existing search history. Ordinary stalks, Galois fibre functors, module completion and Witt-vector Frobenius hits are not this adic Weil assertion. No SGA source is used. I additionally read Deligne Weil II (1.1.7)--(1.1.8), pp. 150--151, for the fibre transport convention, and Stacks Tags 099N (proetale, lemma-pushforward-Noetherian-case), (2) and (5), and 0D6D (sites-cohomology, lemma-derived-pullback-composition), for the sources named by the integral-composition node. No Lean was written and no compiler was run.

The first dry run requested longer verbatim quotes for the iterate/local-operator and composition citations; these now include the full formulas. The next dry run passed at 4767f0032d. In a final read I corrected an escaped TeX inequality that a working script had converted to a newline; the corrected delivery is being checked again before push.

## Unfinished

None in this one-level split; the existing cited unsplit lemmas remain their own DAG tasks.
