# Q47 stage-1 delivery: lem-per-normal-flat-chart-relation-removal

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-normal-flat-chart-relation-removal.json — statement, split in five steps; not a Mathlib leaf.
- citations.json — verbatim statement extracts for the three citations in steps 1–3.
- report.md — this report and author's mathematical review.

There are 0 new nodes and 0 new Mathlib leaves. Only the sandbox was written; no Lean was written and no compiler, Lake, local DAG checker, or git command was run by the worker. write_split.py is a sandbox-only preparation aid, not a delivery file.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for normal-flat, chart-relation, Hironaka, initial-coefficient and leading-syzygy terminology. The project dehomogenization declarations describe polynomial chart maps, not this ideal-intersection assertion. No project declaration gives all the item's clauses.

## WANTED

WANTED: Hironaka, Certain numerical characters of singularities, J. Math. Kyoto Univ. 10-1 (1970), 151–187, archival local copy; especially Lemma 17, pp.172–173, and Lemma 20, (20.3)–(20.12), pp.177–181, for lem-per-normal-flat-chart-relation-removal. The document named in the live node is absent from literature/. I read the online PDF at https://scispace.com/pdf/certain-numerical-characters-of-singularities-18d51ii5bz.pdf, including the basic assumptions (2.1)–(2.2), (19.1)–(19.2), Lemma 17 and (20.3)–(20.12). The finite-jet reformulation and induction are agent-written, and proof_origin.by remains agent. No claim is made to have read a local Hironaka PDF. No SGA source was used.

## Audit of the imported item

The statement is unchanged. No statement dispute was found. The redundant stmt_dep def-trf-permissible-basis-chart-data was removed: the statement introduces its own rings and maps, cites the coordinate-chart construction directly, and does not use a notion defined only by that larger data node. All other statement dependencies were retained. The order and initial-form conventions are written inline; def-trf-local-standard-basis-invariants supplies the order/minimality convention, not an unmentioned theorem.

The reduced-case twin lem-trf-normal-flat-chart-relation-removal is existing source material, not a theorem applicable to nonreduced R. Its five-step assembly can be checked without reducedness using the actual statements of lem-trf-normal-flat-initial-coefficient-lifting and lem-trf-projective-order-leading-syzygies. I rewrote the chart calculation, explicitly checked all the hypotheses of both inputs, specified the induction invariant, and made the finite-jet use explicit. I did not cite the reduced-case twin as if its extra hypothesis were available.

The source's normal-flat coefficient calculation in (20.6) and (20.7) and its raising of weighted coefficient order in (20.12) are the route followed here. The finite-jet hypothesis replaces the particular numerical-generator argument used to reach (20.7). The perverse chapter and unit were read and left unchanged; this is generic commutative algebra below the ancestor's regular-resolution branch. The two off-unit tools are declared in split_report.tool_uses; no node in the item unit states either input.

## Not duplicates

No new nodes were created. For the existing item: lem-per-normal-flat-chart-relation-removal vs lem-trf-normal-flat-chart-relation-removal: the latter assumes R is reduced, while this item imposes no such assumption; its conclusion cannot be cited directly here. The smaller coefficient-lifting and leading-syzygy statements are reused, rather than recreated for the perverse chapter.

Whole-DAG keyword searches found these existing tools and the reduced twin. tools/blueprint_refs.py searches for normal flat, syzygies, relation removal, and coefficient lifting found no blueprint node stating this item. The nearest ancestor is lem-per-artin-gabber-affine-curve; its current latest blueprint statement/proof and the recorded chapter/unit were read. The existing blueprint.from.place already specifies the coefficient-elimination role, so it was retained, with same_as=[] and the same place recorded in split_report.blueprint.

## Mathlib searches

The item might itself be in Mathlib, so fresh searches were made using only the authorized msearch.py. The existing imported search records were preserved and the actual Q47 records appended. LeanFinder was tried twice with different formulations; Loogle, LeanSearch, and Mathlib grep were also run. Search results and digests are in searches.jsonl. The first semantic query returned ramification-index quotient maps over Dedekind domains, which do not give the chart intersection; the second returned smooth and submersive presentations. LeanSearch returned formal smoothness and ordinary flatness stability, not normal-flat standard-basis relations. Loogle's strongest candidate was Ideal.exists_pow_inf_eq_pow_smul (Artin–Rees), whose declaration in Mathlib/RingTheory/Filtration.lean:389 was read: it gives eventual intersections with powers of one ideal and an unspecified threshold, not this finite prescribed jet bound involving two different ideals. The grep hits in Submersive.lean and WittPolynomial.lean refer to ordinary module standard bases, as confirmed from their source. There is no exact or one-line-specialization match. The extra grep was directed at Filtration.lean to locate the Artin–Rees candidate. Every appended query is copied exactly from the real search log; no unavailable response is recorded as absence.

## Review by Q47

I checked B–E of delivery-errors.md, in both copies, against the item, the source and the cited node statements. There are no new unsplit nodes that might hide a proof sketch or restate a conclusion. No step merely applies a renamed intersection theorem. The only two non-elementary steps invoke smaller existing results, and all five proof steps have explicit elementary flags. The non-elementary steps have lengths 1099 and 1057 characters, below the 2000-character audit threshold; the remaining steps carry finite algebraic bookkeeping from those steps. I checked each one as follows.

1. I opened def-nagata-blowup-chart-ring and copied its actual definition into citations.json. It says the chart is a subalgebra of the localization R[1/xbar_0], precisely what is used. Multiplication by xbar_0 is injective on the subring even if R has nilpotents; localization preserves this by the explicit annihilator argument in the step. The divided expression of v in a cap P^h maps to zero because multiplying it by xbar_0^h gives zero. Reducing the parameter-monomial expansion modulo H gives theta_i. The triangular prefix identities prove equality of the two prefix ideals by induction, and thus w_j is in HJ. The equality of quotient maximal ideals gives lifts of every power N^v. These are ring and ideal calculations, not an appeal to a definition for an extra theorem.

2. I opened the full statement of lem-trf-normal-flat-initial-coefficient-lifting. It takes precisely a regular local ambient T, the parameter ideal P, normal flatness of gr_I R over A, and the given minimal initial generators f_i in P^{d_i}; importantly its last sentence explicitly allows nonreduced R. For u from a homogeneous syzygy, membership in a cap P^h and vanishing of its degree-h initial class prove all three membership hypotheses of that lemma with n=h. Its conclusion is quoted verbatim in citations.json. All indices d_i<=h are included, including possible generators beyond the prefix. Coefficients in M P^{h-d_i} divide into H, and the remainder in a cap P^{h+1} divides into a' by step 1. This proves the syzygy-lift sum is in H a', rather than claiming it is already in HJ. No regular-sequence or tensor-exactness fact is used without a node.

3. I opened lem-trf-projective-order-leading-syzygies. It only needs a field k, a prime polynomial localization L, nonzero homogeneous forms of degrees at most e lying in U_{d_j}, and coefficients in N^{e-d_j} with summed product in N^{e+1}. At stage e, exactly the active indices have d_j<=e, and the hypothesis phi_j(1,t) in N^{d_j} puts their forms in U. Nonzeroness comes from finite order d_j of f_j. Removing inactive terms leaves a sum in N^{e+1}. The verbatim conclusion in citations.json gives both the homogeneous syzygy and the residue coefficient improvements. No rationality of the point, perfectness of k, or minimality in gr_N L is required by this node. Inactive coefficients are extended by zero, as explicitly stated in the step.

4. I checked the finite sum of lifted syzygies rather than invoking any further comparison theorem. Substituting q_j=g_j-w_j changes a lifted syzygy sum only by HJ. Its sum is therefore in H a'. The finite-jet hypothesis a' subset J+M'^d yields H a' subset HJ+M'^{d+1}, since H subset M'. Thus the coefficient replacements preserve the represented element modulo E=HJ+M'^d and keep its residue sum in N^d. For active indices the exponent increases by one; for inactive indices the next exponent is zero. This proves the stated induction invariant for every transition.

5. I checked termination after d-1 transitions. The surjection M'^v onto N^v gives lifts of the final residues with exactly the powers needed; multiplying by q_j of order d_j places each resulting term in M'^d. Differences of lifts contribute HJ. Congruence modulo E then proves the original element belongs to E. This step uses the already established construction, not a new standard-basis lemma. The allowed b=0 case has J=0; d=1 has no transitions; d_j=d never becomes active and its product is already in the required power. If r=0, nonzero positive-degree forms are powers of X_0 and cannot satisfy the prefix maximal-order condition in L=k, so b>0 has no such data; the empty-prefix conclusion remains valid. No nilpotent element is cancelled in R itself.

For a concrete nonreduced test take T=k[[x_0,x_1,x_2]], P=M, a=(x_1,x_2^3), and the chart point t_1=t_2=0. Then R=k[[x_0,x_2]]/(x_2^3), A=k and gr_I R is flat over A. Its minimal prime (x_2) does not contain I. Take f_1=x_1, f_2=x_2^3, b=1 and d=3. Here T' is the local chart ring with parameters x_0,t_1,t_2, H=(x_0), g_1=q_1=t_1, g_2=t_2^3 and a'=(t_1,t_2^3) subset (t_1)+M'^3. The desired assertion says (t_1) cap ((x_0)+M'^3) subset (x_0t_1)+M'^3, which follows directly by inspecting monomials of total degree below three. Thus the hypotheses admit a nontrivial nilpotent example. For a nontrivial coefficient syzygy use the prefix t_1^2,t_1t_2 at the origin: (-t_2,t_1) is the reduction of the homogeneous syzygy (-X_2,X_1), and its lifted sum vanishes, as required by steps 2–4. The same pattern can be realized by a=(x_1^2,x_1x_2,x_2^3), with b=2,d=3; its sole minimal prime (x_1,x_2) misses x_0. These checks include equal generator degrees and a genuine prefix syzygy.

I also traversed the statement/proof dependency closures of all three citations: none reaches this item, so the assembly introduces no cycle. Each citations.json quote was checked as a verbatim substring of the node statement. Existing imported metadata and blueprint fields were preserved. The no-new-node choice avoids elementary, duplicate and clause-restatement nodes.

## Unfinished work

No split obligation remains. The two existing input nodes retain their own independent proof obligations in the DAG; they were not edited. The local archival source remains WANTED. Required server dry run and delivery results will be recorded below.

## Server validation

The required dry run exited 0 and printed: OK (not pushed) deliver/Q47/lem-per-normal-flat-chart-relation-removal at 39e54726353: preflight passed. The server ran the required preflight, including its DAG and split checks. There were no failures to repair. Direct delivery follows this successful dry run.
