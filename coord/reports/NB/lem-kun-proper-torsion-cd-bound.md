# Stage-1 report: lem-kun-proper-torsion-cd-bound

## Files written

- dag/nodes/sec-smooth-purity/lem-kun-proper-torsion-cd-bound.json: existing statement, now split into six steps; Mathlib searches found no match.
- citations.json: twenty verbatim statement quotations, covering every node cited in the six steps.
- report.md and searches.jsonl: report and actual search-command log.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searching WeilConjectures in the read-only slopmaster2 checkout by the exact item tag and by cohomological dimension found no declaration asserting this proper higher-direct-image bound. AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_add_lt in AlgebraicGeometry/Sites/CohomologicalDimension.lean has sorry; the separably closed specialization uses it. Neither is an attachment of this item: both concern total cohomology over a field. The upstream master proper-base-change source was consulted only as reference material, not proof evidence.

## Literature wanted

None. The source and the reused blueprint cohomology proof are available locally.

## Corrections and route

The statement is correct as written in Stacks 095U (etale-cohomology.tex, lemma-cohomological-dimension-proper), including arbitrary bases and arbitrary torsion abelian sheaves. It has not been changed. Its five statement dependencies still introduce exactly the notions used in it.

The empty imported proof has been replaced. Stacks proves the fibre bound by dimension induction; this split uses its geometric-stalk reduction, but obtains fibre vanishing from the existing, more general thm-sc-finite-type-torsion-cd. This is a choice below the unit level: the Kunneth unit and chapter are unchanged. The proof is explicitly agent-origin, because its finite-type cohomology input is an agent-written blueprint proof rather than the induction in 095U. The parent lem-kun-0f0c already records the correction of its assertion that arbitrary proper morphisms are finite type over a field; this item supplies the replacement uniform relative bound, not a new ground-field hypothesis.

The tempting cor-weil-pbc-geometric-fiber-finite is not sufficient: its coefficients are a finite ring and a finite module sheaf. Likewise thm-fin-proper-case assumes constructibility, a base of finite type over a field, and invertible coefficient exponent. Neither was used. Instead step 5 writes out the proper-base-change stalk computation from the bounded-below abelian theorem and the exact-sections geometric-point lemma. That computation is not packaged as another node: it is a short consequence of existing statements and definitions.

## Not duplicates

No new nodes were created. Searches of the whole DAG for 095U, 0DDF, proper-base-change-stalk, dimension bounds and geometric-fibre cohomology, and blueprint_refs.py searches for cohomological, proper base change stalk, geometric fibre, 0DDF and proper.*dimension identified the tools used below but no equivalent blueprint item. The nearest blueprint ancestor is lem-kun-0f0c; the item's from.place already names precisely its cohomological-dimension claim, and same_as remains empty.

## Unfinished work

None in this one-level split. The reused nodes retain their own existing statuses; this report does not claim their Lean proofs are complete. No Lean source, compiler, Lake, live project or launcher file was modified. The only packaging operation is the explicitly requested delivery dry run; nothing is pushed.

## Review by NB

I read the full statement and induction proof of Stacks 095U and its preceding stalk lemma 0DDF in etale-cohomology.tex. The source has no invertibility or constructibility condition, so it agrees with the item. I also read the fixed smooth-purity chapter, the Kunneth unit and the master lem-kun-0f0c proof. The local slopmaster2 blueprint has no corresponding lem-kun-0f0c file. There are no new-node sources to review.

For step 1 I read the statements of def-weil-geometric-point, def-pc-scheme-fibre, lem-pc-proper-base-change, def-weil-proper-morphism, lem-sc-fibre-dimension-after-base-change and lem-weil-pbc-dimension-supremum-local-dimensions. I checked the actual Stacks texts 01W4 (morphisms.tex, lemma-base-change-proper), 02FY (lemma-dimension-fibre-after-base-change, part 1) and 0B7I (topology.tex, lemma-dimension-supremum-local-dimensions). The base-change lemma needs locally finite type, supplied by properness of f. The point of Spec Omega is its only point, so its fibre is the whole T; its image in Y is y. The local-dimension equality, followed by taking suprema, gives the required global upper bound even without proving equality of the two global dimensions. I deliberately use the topological dimension at a point, not the dimension of a local ring; those differ for nonclosed points.

Step 2 uses exactly the inverse-image stalk isomorphism in lem-weil-pbc-inverse-image-stalk-germ and both directions of lem-weil-pbc-torsion-sheaf-characterizations. Its stalks are evaluated at arbitrary geometric points of T. The composite with i is still a geometric point of X. Thus every stalk is torsion and the converse characterization applies. No uniform exponent is introduced. This is an elementary consequence of those two statements, with the argument written out.

For step 3 I checked that def-weil-pbc-abelian-etale-sheaves gives the equalizer condition, and def-weil-pbc-etale-cohomology computes cohomology from the complex of sections. An object over the empty scheme is empty; its empty cover makes its abelian section group zero. The same applies to every term of a resolution. This proves the empty case directly and avoids applying the finite-type bound with the nonexistent integer dimension of an empty scheme.

Step 4 uses the statement and proof of thm-sc-finite-type-torsion-cd in its master blueprint file, the statement and proof of lem-kun-03qu-sep-closed in sk-prop-sf-cbc, and the statements of def-sc-etale-torsion-cd and def-kun-separably-closed. The theorem is phrased with dimension exactly e, not an upper bound d: I set e equal to dim T and only afterwards compare 2e with 2d. Nonemptiness and the finite bound make e a nonnegative integer. Algebraic closedness precludes nontrivial finite algebraic extensions, hence finite separable extensions. The torsion definition explicitly permits arbitrary elementwise torsion, so it applies to G without finite coefficients. The finite-type assumption comes from step 1 and c=0 from the point lemma; no properness assumption on the total space over the original base is misread as a field hypothesis.

For step 5 I checked the precise abelian bounded-below statement of thm-weil-pbc-bounded-below, prop-weil-pbc-inverse-image-exact, both clauses of lem-weil-pbc-geometric-point-pullback-stalk, and the full resolution formulas in def-weil-pbc-direct-image and def-weil-pbc-etale-cohomology. F[0] is bounded below and has torsion cohomology, f is proper, and the square uses X times_Y Spec Omega, with the actual inverse-image sheaf G. Exact inverse image commutes with homology. The point lemma requires an algebraically closed field, which is exactly our geometric-point convention. Exact global sections commute with kernels and cokernels. On the other side, a_*J computes Ra_*G by the cited definition, and its sections over P are J(T) by the cited direct-image formula. These statements establish the whole stalk isomorphism; no preservation-of-injectives theorem or derived-composite comparison is being tacitly invoked. In particular I did not cite the finite-coefficient stalk formula as if it asserted the arbitrary-torsion formula.

Step 6 applies the actual morphism-isomorphism criterion of lemma-weil-pbc-geometric-stalk-conservative to the unique map to the zero sheaf. Each stalk map is an isomorphism because step 5 made its source zero. This also handles Y empty. All off-unit statements used as tools are declared in split_report.tool_uses; they supply generic geometry, cohomology and stalk facts, rather than replacing a step of the unit's Kunneth route.

I tested d=0 (only positive-degree vanishing), empty X and empty fibres, nonreduced zero-dimensional fibres, characteristic-p torsion, and an arbitrary non-quasi-compact base with a uniform bound d. The proof never assumes reduction, smoothness, a common torsion exponent, or invertibility. The bound does not claim vanishing in degree 2d; proper curves can have nonzero H^2 with prime-to-characteristic coefficients. A dependency traversal from the finite-type theorem and proper-base-change theorem found no path back to this item. All cited nodes are existing unmerged nodes, and citations.json quotes their statements verbatim. B1-B10 introduce no new-node obligations; C1-C8 are addressed by the explicit citations and tool declarations; D1-D5 by the written fibre, torsion, resolution and stalk arguments; E1-E7 by the hypothesis and small-case checks above. The principal correction during review was to separate empty fibres and use their sheaf axiom, rather than treat bottom dimension as a natural number.


## Second reading by NB

Item statement: checked hypothesis by hypothesis against Stacks 095U, etale-cohomology.tex, lemma-cohomological-dimension-proper, and 0DDF, lemma-proper-base-change-stalk; PASS. Properness, uniform fibre dimension, arbitrary elementwise torsion and strict inequality q>2d agree; no ground-field, constructibility or invertibility condition is needed.

Step 1: opened all six cited node statements and Stacks 01W4 (lemma-base-change-proper), 02FY (lemma-dimension-fibre-after-base-change), part (1), and 0B7I (lemma-dimension-supremum-local-dimensions); PASS. Properness supplies finite type and therefore the locally-finite-type hypothesis. Since P has one point, its scheme-theoretic fibre is T itself; pointwise dimension equality gives the global upper bound by taking suprema. This uses dimension at a point, not local-ring dimension.

Step 2: opened both cited statements, inverse-image-stalk-germ and torsion-sheaf-characterizations, and Stacks 03Q1 (lemma-stalk-pullback), part (3); PASS. At every geometric point of T the inverse-image stalk is a torsion stalk of F. The converse characterization gives torsion of G without a common exponent. The step is elementary from these exact statements.

Step 3: opened abelian-etale-sheaves, etale-cohomology and the newly cited etale-site definition; FIX. Joint surjectivity makes the empty family a covering of an empty object. Its equalizer is the zero group, so all sections of every resolution term vanish. This supplies the elementary empty-fibre case without assigning a natural-number dimension to an empty scheme.

Step 4: opened the statements of separably-closed-point vanishing, separably-closed, etale-torsion-cd, finite-type-torsion-cd and algebraic-closure, and the master blueprint files thm-sc-finite-type-torsion-cd.md and lem-kun-03qu-sep-closed.md; FIX, expanded the algebraically-closed implication. The finite-type theorem is applied with dimension exactly e=dim T, c=0, and the arbitrary torsion sheaf G. Nonemptiness and the finite bound imply e is a nonnegative integer; q>2d implies q>2e. The proof of the cited point lemma is not used as an unstated interface.

Step 5: opened all five cited statements, in particular both clauses of geometric-point-pullback-stalk and the full injective-resolution formulas of direct-image and etale-cohomology; checked against Stacks 0DDF (lemma-proper-base-change-stalk), 03Q1 (lemma-stalk-pullback), 04JN (remark-stalk-pullback), and 04JQ (lemma-equivalence-abelian-sheaves-point); PASS. F[0] is bounded below with torsion cohomology and the square is cartesian with proper f. Exact inverse image computes cohomology sheaves; exact sections over P commute with kernels and cokernels. A bounded-below injective representative J is K-injective as supplied in the direct-image definition; sections of a_*J are sections of J on T term by term. This proves the required stalk isomorphism without assuming finite coefficients or preservation of injectives by a_*.

Step 6: opened geometric-stalk-conservative and checked its isomorphism criterion against the map R^qf_*F to the zero sheaf; PASS. Every geometric stalk is zero by step 5, including vacuous conservativity when Y is empty.

New nodes: none; B1-B7, duplicate pruning and new-leaf provenance require no new-node repairs. Independently ran msearch.py grep for rightDerived.*(isZero|eq_zero)|IsProper.*cohomology (zero hits), Loogle for "etale", "cohomology" (zero hits), and LeanFinder for right-derived pushforward vanishing above twice relative Krull dimension (eight generic derived-category t-structure hits, none giving this bound). Actual outputs remain in searches.jsonl and are recorded in the item. The slopmaster2 CohomologicalDimension.lean theorem subsingleton_H_of_two_mul_add_lt, lines 44-51, has a literal sorry and is not a finished attachment; its specialization does not prove this relative theorem.

Small cases: checked F=0, empty X, empty Y, empty fibres, d=0, a point over an algebraically closed field, and d=1. The argument gives positive-degree vanishing for zero-dimensional fibres and only q>2 for curves; it does not kill possible degree-2 cohomology. Nilpotents and characteristic-p torsion are never excluded. An arbitrary non-quasi-compact Y causes no problem because the argument is stalkwise with the given uniform bound. Dependency traversal through every proof and statement dependency found no path back to this item. No definition or target statement is changed.

Changes: added the etale-site citation and jointly-surjective empty-cover argument to step 3; expanded and cited the algebraically-closed-to-separably-closed argument in step 4; added two full verbatim citation quotes and updated proof_deps; recorded the three independent searches. All other steps, the statement, blueprint route and first worker's review are retained. The worker's split_report.tool_uses entries are declarations for maintainer assessment, as explicitly allowed by tools/review_split.py lines 99-102; no maintainer-owned top-level tool_uses field was written. Delivery dry run and push follow this second reading.
