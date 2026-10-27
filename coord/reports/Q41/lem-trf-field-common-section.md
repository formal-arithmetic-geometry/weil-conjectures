## Worker report

Files written:
- dag/nodes/sec-trace-formula/lem-trf-field-common-section.json: statement, split using three existing Mathlib leaves; no Mathlib match for the whole assertion.
- citations.json: one verbatim statement quotation for each node used by each proof step.
- report.md and the command-generated searches.jsonl: delivery report and actual search log.

New nodes: 0. New Mathlib leaves: 0. The three existing leaves used are lem-trf-vector-subspace-complement, lem-trf-equal-dimension-linear-equivalence, and lem-weil-pbc-idempotent-charpoly-rank-nullity.

Attachments: none. Searched lean/WeilConjectures for the exact blueprint tag and for common complements, common sections, and simultaneous IsCompl assertions. No project declaration states this item. Individual splitting statements do not give compatibility with the second surjection.

WANTED: none. The source is present.

The source, Stacks Tag 0FJK (more-algebra.tex, lemma-homotopic-surjections, final paragraph), explicitly omits the field linear-algebra argument. The imported item had no proof; it is now filled by a graph construction, rather than by moving the common-complement assertion to another node. Its statement, hypotheses and stmt_deps are unchanged. The proof is marked agent-written because the source does not provide these details. The current latest blueprint ancestor proof (lem-trf-local-term-locality, (1)--(2)) follows the contracting-correspondence theorem; the existing blueprint.from chain records how this algebraic input arose below it. Neither chapter nor unit is changed, and this item is not the unit's key node.

Unfinished work: none for this split. This is stage 1 only; no Lean files were written or compiled.

## Not duplicates

No new nodes were created. The DAG searches found the existing complement and equal-dimension leaves in this unit and the existing rank-nullity leaf in sec-proper-base-change. They were reused. Whole-blueprint searches for common section, common complement, equal-dimensional and rank-nullity found no blueprint node stating this item; same_as remains empty.

## Review by Q41

I read Stacks Tag 0FJK in more-algebra.tex, including the full proof of lemma-homotopic-surjections and its last paragraph. The claim there is the existence of a common summand for two surjections; the field case has no infinitude hypothesis. I checked our section formulation is its consequence by taking the inverse of the first restriction. I also read the chapter/unit records and their current latest blueprint files, and the latest lem-trf-local-term-locality proof. The existing algebraic subproblem is below that unit route. There is no source error or statement dispute here.

For step 1 I opened lem-trf-vector-subspace-complement and lem-weil-pbc-idempotent-charpoly-rank-nullity and read their full statements. The former supplies unique direct-sum decompositions over every field without a finite-dimensionality assumption. Projection of the finite coordinate spanning family therefore proves finite-dimensionality of each subspace directly; no unquoted inheritance theorem is used. The latter states precisely image dimension plus kernel dimension equals source dimension. Both a and b have the given surjectivity and the same finite-dimensional source and target, so their image dimensions agree and finite natural-number cancellation gives equal kernel dimensions. The standard vectors give finite spanning even for empty coordinate sets.

For step 2 the complement statement is applied to I inside each kernel, not to a quotient or to an unidentified ambient space. The two projections are linear by uniqueness of direct-sum decomposition, with exactly the images and kernels written in the step. Both their source and target are finite-dimensional by step 1. Thus the rank-nullity statement supplies both displayed equations. The directness of I+P_1+Q_1 is proved by moving y into P intersect Q and using the two chosen complements; it is not cited as an additional theorem.

For step 3 I opened lem-trf-equal-dimension-linear-equivalence. Its full statement supplies a bijective linear map between arbitrary finite-dimensional spaces of equal dimension over the same field. Those hypotheses hold for P_1 and Q_1 by steps 1 and 2. The proof then explicitly checks closure of the graph, its intersections with both kernels, and both spanning formulas. This is where the substance of the common-complement construction is carried, rather than a citation of the item's own conclusion. I checked that inverse e exists also when P_1=Q_1=0.

Step 4 uses only the complement statement, now for P+Q inside V. It gives a remainder R disjoint from P+Q. Moving r into that intersection proves that U=D+R has zero intersection with each kernel; the two sum equalities are supplied by the explicit formulas in step 3 and V=(P+Q)+R. The cited complement theorem says exactly the decomposition needed, and imposes no additional field hypothesis.

Step 5 is elementary assembly from the complements already proved: lifting an arbitrary w, then subtracting its kernel component proves surjectivity of both restrictions; their zero kernels prove injectivity. Defining q by the unique preimage proves additivity and scalar compatibility, and the written inverse for bq verifies its isomorphism clause. No general inverse-function or splitting theorem is hidden here. The cited statements for all previous steps were copied verbatim into citations.json; proof_deps is exactly the union of uses, and all three dependencies are existing Mathlib leaves with no dependency back to this item.

I read the three leaf sources in Mathlib: Submodule.exists_isCompl at LinearAlgebra/Basis/VectorSpace.lean:280-282; LinearMap.finrank_range_add_finrank_ker at LinearAlgebra/FiniteDimensional/Lemmas.lean:173-176; FiniteDimensional.nonempty_linearEquiv_of_finrank_eq at LinearAlgebra/Dimension/Free.lean:239-242. Their statements agree with the corresponding DAG statements. Search results for individual splittings (LinearAlgebra/Finsupp/Pi.lean:171-191) and unique sums of already complementary spaces (Projection.lean:235-242) do not prove simultaneous existence; the finrank/disjointness criterion likewise still requires construction of the common subspace. I retained the imported search history and appended the actual Q41 queries from searches.jsonl, including the second phrasing. No query or result was invented.

Small cases: for m=0 take q=0 and use the unique automorphism of the zero space; n=0 forces m=0. If the kernels agree, P_1=Q_1=0 and the construction chooses an ordinary complement. For transverse one-dimensional kernels in F_2^2, the graph is span((1,1)), which is complementary to both coordinate axes; the subtraction formulas remain valid in characteristic two. The argument never selects a scalar outside a finite exceptional set and does not divide by 2. All five proof steps are below 2000 characters; none hides an additional non-elementary comparison or sublemma. Against delivery-errors B--E I checked self-contained statements, preserved source metadata, exact citations, no duplicate or clause node, acyclicity of the cited leaves, and every hypothesis of each application. I corrected the initially implicit finiteness and dimension-additivity arguments by writing the projection arguments explicitly.
