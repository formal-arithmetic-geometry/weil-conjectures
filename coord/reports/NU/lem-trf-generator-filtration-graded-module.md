# Stage-1 report: lem-trf-generator-filtration-graded-module

## Files written

- dag/nodes/sec-trace-formula/lem-trf-generator-filtration-graded-module.json: statement, split into seven elementary steps; Mathlib verdict no match for the complete statement.
- citations.json: seven entries, one for every occurrence of a cited node in a proof step; each quote was checked as a literal substring of its node's statement.
- report.md: this report.

There are **0 new nodes and 0 new Mathlib leaves**. The existing sandbox item was identical to the live item and had no proof or report. I retained its statement, metadata, citations and inherited searches. I read the three pre-existing NU search-log records and their results rather than repeating those queries, then completed the missing LeanFinder search and a second conceptual phrasing. All added search entries are taken from searches.jsonl, with exact tool/query text and actual recorded outcomes.

## Attachments

None. Searching lean/WeilConjectures for the blueprint tag, generator filtration, ReesModule and module homogenization did not find a declaration giving the item. The project Dehomogenization and PopescuWeakHomogenize files concern ring/localization constructions and equations, not the specified generator-filtration module. MinimalGradedPresentation assumes finite graded target data; it does not construct this module.

## WANTED

None. The relevant Stacks sources are present and were read.

## Corrections and source comparison

The imported statement is correct; no hypotheses, objects, or conclusions were changed. The item was an unsplit input created for the valuation finite-presentation argument. I supplied the omitted construction and its checks, rather than introducing a new lemma for each clause.

I read More Algebra Tag 053E, label lemma-flat-finite-type-valuation-ring-finite-presentation (more-algebra.tex:5967 onward), including its use of homogenization, removal of torsion and the graded module input. I also read Algebra Tag 052N, label lemma-homogenize (algebra.tex:13730 onward), including its quotient presentation and the sentence “Some details omitted.” The present item is the explicit generator-filtration alternative: it constructs finite formal polynomials inside the coefficient module and therefore proves torsion-freeness directly. The source does not literally use this construction, so proof_origin is honestly marked agent. No theorem about homogenized relations or homogeneous localization is assumed in this proof; the neighboring filtered-module-evaluation-presentation node handles the later evaluation/presentation step.

The current blueprint in literature/blueprint/latest was read at lem-trf-local-term-locality and sk-i-curve-zero, together with the DAG unit/chapter records. The item serves the existing valuation finite-presentation input under the ancestor's proof (1)--(2), normal-cone specialization branch. It changes no unit or chapter route. Blueprint searches for homogenization, filtration, generator filtration and 053E found no blueprint node stating this construction; blueprint.same_as remains []. This is not the key statement of its unit, so no unit realization fields were edited.

## Unfinished work

None within the stage-1 assignment. No Lean was written, and no compiler, Lake, or local DAG validation tool was run.

## Not duplicates

There are no newly created nodes and therefore no new/existing same-tag pairs. I nevertheless read the neighboring 053E statements: lem-trf-valuation-finite-type-module-presentation concludes finite presentation over a valuation base; lem-trf-valuation-flat-finite-module-presentation is its essentially finite type local version; lem-trf-local-graded-flat-module-finite-presentation assumes a finite flat graded module; lem-trf-filtered-module-evaluation-presentation proves the evaluation quotient and presentation descent. None states the present construction. The ideal-power Rees single-degree-generation node assumes its finite Rees module as input and concerns eventual multiplication surjectivity, so it is also different.

## Review by NU

I checked delivery-errors B through E against the written node and the open sources. No new statement-only node was needed: every calculation below is a short expansion in a span, formal coefficient sum, or monomial product. In particular the proof never imports the quotient construction of 052N as an unproved theorem, never uses freeness of any F_dM, and never claims that an infinite direct sum is finite over A. Finite generation is over P and follows from an explicit identity.

Step 1 uses no external theorem: the inequalities on the multi-index give F_dM contained in F_(d+1)M, and multiplication by b_i increases the monomial degree by one. A-linearity follows from the given commutative B-module structure. Step 2 cites def-weil-finitely-generated-module for the finite B-linear expression, def-weil-pbc-finite-type-algebra for coefficients being polynomials in the specified generators, and def-weil-pbc-mv-polynomial-ring for their finite monomial expansions. I opened all three nodes: their statements give precisely those assertions. Choosing the maximum over the finitely many degrees proves exhaustivity without a Noetherian hypothesis.

Step 3 cites only def-weil-pbc-mv-polynomial-ring for the unique finite coefficient representation of p. Its action is constructed by an explicit formula, not an appeal to a polynomial-ring universal property into a potentially noncommutative endomorphism ring. The degree estimate is proved by multiplying each spanning vector; all new exponents and supports stay finite. Step 4 cites the same polynomial definition, specifically its multiplication by addition of exponents. The displayed composition identity, checked on a single coefficient, proves associativity for all polynomials by finite distributivity. The zero, one, addition and A-scalar laws are included explicitly. Thus no uncited commuting-endomorphisms theorem is hidden.

Step 5 cites that polynomial definition for homogeneous monomial expansion. The internal module grading follows from literal coefficient extraction in finite formal polynomials, and the action's degree shift is already displayed in Step 3. Negative module components are zero. Step 6 cites def-weil-finitely-generated-module only for the meaning of generation; its substance is the written identity X_0^(d-|alpha|) X^alpha (m_j t^0) = b^alpha m_j t^d. The bound |alpha| <= d makes its exponent nonnegative. Step 7 uses the inline definition of torsion-freeness from the item, and proves it by extracting every coefficient; it needs no theorem about flatness or preservation of torsion-freeness under direct sums.

For every cited use I checked the exact quoted sentence in citations.json against the live node's statement. No citation relies on the proof rather than the statement of another node. All proof uses belong to the three existing definition nodes already in stmt_deps, so there is no new cycle or off-unit theorem dependency. Each proof step is below 700 characters; no long step hides a separate lemma.

I tested n=0 (empty multi-index product 1, B generated by constants, X_0 shifts degree), r=0 (M=N=0, empty generating list), d=0 (m_j in F_0), the zero coefficient ring/module, redundant or zero generators, and A a domain with nonzero torsion-free M. No independence of the m_j or injectivity A -> B is used. Non-domain rings satisfy all construction clauses; only the final torsion-free clause assumes a domain. Torsion in M over a domain is deliberately permitted until that final conditional clause. These checks found no statement dispute to report.

The Mathlib hits were read: FilteredAlgebra/Basic defines a filtration, Filtration uses decreasing ideal filtrations, GradedAlgebra/FiniteType gives homogeneous algebra generators, HomogeneousLocalization gives localized algebra generators, MvPolynomial/Homogeneous grades polynomials, and finrank_directSum assumes a finite index type. None is an exact or one-line specialization giving this increasing generator-filtration P-module together with the stated generators and torsion-free clause.
