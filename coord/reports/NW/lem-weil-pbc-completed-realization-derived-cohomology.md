# Stage-1 report: lem-weil-pbc-completed-realization-derived-cohomology

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-completed-realization-derived-cohomology.json`: existing statement, split into five steps; no Mathlib match for the whole statement.
- `citations.json`: verbatim statement excerpts for all 13 step/node citations.
- `searches.jsonl`: search-command log, retained as produced.
- `report.md`: this report.

No new DAG nodes and no new Mathlib leaves. The statement and statement dependencies are retained verbatim. No unit or chapter file is changed. All writes are inside this item's sandbox; no Lean, compiler, Lake or repository git command was used.

## Attachments

None. Searching `lean/WeilConjectures/` for the blueprint tag and completed-realization notions found no declaration giving the entire item. `lean/Sheaf/Paper/IntegralStratifiedPerfectModels.lean` already constructs the ordinary and derived functors and proves ordinary exactness, but that file is outside the permitted attachment root and does not itself state both normalized comparison clauses. It is useful implementation context, not evidence for attaching this item as finished.

## WANTED

None. All documents used are already available.

## Problems found and corrections

The imported item had no proof. It is mathematically consistent as written: gamma is the specified normalized coefficient isomorphism, and the functor uses its inverse for scalar restriction. No statement dispute or hypothesis correction was necessary. The original source mentions Bhatt--Scholze's constructibility propositions; these explain the local models but are not an assertion of this exactness theorem for arbitrary modules. The proof is accordingly marked agent-written, assembled from the actual Stacks exactness and flatness results and existing generic DAG results.

A proposed source label for tensor products was corrected before delivery: Tag 03EQ is the flatness section, while the tensor definitions are Section 03EK. The source label for 05RU was also written with its actual name, definition-unbounded-derived-category. Neither correction changes the statement.

The original mathlib_searches records and their results are retained. The current search-command log adds LeanFinder, Loogle, grep and LeanSearch, with a second LeanFinder phrasing. I read the returned declarations and types: `AdicCompletion.map_exact` concerns algebraic completion of finite modules; constant/condensed sheaf hits lack this completed pro-etale coefficient functor; the second phrasing finds generic exact-derived-functor infrastructure, which the split already cites through existing Mathlib leaf nodes. None supplies the whole item by a one-line specialization.

## Not duplicates

No new nodes were created. Searches for Tags 093J, 093M and 015F and for constant exactness, completion flatness and completed realization found the existing nodes used below. Blueprint searches for completion flat, exact functor and completed realization produced no blueprint node stating this whole normalized realization theorem. The existing generic exact-functor nodes and completed-constant-sheaf-reduction are reused. No clause of the item has been repackaged as a new node.

## Review by NW

I read coord/brief-stage1.md, stages/1-dag.md, GOAL.md, the three route levels in SETUP.md, the worker role, and delivery-errors.md B--E in full. I read the proper-base-change chapter and unit and the current main-20261015 finite-extension statement and proof. The ancestor's integral-lattice sentence is the existing origin of this local-model branch; this split does not replace the unit's projective-line or finite-torsion route.

For the item I read Stacks sites-modules.tex lemma-constant-exact (093J) and lemma-completion-flat (093M), including the latter's Noetherian and arbitrary-site hypotheses and its proof. I read derived.tex lemma-right-derived-exact-functor (015F), which explicitly applies to unbounded complexes and says every complex computes the derived functor. I also read Bhatt--Scholze Proposition 6.6.11 and the definition of the locally constant perfect model immediately after its statement, and Definition 6.8.10/Proposition 6.8.11(3), including their proofs. These passages distinguish completed coefficients from a discrete constant coefficient replacement. There are no new nodes requiring separate source review.

In step 1, I opened lem-weil-pbc-finite-type-constant-exact: despite its name, its statement is for all modules over any commutative ring on a small site. It states precisely finite-limit and finite-colimit preservation. I checked def-weil-pbc-proetale-site supplies the small skeleton and universes, and def-sf-site-constant-module-functor really specifies the presheaf then sheafification construction and its action on linear maps. The sum-of-maps equality proves additivity directly. No finite-presentation assumption is smuggled in.

In step 2, I opened lem-weil-pbc-completed-constant-sheaf-reduction and read its exact statement: its first clause gives B flat over underline A, explicitly meaning preservation of short exact sequences under tensor. This is stronger than a definition of flatness and is the actual theorem needed here. T is an arbitrary scheme and A is commutative Noetherian as required. The positive indexing agrees exactly; no claim about limit exactness for arbitrary inverse systems is used. I opened def-pur-sheaf-tensor-product to check the sheafified tensor construction and wrote additivity on its local tensor generators. I read def-pc-sheaf-restrict-scalars and def-weil-sheaf-of-modules-category: the former keeps the underlying abelian sheaf and changes the action through gamma inverse; the latter specifies sectionwise kernels and sheafified sectionwise cokernels. Thus inverse scalar restrictions are explicitly inverse and preserve those constructions. Gamma's direction is A_T to B_T for this restriction, as in the item. Gamma is already specified in the hypotheses; the proof does not assume a separate existence or a constants-to-continuous-functions comparison without citation.

In step 3, I opened lem-weil-pbc-exact-functor-derived-factorization. It states preservation of quasi-isomorphisms, the representative isomorphism, a triangulated functor, and its specified shift compatibility. I also read the cited Mathlib ExactFunctor.lean implementation (mapDerivedCategory, mapDerivedCategoryFactors, CommShift and IsTriangulated). The hypotheses are exactly the additive finite-limit and finite-colimit preservation proved in steps 1--2. It covers unbounded derived categories; there is no bounded-below substitution and no injective or K-flat resolution requirement.

In step 4, I opened lem-weil-pbc-exact-functor-complex-cohomology: its comparison is induced by the kernel/image identifications, and its direction is H(FK) to F(HK). The step explicitly inverts it to match the item's direction, then uses the inverse of H(phi). I opened def-weil-abstract-derived-category for cohomology's localization factorization. I opened lem-weil-pbc-localization-universal-property: part (2) really descends natural transformations, and a natural isomorphism descends with its inverse. This is why naturality holds for derived morphisms as well as chain maps. Both precomposed functors invert quasi-isomorphisms; the step verifies this before applying the lemma. Scalar restriction changes none of the underlying cycle, boundary or quotient maps, fixing the coefficient normalization. No comparison theorem is hidden behind the word transport.

In step 5, I reread the factorization node's shift equation and termwise identity tau. A shifted degree-zero complex has just one possibly nonzero term, in degree minus r. Thus the single-object identification is a direct computation from the factorization and is marked elementary, with its cited generic theorem explicit. The shift equation identifies the composite with the factorization of the shifted complex itself. Naturality in M is inherited from these chain-level identities. This does not introduce a new lemma asserting one of the item's own clauses.

Small cases checked: M=0 and P=0; q arbitrary; r positive, zero and negative (the term is always in degree -r); an unbounded complex (only its three adjacent terms enter each cohomology calculation); I=0 whenever the adic-datum hypotheses permit it (the inverse system is constant); I=A and the zero ring/empty scheme (the completed coefficient algebra and realization are zero). No flatness or faithfulness of the ordinary A-module M is needed. No claim identifies the completed sheaf with the discrete constant ring sheaf. All five steps are under 2000 characters. The proof uses existing nodes, so no duplicate-tag pairs or new-node search obligations arise.

The server review_split check passed with zero new nodes before report preparation. The final delivery dry run and push are performed after this report is written.

## Unfinished work

None at stage 1. No Lean proof is claimed or delivered. The independent maintainer review remains the normal delivery review.
