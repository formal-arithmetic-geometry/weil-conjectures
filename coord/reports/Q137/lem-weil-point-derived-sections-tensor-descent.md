## Worker report

Group Q137, item lem-weil-point-derived-sections-tensor-descent; stage 1 only, direct delivery, 2026-10-21.

Files written: dag/nodes/sec-smooth-purity/lem-weil-point-derived-sections-tensor-descent.json (statement, split, no Mathlib match), report.md, citations.json, and sandbox-only search records/results and preparation script. There are **0 new nodes and 0 new Mathlib leaves**. The item's statement and stmt_deps are unchanged. Its proof now has seven steps and proof_deps is exactly their uses union. No repository file or Lean file was written and no compiler was run.

Attachments: none. The whole-library tag search found no declaration for this item. The nearest project result, AlgebraicGeometry.Etale.pointSectionsDerivedBaseChangeIso at lean/WeilConjectures/SixFunctors/Etale/Derived/PointFiberAlgClosed.lean:96, is about constant coefficients on the small etale site. It does not state this result for completed coefficient sheaves on the pro-etale site, or its derived-counit normalization and arbitrary K-flat resolution formula. It is not an attachment.

WANTED: none.

The original node had a complete statement and no proof. I retained that statement, its metadata and inherited searches. The five searches actually run by Q137 are appended without altering the inherited records. Two semantic phrasings, Loogle, source grep and LeanSearch found general exact-functor/localization declarations and sheaf APIs, not the entire item. I read ExactFunctor.lean:36-59 and Localization/Predicate.lean:350-360. The generic localization theorem is already lem-weil-pbc-localization-universal-property, so no duplicate Mathlib leaf was made. The whole-blueprint search for sections-tensor returned no node; the exact-functor search returned the existing general derived-functor notions. The sandbox was initially empty of item files, so there was no previous split or report to replace.

Nothing remains unfinished in the one-level split. The cited existing nodes retain their own proof obligations; they were not copied or modified.

## Sources and route

I read the chapter and unit records, the three-level rules, GOAL.md, and both copies of delivery-errors B-E. The node belongs to the coefficient-compatibility route of sk-thm-sf-compatibility. Its blueprint ancestor is def-weil-finite-coefficient-point, whose main-20261015 source is literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sf-admissible/def-weil-finite-coefficient-point.md. I read its final stagewise-colimit paragraph and the master counterpart. The updated DAG ancestor separates the fibre functor definition from its equivalence assertion; this item only proves the scalar comparison used in the stagewise construction.

For the mathematics I read sites-cohomology.tex, lemma-derived-base-change (06YY) and its proof: a K-flat resolution with flat terms computes the left-derived pullback, using derived.tex lemma-find-existence-computes (06XN). I also read derived.tex lemma-right-derived-exact-functor (015F) and categories.tex lemma-properties-left-localization (04VG), and the Mathlib natural-isomorphism lifting code which supplies the categorical enhancement not asserted in the Stacks lemma alone. The extra counit and inverse-arrow calculations are written by this worker, so proof_origin.by is agent. No SGA source is used.

The split_report declares the general point-exactness, resolution, change-of-rings, and K-flat left-derived-counit nodes as tools. They supply the generic exactness/derivation mechanisms for the unit's own coefficient route. They do not change that route. The exact-functor factorization and localization universal property are existing Mathlib leaves.

## Review by Q137

I opened every node cited in the proof and compared its statement with the particular use; citations.json contains a verbatim passage for every step/node pair. There are no new-node sources to audit.

Step 1 uses the global datum solely for k being an algebraic closure, meeting the algebraically closed field hypothesis of lem-weil-point-proetale-sections-exact. That lemma explicitly covers modules over every ring sheaf and unbounded derived categories, so it applies to both completed sheaves, not just to constant discrete coefficients. The finite-free sections-tensor node explicitly identifies their coefficient sections with the valuation rings and explicitly asserts additive exactness of both scalar extensions. The exact-functor factorization node asserts preservation of quasi-isomorphisms and existence of the factored triangulated functors. I did not infer tensor exactness merely from a definition of flatness.

Step 2 uses lem-pc-kflat-resolution for an unbounded resolution with flat terms, lem-pur-derived-change-of-rings clause (1) for inversion of quasi-isomorphisms between K-flat inputs, and lem-pur-left-derived-from-kflat-class for the counit and its isomorphism on that class. These are precisely its two hypotheses. The counit is first a transformation on the homotopy category and is pulled back to complexes; the proof does not confuse these source categories. The exact functor on the homotopy category factors through the exact derived functor from step 1. Step 3 writes its naturality at q and isolates epsilon_C as a product of three isomorphisms. Thus no K-flatness of C or unmentioned restriction on its cohomology is needed.

Step 4 uses parts (2)-(3) of lem-weil-pbc-localization-universal-property, whose statement explicitly includes lifting transformations, preservation of invertibility, and uniqueness. The component of c is epsilon after the termwise factorization, so its inverse is the required normalized direction T_D to LT. I corrected a possible ambiguity in a proof by Kan-extension uniqueness alone: the proof here actually specifies this normalization on every representative.

Step 5 uses the finite-free node's natural chain isomorphism, not merely its objectwise tensor comparison. The localization result supplies naturality for every derived morphism. I checked the direction: theta^D is Gamma(c inverse) after tau, so its target is Gamma(LT K).

Step 6 defines rho_q = epsilon_P composed with LT(q) inverse. The existing derived change-of-rings node states precisely this resolution computation and its canonical comparison. Substituting counit naturality gives c_C = T(q) rho_q. The chain square then gives theta^D_C = Gamma(rho_q inverse) theta_P A(q) inverse. All three sources and targets agree. Applying that same identity separately to two resolutions proves independence without assuming a comparison chain map exists between them. The finite-free node supplies the chain naturality used in the substitution.

Step 7 obtains inverse-arrow naturality by multiplying the q square by B(q) inverse and A(q) inverse, then uses the f square. This yields the displayed roof formula with B(f)B(q) inverse on the left, in the order in the statement. Full naturality comes from localization, so the proof does not assume that the naive category of cochain maps itself has an Ore calculus. No extra roof-existence lemma is silently used.

Edge checks: E=L gives the rank-one multiplication comparison, with T and V canonically the identity and the counit normalization unchanged. For the zero complex every displayed map is the unique zero-object isomorphism. For a resolution q equal to the identity of a K-flat complex the formula reduces to Gamma(epsilon_P inverse) theta_P. A genuinely unbounded complex and a torsion module are both allowed: only the exactness already in the cited statements is used, never boundedness, constructibility, torsion-freeness of the input, or derived completeness. The restriction ell != p and the completed rather than discrete rings remain exactly as stated.

Against B1-B10: no new statement-only nodes, no new notions or leaves, no missing blueprint reference; source tags and their labels were read, all new search records came from msearch, and the nearest project declaration is not an exact attachment. Against C1-C8: all non-elementary uses are cited by their actual statements, definitions are not substituted for theorems, the tool uses are declared, and no new dependency is a parent/citer of the item. Against D1-D5: no clause is merely renamed as a new node; the proof contains the comparison construction, its normalization, and both explicit naturality calculations. Against E1-E7: hypotheses and coefficient categories were checked as above, formulas have matching objects and directions, and no source error or statement dispute was found. Every proof step is shorter than 2000 characters; there is no long hidden comparison lemma to extract.

## Not duplicates

No new nodes. All general tools are reused under their existing ids. In particular no new exact-functor localization, counit, or resolution-independence lemma was introduced.
