## Worker report

Q113, stage 1, 2026-10-22. Item: lem-trf-point-exact-realization.

Files written:
- dag/nodes/sec-trace-formula/lem-trf-point-exact-realization.json: unchanged statement and statement dependencies; five-step proof, status split, proof dependencies, proof origin, blueprint realization and logged Mathlib searches.
- citations.json: thirteen step/node pairs, each with a verbatim portion of the cited statement.
- report.md: this report and direct-delivery review.

## New nodes

None. Zero new nodes and zero new Mathlib leaves. The existing DAG supplies the non-elementary prerequisites; making new versions of them would duplicate them. No unit or chapter record is changed: this item is not the unit's defining node.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for point exactness, exact realization, proEtaleConstantModulePullback and pointFiniteSections. No project declaration states all clauses of the item. Read lean/Sheaf/Paper/PointExactDerivedModel.lean as supplementary reference: exactness (line 123), preserves_constructible (182) and evaluation_restriction (201) all end in sorry (142, 192 and 212). They are not attachments, and the file is outside the required WeilConjectures attachment root in any event. No Lean file was written and no compiler was run.

## WANTED

None for this assembly. It uses existing DAG statements and the obtained Stacks and blueprint texts; it does not claim a new literature theorem.

## Corrections and scope

The live item was statement-only, with no repair note for this item and no prior sandbox node, report or citations. Kept the complete statement, canonical coefficient maps, unbounded quantifiers and no-K-flatness clause. The parent point-exact-derived-model already delegates this exact realization to the item; it cannot be cited as its proof. No parent is used and no compositor or transformation-descent assertion is silently assumed. The five steps separate exactness, localization, identification with specified total derived functors, bounded constructibility, and finite-point evaluation. No STATEMENT-DISPUTED issue was found.

The exactness of sections first has target Gamma(s,A_s)-modules. Step 1 explicitly restricts scalars along the constant-section map to A; it does not assume an unproved identification of those rings. Step 3 identifies the specified total pullback rather than merely constructing some functor on the localization. It records the actual map H_r(P) to H_r(K) for a K-flat resolution P to K. Step 4 applies an isomorphism theorem to a scheme automorphism, so does not incorrectly assume that geometric Frobenius is a k-morphism. Step 5 uses a theorem for finite cohomology rather than extracting that theorem just from a definition.

## Searches and blueprint

Read all results in searches.jsonl. The six actual Q113 searches comprise Loogle for CategoryTheory.Functor.mapDerivedCategoryFactors; grep for proEtaleConstantModulePullback|proetale.*exact|exact.*proetale; LeanFinder for exact constant-coefficient pro-etale point pullback and sections; LeanSearch for exact inverse image and point sections; a second LeanFinder phrasing for exact functors computing their total derived functor; and grep for mapDerivedCategoryFactors|mapDerivedCategory in Algebra/Homology/DerivedCategory/ExactFunctor.lean. Every service answered successfully. Both generic and point-specific phrasings were checked. Read the generic Mathlib definitions in ExactFunctor.lean, lines 36 and 41. Those provide the existing factorization leaf, not the whole pro-etale point assertion. The point-search hits concern generic site points, Galois-category fibers and etale algebra; they do not prove this item. Fresh records were appended verbatim by tool/query to the inherited searches, not substituted for them.

Ran tools/blueprint_refs.py ancestor on the item, which names lem-trf-frobenius-operator-compact-description. Searched the whole imported blueprint for exact functor, pullback constructible, pullback preserves, exact realization, isomorphism derived pullback and point sections, and searched DAG statements by the same concepts and Tag 015F. Read the ancestor's current main-20261015 .proof.md, especially the paragraph beginning “That action transports the pair”. The item realizes exact finite-coefficient point evaluation needed there via the exact-derived-model intermediary. No blueprint statement is identical to this combined assertion. The same_as list remains empty and from.place remains its already precise inherited place.

## Not duplicates

No new-node/existing-node pairs arise. In particular the generic exact-functor factorization, exact-functor total-derived identification, isomorphism pullback and sections-finiteness facts are cited by their existing ids rather than recreated.

## Review by Q113

I read the item and all twelve distinct statements cited in its proof, the current ancestor proof and the unit/chapter records, and checked the source texts with those statements open. The unit is sk-d-weil in the trace-formula chapter; this is a prerequisite of its Frobenius transport calculation, not a change of chapter route. Stacks derived.tex, Tag 015F, lemma-right-derived-exact-functor, explicitly treats the unbounded derived category and every complex; the left-derived dual has the corresponding universal property. Stacks homology.tex, Tag 010N, lemma-exact-functor, gives the exactness/additivity convention. I also read proetale.tex Tag 0982, lemma-w-local-strictly-henselian-extremally-disconnected, and Tag 098H, lemma-w-contractible-is-weakly-contractible. The existing small-site sections node explicitly states its conclusion on the small site and for module sheaves, so I use that statement, not an unjustified transfer of arbitrary sheaves between the big and small sites. The finite-point source is the obtained blueprint def-weil-finite-coefficient-point.md; its refined DAG statement specifies termwise sections and separates finiteness from the definition. I read the current main-snapshot finite derived-pullback definition and constant-exact proof as well. The latter's abbreviated presheaf-adjoint explanation is not used as a new lemma: exactness is taken from the existing exactness node's actual statement.

Step 1 uses def-weil-l-adic-coefficient-extension for finiteness of A, prop-weil-pbc-proetale-constant-ring-map for the actual canonical coefficient isomorphism and prop-weil-pbc-proetale-constant-exact for exactness and the commutative tensor comparison. Its hypotheses allow every scheme morphism and finite discrete commutative rings, hence apply to h^r and A at every n >= 1. The last cited statement, lem-weil-point-proetale-sections-exact, supplies module sections exactness for algebraically closed k. The extra restriction of scalars is elementary: it changes no underlying kernels or cokernels. Additivity is checked on addition of module morphisms. Thus this step is marked non-elementary for its cited exactness theorems, not elementary merely because it is an application.

Step 2 uses the statement of lem-weil-pbc-exact-functor-derived-factorization, a Mathlib leaf: its hypothesis is exact additive functors between abelian categories, established in step 1, and its conclusion is exactly quasi-isomorphism preservation and a natural factorization for every complex. It imposes neither boundedness nor flatness. Its full statement includes the factorization equation used here; the citation witness is a verbatim portion, not the only clause read.

Step 3 uses lem-weil-pbc-exact-functor-derived-functor, whose statement expressly identifies the factorization with both total derived functors through their Kan universal properties. The finite clause of def-weil-derived-pullback-tensor-hom states that exact inverse image computes the specified pullback on any representative; def-weil-pbc-proetale-operations explicitly defines it by exact termwise localization and states that applying it to any K-flat resolution yields a quasi-isomorphism to the termwise value. These statements justify identification with Q_r and its normalization, not an arbitrary natural isomorphism. The existing sections-exact node identifies induced evaluation. The displayed map from H_r(P) to H_r(K) is the image of the resolution map and is invertible by step 2; nothing in the argument assumes K itself K-flat. Naturality and comparison uniqueness are part of the cited total-derived-functor statement.

Step 4 uses def-weil-frobenius-detailed for the scheme automorphism and lem-weil-isomorphism-derived-pullback for the constructible conclusion and specified derived-pullback comparison. Checked that k has characteristic p, ell is distinct from p, n is positive, and h^r is an isomorphism. The lemma asks for ell invertible on the schemes, not that the isomorphism be k-linear. Its statement covers every representative of a bounded constructible object and supplies membership in D^b_c after inverse image. Combined with its displayed derived isomorphism, this is exactly preservation by Q_r. This is a generic tool used as a black box; the unit's Frobenius route is unchanged.

Step 5 uses clause 1 of def-weil-finite-coefficient-point for the precise definition K maps to Gamma(s,K) and clause 1 of lem-weil-point-sections-finiteness for membership in D^b_fin(A). Checked the same finite-field and finite-extension datum and the same constant scalar map. The inclusion of the full subcategory forgets only the finite-cohomology condition, so the ambient functor with comparison v restricts to the specified V. No equivalence of all sheaves on the pro-etale point with ordinary modules is assumed.

The item is unchanged mathematically. Each non-elementary fact is a cited statement; the only inline arguments are scalar restriction, additivity, taking powers of an automorphism, invertibility of a nonzero field element and substituting the already specified factorization. There is no newly introduced hidden lemma. All five steps are below 2000 characters individually; the whole assembly is 2666 characters. The off-unit generic tool applications are declared only in split_report.tool_uses for maintainer assessment, not authorized by a worker-written top-level tool_uses field.

I checked B1-B10: no new unsplit node or duplicate definition, the item introduces every object, TeX uses single backslashes after JSON parsing, all sources use tags and labels where applicable, actual searches and results are retained, and no sorried declaration is treated as finished. Checked C1-C8 against each citation, including small-site scope and unbounded scope. Checked D1-D5: the steps carry the assembly using pre-existing strictly independent tools; no new node restates a clause, no circular reference to the parent, and the omitted exact-functor comparison is supplied by the existing Kan-property theorem. Checked E1-E7 on n=1, ramified E, arbitrary positive r, the zero complex, an acyclic unbounded complex, and an unbounded non-K-flat representative. Exactness handles the latter two without extra resolution assumptions; finite output is asserted only for bounded constructible input. I did not replace pro-etale sections by an etale geometric stalk. There are no new statements requiring additional edge-case hypotheses and no SGA source is cited.

## Completion

Mathematical split and review complete. Server dry run and final direct push are the remaining delivery steps; their command output supplies the authoritative outcome.

First dry run: the citation gate requested longer witnesses for coefficient finiteness and the constant-ring isomorphism (minimum 40 characters). Expanded both to verbatim hypothesis-and-conclusion passages of their existing statements; no proof or statement changed.
