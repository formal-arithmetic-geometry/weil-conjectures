# Q109: lem-trf-point-system-insertion-composition

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-point-system-insertion-composition.json`: statement split into seven proof steps; statement and statement dependencies retained. The item is not a Mathlib leaf.
- No new nodes, no new definitions, and no Mathlib leaves.
- `citations.json`: twenty exact statement quotations, one for every cited node in every proof step.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and point/insertion/composition terminology, and inspected the available pro-etale composition modules by their names and section formulas. They supply generic comparisons, not the simultaneous finite/completed coefficient normalization, semilinear whole-system insertion and unbounded localization assertion. No sorry-free project declaration states this item.

## WANTED

None. The proof uses sources already present and existing DAG statements.

## Audit and changes

The item was unsplit with no proof. Its statement is coherent and is retained exactly. The argument is an agent deduction from Stacks `sites.tex`, Tag 03CB (`lemma-composition-morphisms-sites`), the constant-sheaf definition Tag 0H7J (`example-constant-sheaf`), and the existing more precise DAG tools. I read both Stacks passages with their adjacent text and the current blueprint `main-20261015/.../sk-thm-trace-transport/thm-trf-l-function-euler-product.proof.md`, Step 1, Global powers. The blueprint only asserts the global composition compatibility; it does not itself prove this system refinement. Accordingly `proof_origin.by` is `agent`, not `document`.

The proof explicitly separates reindexing, coefficient normalization, scalar restriction, the specified tensor compositor, insertion through transitions, the chain equation, and localization. I did not identify an arbitrary natural isomorphism with the specified compositor merely because their functors agree. The site generator normalization and the adjunction-normalized tensor comparison identify it. I did not apply finite-coefficient naturality to a map between two different coefficient rings. Step 5 checks the semilinear transition on underlying abelian sheaves, then checks its tensor-unit formula using coefficient reduction. I did not infer equality of derived morphisms from evaluation. Equality is proved as a natural transformation on complexes of entire towers and then localized using full faithfulness on natural transformations.

I searched the whole DAG for the Stacks tag 03CB and for reindexing, inverse-image composition and localization. This found `lem-trf-site-inverse-image-composition-generators`, `lem-trf-constant-coefficient-composition`, `lem-sf-proetale-tensor-composition-unit`, and `lem-weil-pbc-localization-universal-property`. I opened their complete statements, along with all other statements cited by the proof. The more general finite-system pullback coherence node was inspected but is unnecessary; the present proof constructs the transition compatibility directly. Blueprint searches for insertion, point insertion and coefficient composition found no blueprint node stating the complete item. The item's nearest blueprint ancestor remains `thm-trf-l-function-euler-product` and its existing precise `from.place` is retained.

Actual Q109 Mathlib searches are appended to the inherited search history and logged in `searches.jsonl`: LeanFinder with two phrasings, LeanSearch, Loogle `SheafOfModules.pullbackComp`, and grep for insertion and `pullbackComp`. All services responded. I read the returned types and the source of `SheafOfModules.pullbackComp` and its conjugation lemma at `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:167-181`. That declaration is the generic module comparison, not the point-system assertion. The adic-completion hits concern algebraic module quotients, not sheaves with arbitrary semilinear strict transitions. Existing inherited searches and their provenance remain intact.

## Not duplicates

No new nodes. All auxiliary results are citations of existing nodes. In particular the existing constant-coefficient composition nodes are reused, not recreated.

## Review by Q109

I checked the following against the open node statements and the sources, rather than against their proofs alone.

1. `lem-weil-proetale-isomorphism-inverse-image` supplies the actual site-reindexing equivalence and its naturality. `lem-sfb-proetale-object-inverse-image-restriction` supplies the stronger graph-coprojection normalization that reindexing alone does not state. Its hypothesis holds because each power of an automorphism is an object of the pro-etale site. `lem-trf-site-inverse-image-composition-generators` states exactly the nested-generator formula and equality detection used to identify the canonical compositor. The graph calculation uses the two fibre-product projections, not an assumption that every section after sheafification has one colimit representative.

2. `lem-trf-constant-coefficient-composition` gives the finite-ring identity with the inverse orientation; I verified that multiplying by its inverse gives the displayed orientation for d. The finite rings A_n meet its finiteness hypothesis. Part (3) of the isomorphism-inverse-image statement gives reduction naturality. `def-weil-inverse-image-pullback-comparison` actually states the completed projection formula, and part (2) of the isomorphism lemma gives preservation of its limit. `def-pur-sheaf-inverse-limit` computes the limit sectionwise, so equality after all pi_n is legitimate for sheaf maps into that limit. This does not treat the completed ring sheaf as a discrete constant sheaf.

3. `def-pc-sheaf-restrict-scalars` says explicitly that restriction leaves underlying sections unchanged and changes only the scalar action. `lem-coef-semilinear-derived-sections` states the whole-system category and componentwise morphisms and exactness. The proof writes both scalar actions and uses the projection identity of step 2 to equate them. All b and t components commute with the original v_n by naturality on underlying maps. This is an elementary assembly step, not a new lemma about arbitrary derived evaluations.

4. `lem-weil-sheaf-scalar-extension-ring-iso` gives the inverse of the specified unit insertion. `lem-sf-proetale-tensor-composition-unit` states both its pure-tensor formula and its adjunction compatibility and uniqueness. The finite coefficient identity of step 2 verifies that node's prescribed composite coefficient identification. `lem-weil-pbc-proetale-derived-pullback-composition` fixes the derived comparison by the termwise comparison on K-flat representatives. Exactness of these isomorphism pullbacks ensures that this is the same localized comparison; no assertion of flatness of coefficient reduction is needed.

5. `lem-trf-point-sheaf-insertion-calculus` gives the exact finite-ring section insertion, its linearity and naturality, and its chain formula. It applies to every finite commutative A_n and every positive power of the chosen arbitrary automorphism. For transitions between different A_n, I deliberately use naturality of restriction, colimit insertion and sheafification on underlying abelian maps, then the balanced tensor formula of `def-pur-sheaf-tensor-product`. The two transition paths are written explicitly as v_n(x) tensor rho_n(1), which is v_n(x) tensor 1. There is no use of normalization of the system or surjectivity of a transition.

6. The same finite insertion-calculus statement gives the section cocycle, which becomes the claimed inverse-image cocycle after conjugating by j as verified in step 4. This step is elementary substitution and extensionality, with the actual differential and transition equations already established in step 5. It retains the whole tower. It is not a new node repeating a clause of the item.

7. The exactness asserted in `lem-weil-proetale-isomorphism-inverse-image`, componentwise exactness asserted in `lem-coef-semilinear-derived-sections`, and exact sections asserted in `lem-weil-point-proetale-sections-exact` imply that these degreewise functors preserve quasi-isomorphisms. `lem-weil-pbc-localization-universal-property` explicitly gives descent of natural transformations, preservation of composition, and equality detection after precomposition with localization. Its hypotheses apply to the ordinary unbounded localization used here. Hence I_r is natural for every derived system morphism, with no appeal to evaluations detecting equality.

I checked zero systems, identity h, the smallest level n=1, repeated powers, noncartesian systems with zero transition maps, and complexes with nonzero terms in arbitrarily high and low degrees. For h=id all reindexing and scalar-restriction comparisons are identities and the insertion reduces to identity under j. For zero transitions both paths of the transition calculation are zero. No proof invokes finite free models, resolutions at the level of evaluated systems, or a bound on cohomological amplitude. Restricting sections to R only uses its quotient action at each level. The n>=1 convention is retained, rather than silently using the n>=0 index of a background tower definition; shifting this index changes none of the explicit maps.

Against delivery-errors B-E: there are no new statements to hide proof sketches in or duplicate; every use is quoted verbatim in citations.json; no tag-only citation supplies a missing theorem; no claimed elementary step hides a separate non-elementary identification. I checked each non-elementary step's length: all are below 2000 characters. The generic cross-unit tools are declared in split_report.tool_uses and explain their use within the unit's fixed Global powers route. No chapter or unit record is changed, no source-route substitution is made, and no SGA source is used.

## Unfinished work

None in the one-level split. The existing dependency nodes remain responsible for their own proofs. The required server dry run and delivery are performed after this report is written.
