## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-stack-small-etale-comparison-calculus.json: statement item, now split in five steps; no Mathlib match.
- citations.json: one verbatim statement quotation per cited node and proof step.

## New nodes

None. Zero new Mathlib leaves. In particular I did not introduce new nodes for composition of comparisons, local quasi-coherence, flat comparison, or detection of an inverse by sheaf gluing.

## Attachments

None. Searches in lean/WeilConjectures for the exact blueprint tag, small-etale comparison, fibred categories, and related algebraic-space comparison terminology found no declaration proving this entire statement. The isolated torsor graph-evaluation docstring hit concerns a different comparison.

## WANTED

None. The sources used are present locally.

## Statement and reference audit

STATEMENT-DISPUTED: the imported tensor-pullback reference was ill-scoped. def-pc-module-pullback introduces a map of schemes and modules on its Zariski sites, whereas the expression a^*H_w here has algebraic-space small-etale domain and codomain. Replaced that reference by def-trf-space-etale-module-functors, which defines exactly this functor. Similarly def-weil-flat-morphism only defines flat scheme maps: the conclusion about flat algebraic-space maps now also cites def-sfb-space-morphism-properties, whose chart test defines that property. No mathematical hypothesis, conclusion, coefficient category, or formula changed. This is a definition-domain repair, not a stronger assumption on the stack or on H.

The imported proof was empty. Its statements remain valid with these scope corrections. No claim that H is globally quasi-coherent is made: local quasi-coherence of its scheme restrictions and flat compatibility are separate assumptions. The flat comparison proof in fact uses only the latter assumption, which is permitted under the stated stronger hypotheses.

## Searches and blueprint

Read coord/brief-stage1.md, stages/1-dag.md, SETUP.md including its three levels, GOAL.md, roles/worker.md, and the whole B–E checklist in coord/delivery-errors.md. The sandbox initially contained only dispatcher marker files, so there was no earlier split, report, or search log to retain. The live item and all its inherited search/provenance fields were retained. There is no repair-note file for this item.

Read the chapter and unit records and the newest literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The inherited ancestry places this auxiliary comparison calculus below direct-images (3), through the adequate-moduli and coherator route. No chapter or unit route was changed. blueprint_refs.py ancestor reports None for the inherited imported ancestry, so its null root and via chain were preserved, with a precise additional place describing this split.

Whole-DAG searches for Tags 075D, 076R, 0GQC, 0762 and comparison terminology found lem-sfb-fibred-fppf-space-module-comparisons. Its arbitrary-CFG, arbitrary-module comparison clauses generalize the first part of the item. Its final quasi-coherent-big-module clause does NOT apply to our arbitrary H; I have not used it. Also read the neighbouring big-etale restriction calculus, groupoid Hom lemma, local flat-comparison structure lemma and coherator statement to distinguish their scopes. Whole-blueprint searches for 'small etale comparison', 'flat base change property', '076R' and 'locally quasi-coherent' found no matching imported node. A broad comparison search gives generic derived/six-functor comparisons, not this ringed stack restriction statement.

Ran msearch.py for this item using LeanFinder twice with different phrasings, LeanSearch, Loogle, and source grep in AlgebraicGeometry. The exact query strings and actual returned names are retained in searches.jsonl and appended to mathlib_searches. Read Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:150–180 (pullbackComp at 167), and AlgebraicGeometry/Modules/Sheaf.lean:232–250 and 447–462 (pullbackComp at 241, restrictFunctorIsoPullback at 453). These are generic composition and Zariski open restriction, not the stack/test comparison or its local quasi-coherence and flat compatibility. Other search hits concern module flat base change or ring etaleness. No hit states the whole item. All services returned results; none was recorded as unavailable.

## Not duplicates

No new nodes. Existing generic comparison, atlas, and quasi-coherence statements are reused, rather than recreated.

## Review by Q73

I read stacks-sheaves.tex at lemma-comparison (075D), the module paragraph after equation-comparison-modules, equation-comparison-algebraic-spaces-modules (076R) and its following sentence, and lemma-compare-locally-quasi-coherent (0GQC), including its proof. I also read stacks-cohomology.tex at definition-flat-base-change (0762). These sources respectively give comparison coherence, its module/algebraic-space version, the chartwise quasi-coherence argument, and the scheme flat-comparison hypothesis. The source omits coherence verifications; the existing general fibred-fppf comparison node is cited for that work. There are no new-node statements to source or to review.

Step 1 cites the actual statement of lem-sfb-fibred-fppf-space-module-comparisons: it introduces arbitrary algebraic-space tests, the same two-isomorphisms, the adjoint comparison, identity, composition, naturality, scheme-test agreement and etale invertibility. Its category-fibred hypothesis holds for an algebraic stack and its module is on the fppf site we use, so no topology switch is being assumed. This is a specialization of an existing independent input, not moving the item's clauses to a newly created lemma.

Step 2 uses that same etale comparison and def-trf-algebraic-space's explicit identification of etale pullback with localized restriction. The statement of lem-trf-scheme-zariski-etale-quasi-coherent-equivalence gives local-presentation quasi-coherence for the associated etale module in the hypothesis. def-trf-space-quasi-coherent-module defines the arbitrary-site local-presentation condition. The proof spells out that the presentations and covers on each chart are presentations and covers of the corresponding slice of V_et; it does not assume a Zariski presentation directly on the stack. This is the argument of 0GQC, now in the explicit local-presentation convention.

Step 3 uses def-trf-algebraic-space for surjective etale scheme atlases. I checked the full statement of lem-trf-space-representable-etale-scheme-tests: two scheme-source maps to W have a scheme fibre product; etale maps and surjective etale maps compose. The statement of lem-trf-space-fibre-products-etale-covers supplies the base-changed surjective etale cover. Thus P is a scheme, r:P->V is a surjective etale chart and t:T->W is an etale chart. The definition in def-sfb-space-morphism-properties then gives flatness of the scheme map f:P->T in the square ar=tf. We do not assume that V times_W T is itself a scheme, or that a is scheme-representable.

Step 4 uses the exact composition law and etale invertibility in the general comparison statement, twice, to obtain c_r r^*c_a = c_f f^*c_t with the pasted two-isomorphism. The middle comparison c_f satisfies the input hypothesis because both P and T are schemes and f is flat. The source and target of the equation are displayed; cancellation yields an inverse after r-pullback without any tensor-exactness assertion. I read the statement of lem-trf-space-etale-module-pushforward-restriction and use only its explicit clause that etale tensor pullback is restriction, not its direct-image result. The scheme-test and cover nodes ensure the covers of arbitrary test A used for gluing exist and are scheme covers. The sheaf condition of def-weil-sheaf-of-modules-category glues the unique local inverse on sections; uniqueness on overlaps also gives module linearity and restriction compatibility. No separate non-elementary descent theorem is hidden in that final gluing argument.

Step 5 specializes the existing comparison's naturality in tests and two-isomorphisms to the canonical groupoid two-isomorphisms. It asserts flat invertibility only when the preceding hypotheses apply, and does not impose flatness on every groupoid map. This final specialization is elementary.

I tested identity arrows, composable identity arrows, H=0, empty source charts, and the identity presentation of a scheme. The formulas give the identity or unique zero map as required. For an empty space the sheaf category is terminal and the gluing assertion is vacuous. For arbitrary non-quasi-coherent H the first comparison conclusions still apply, while the quasi-coherence assumption is explicitly introduced only at step 2. Non-scheme-representable flat a is covered by the P=E times_W T construction, so no representability condition has slipped in. No finite-type, separatedness, qcqs, smoothness, or finiteness hypothesis was added. All step texts are below 2000 characters.

Corrections made during this check: fixed the Zariski-only pullback reference and added the algebraic-space flatness definition; used the existing general comparison node instead of new nodes for its clauses; made the square ar=tf, the cancellation equation and the inverse-gluing argument explicit. The four off-unit generic tools are declared in split_report.tool_uses for maintainer review. They concern scheme/space module interfaces and atlases, not an alternative six-functor route. No SGA source is used.

## Unfinished work

None in this one-level split. Existing cited unsplit input nodes remain the tasks of their owners.
