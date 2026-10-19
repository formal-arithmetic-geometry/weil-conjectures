# Stage-1 report: def-trf-global-operator

## Files written

- `dag/nodes/sec-trace-formula/def-trf-global-operator.json`: definition, split using existing interfaces; no Mathlib match for the geometric construction.
- `dag/units/sk-d-operator.json`: only `realized` and `realized_by`, identifying this detailed definition with the unit's displayed composite. The unit has no proof steps.
- `citations.json`: `[]`, because this item is a definition, with no proof steps. Its construction dependencies are in `stmt_deps`.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. I searched `WeilConjectures/` by the exact blueprint id and by globalOperator, global operator, and cohomological correspondence, and checked `dag/lean_names_upstream.json`. The exact id has no hit. `AlgebraicGeometry.ProEtale.Correspondence.globalOperator`, `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Correspondence.lean:861`, has a real composite body (lines 861–866), using `globalOperatorUnit` at 817 and `globalOperatorCounit` at 841. It operates on `Ra_X! K` under a supplied `GeometricOperations A s`, rather than establishing the finite-coefficient point-fibre construction and its canonical comparisons under the hypotheses of this item. `Defs.lean:147` explicitly says the package's `properComparison` has not yet been pinned to the canonical natural transformation. Thus a real body here is useful reference material but not an exact attachment for every clause of this item. No claim of a transitive sorry-free implementation is made.

## WANTED

None. The current blueprint and operation-interface statements needed to split this definition are present. No new theorem needing an external source was created.

## What was wrong and what changed

The imported text has an unmatched parenthesis and ends with the fragment “and”. I used `blueprint_update.statement` and read the actual current file, `literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-d-operator/def-trf-global-operator.md`, including all four numbered clauses. I also read the current `_section.md` and `rem-ptr-trf-global-operator-6.md` in that directory. The old source path is updated to the current snapshot; all import and blueprint-update fields remain intact.

The first isomorphism cannot come from proper coincidence and “identity naturality” alone: that changes `Rc2*` to `Rc2!` but does not change the ambient compact-support space from X to C. I made explicit the composition isomorphism `Ra_X! Rc2! ≅ Ra_C!`, evaluated after the inverse of `Rc2! ≅ Rc2*`. The exceptional-side arrow is the inverse of composition along c1. This is the construction already drawn in the unit and in the Lean helper docstrings; it is not a new mathematical hypothesis or a change of route. Both isomorphism directions are now specified by formulas.

The source's final perfectness sentence is a property of the constructed map, not data needed to define it. The node already has the appropriate forward pointer to `lem-trf-global-operator-perfect`, which itself depends on this definition. I left that pointer intact, removed the property from the defining statement, and did not introduce a dependency cycle. The operator is defined in D(A); the existing lemma states its perfectness refinement.

The previous `def-weil-derived-direct-image` dependency constructs Rf* but does not itself state the ordinary adjunction. The definition now explicitly cites clause (1) of the existing `fix-prop-adjunctions` for the unit and the existing `def-weil-derived-pullback-tensor-hom` for the derived pullback. All other original operation and convention dependencies are used explicitly. The point-fibre convention is written as `Fib_s(Ra_Z! M)`, without conflating a pro-etale sheaf complex on the point with its coefficient complex.

## Search and duplicate audit

I ran `tools/blueprint_refs.py search 'global operator'` and `ancestor def-trf-global-operator`, and searched the DAG and both blueprint snapshots for the item. The imported blueprint node `sk-d-operator` records the same formal composite before point-fibre evaluation, so it is recorded in `blueprint.same_as`; this finite-stage definition specifies its coefficient-point realization with canonical comparisons. When I reopened the shared node after the first dry run, it had been expanded from the original short sketch into an explicit seven-arrow construction. I now cite that existing definition directly for the pre-fibre composite, rather than leaving the unit route links implicit. The other hits concern naturality, graph specialization, Frobenius, or perfectness and are not duplicate definitions.

No new node was necessary: the ordinary adjunction, proper coincidence, composition, exceptional adjunction, coefficient fibre, and categories all have existing interfaces. Before deciding this, I read the statements of the original dependencies and searched the DAG and blueprint for ordinary derived adjunction and compact-support composition. `def-sfb-module-derived-pushpull-adjunction` concerns commutative condensed-ring module objects, so I did not silently use it for these constant finite-ring sheaves. `def-weil-pbc-proetale-operations` also supplies an ambient ordinary adjunction, but `fix-prop-adjunctions` already gives the precise bounded constructible unit needed here.

All Mathlib searches were run through `msearch.py` and copied from `searches.jsonl` with their exact tool and query text. Both semantic services and Loogle were available. I tried two semantic phrasings and additional grep searches. The hits concern compactly supported functions, ordinary sheaf pullback/pushforward, generic adjunction identities, and generic induced derived functors. In particular, I read `Mathlib/CategoryTheory/Adjunction/Basic.lean:90` onward and `Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:1` onward: they supply categorical ingredients, not the geometric functors and comparisons defining this operator. I also inspected the ordinary scheme-module pushforward source in `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`. None is an exact or one-line specialization for this definition. The records do not assert that a generic ingredient is a match for the entire item.

## Review by Q101

I read the main-20261015 definition, the unit's current blueprint statement and recorded unit file, and the fibre/perfectness pointer. The finite datum is the same p, q, k and the same coefficient quotient A throughout; X and C are separated finite type over k, both legs are over s, and the ordinary leg alone is assumed proper. The exceptional adjunction is the constructible one of the current `def-trf-admissibility`, not the obsolete strong unbounded ambient-adjoint notion. In that node's statement, every separated finite-type morphism in this setting is exceptionally admissible, so making the specified adjunction explicit imposes no new geometric restriction.

There are no proof steps to audit for this definition. I instead checked each of its construction clauses against the actual cited node statements:

- Opening data and coefficient cohomology: `def-trf-correspondence` states `u:Lc2* K → Rc1! K` with the ordinary/exceptional leg convention; `def-trf-coefficient-conventions` states `RΓ_c(X,K)=Fib_s(Ra_X!K)` and the finite coefficient categories; `def-weil-finite-field-fiber` and `def-weil-scheme-morphism-properties` give the field and scheme notions. These are the hypotheses and objects used in the displayed endomorphism.
- First arrow: I opened `fix-prop-adjunctions`; clause (1) states the derived adjunction `Lf* ⊣ Rf*` on bounded constructible categories and its unit `id → Rf* Lf*`. Apply it to f=c2 and K. The finite-stage pullback and right-derived-image constructions are precisely those of `def-weil-derived-pullback-tensor-hom` and `def-weil-derived-direct-image`, whose statements I read. This does not take an exceptional counit from the ordinary adjunction.
- First isomorphism: I opened `prop-functor-package`; clause (3) states both `R(gf)! ≅ Rg! Rf!`, with identity and associativity equations, and `Rf! ≅ Rf*` for proper f. With f=c2 and g=a_X, invert proper coincidence and then compose. The equality a_X c2=a_C follows directly because c maps to the fibre product over s. Applying the fibre functor to an isomorphism and composing components are elementary category operations. No projection formula or base-change theorem is used.
- Middle arrow: u is the actual morphism in the correspondence definition. Applying the compact-support cohomology functor means applying `Ra_C!` and then `Fib_s`; no assertion about a morphism of sheaves or stalks is substituted for it. `def-compact-support-direct-image-detailed` supplies the compactification-derived functor, on its stated domains; the package supplies the constructible operations and comparisons used here.
- Second isomorphism: the same clause (3), now for f=c1 and g=a_X, gives `Ra_X! Rc1! ≅ Ra_C!`. Its inverse has exactly the displayed source and target after evaluation at Rc1!K. Properness of c1 is not used. `def-trf-admissibility` specifies Rc1! as a functor on D^b_ctf, so the counit may be evaluated at K in that category.
- Last arrow: I read `def-trf-admissibility`, whose statement explicitly gives the adjunction `$Rf_! \dashv Rf^!$` with counit `$Rf_!Rf^! \to \mathrm{id}$`. The arrow used is this counit at K, mapped by `RΓ_c(X,-)`. The ordinary unit and exceptional counit occur in the correct order. No exactness theorem is needed merely for a functor to map this morphism.

I reopened the updated `sk-d-operator` statement after the server finding: it writes the unit, inverse proper comparison, composition along c2, coefficient map, inverse composition along c1, and exceptional counit explicitly before Fib_s. The added statement dependency takes precisely this formal construction; it does not infer the existence of an unrestricted ambient exceptional adjoint from the abstract definition. Its sk-d-corr and sk-d-six dependencies are consequently reached, as required by the unit. The actual canonical maps and their constructible domains remain supplied by the interfaces audited above.

For C1/C4, every non-elementary comparison used in the definition is stated in a direct dependency, rather than inferred from a definition that merely names a functor. The two added direct interfaces close the ordinary-adjunction gap without a new node. The off-unit ordinary adjunction and six-operations package uses are declared in `split_report.tool_uses` as generic interfaces. The construction is the unit's prescribed unit–proper comparison–coefficient map–exceptional counit route.

For B1–B10 and D1–D5, no statement-only children, relabelled clauses, new definitions, or hidden existence choices were introduced. Imported fields and the existing perfectness pointer were retained. A genuine definition has `proof=[]`, `proof_deps=[]`, and `proof_origin=null`; the required citation list is correspondingly empty. There is no new Stacks lemma needing a tag or pairwise duplicate explanation.

For E1–E6, I traced every intermediate source and target in D(A), checked both uses of a_X c_i=a_C and the properness hypothesis at c2 only, and kept the finite coefficient category unchanged. At K=0 the displayed morphisms all have zero source and target. With both legs identities, the proper and composition comparisons identify the construction with RΓ_c(u), using the normalized identity adjunctions; with C empty the intermediate cohomology is zero and the composite is zero. These cases detect reversing the exceptional-side isomorphism or omitting composition along c2. The correction is to make those two directions explicit, not to posit a new lemma about them.

## Validation and repair

The standalone server `review_split` returned PASS with 0 new nodes and unit sk-d-operator realized. The first full dry run then rejected the unit record because its cited units sk-d-corr and sk-d-six were not reached. I read the current statements of sk-d-corr, sk-d-six, sk-d-setup, and the updated generic sk-d-operator, and added the direct reference to the existing pre-fibre construction described above. This preserves the finite coefficient and constructible-adjoint conventions, adds no new node or hypothesis, and makes the unit route explicit. The full dry run is rerun on this repaired version.

## Unfinished work

None at this one-level definition split. Its existing dependencies remain responsible for their own proofs. The required dry run is the acceptance check; this sandbox is handed to a fresh second reader and is not pushed by this worker.

## Second reading by Q101

- Item statement: checked against `def-trf-global-operator.md` in blueprint snapshot `main-20261015`, including the displayed composite and clauses (1)–(4); the finite coefficient datum, properness of (c_2), point-fibre evaluation, and perfectness pointer are represented faithfully.
- Definition node: checked every hypothesis and arrow against its cited dependency statements; the first comparison uses the inverse proper-coincidence map followed by compact-support composition, and the (c_1) comparison is correctly inverted. Verdict: sound; no node or statement change required.
- Proof steps: none (definition node has `proof=[]` and `citations.json` is empty); there are therefore no uncited proof facts to audit.
- New nodes: none; no B1–B7 or duplicate-node issue applies. The existing `sk-d-operator` is cited for the pre-fibre construction, while the concrete finite-stage maps are supplied by existing interfaces.
- Small cases: the zero complex gives the zero endomorphism, identity legs reduce to the induced map on compact-support cohomology, and an empty correspondence has zero intermediate cohomology; these check the arrow directions and composition placement.

No repairs were needed in the second reading. The required dry run was run after this review section was added; any tool-reported mechanical issue is repaired before delivery.
