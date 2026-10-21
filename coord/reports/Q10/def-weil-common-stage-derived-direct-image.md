# Stage-1 delivery: def-weil-common-stage-derived-direct-image

## Files written

- dag/nodes/sec-smooth-purity/def-weil-common-stage-derived-direct-image.json — definition; audited statement dependencies and expanded the imported three-step construction to ten explicit steps. Not a Mathlib leaf.
- dag/nodes/sec-smooth-purity/lem-sf-fixed-pair-adjunction-lift.json — statement, unsplit; no exact Mathlib match. It records an existing project adjunction construction and its two carrier formulas for attachment; no new mathematical proof obligation is intentionally substituted for the main construction.
- citations.json — one entry per step/node citation, copying the cited statement verbatim.
- searches.jsonl — actual search-command log, retained without alteration. prepare.py is sandbox-only preparation code, not part of the delivery.

## Attachments

CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction belongs to lem-sf-fixed-pair-adjunction-lift; WeilConjectures/CategoryTheory/Endofunctor/IsoAlgebraAdjunction.lean:86.
CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction_unit_app_hom_f belongs to lem-sf-fixed-pair-adjunction-lift; the same file:108.
CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction_counit_app_hom_f belongs to lem-sf-fixed-pair-adjunction-lift; the same file:113.

These are recorded in lean_candidates for the maintainer's independent closure check. I read the entire module: the displayed construction, the two compatibility lemmas it uses, and the two carrier equalities contain no sorry. I did not claim to regenerate its transitive sorry map or mark it closed. There is no attachment for the item: its constructions are in Sheaf.Paper.SfCommonStageDirectImage, not a declaration under WeilConjectures/ stating every clause of the item. Searching WeilConjectures/ by the item tag and sfModelDerivedPush/sfModelWeilDerivedPush found no such declaration. The source of the selected common-stage composition comparison contains an open theorem, so a short consumer definition is not evidence of a closed construction.

## WANTED

None. All sources needed here were available locally. No source was downloaded, and no SGA source is used.

## Corrections and scope

STATEMENT-DISPUTED: the imported statement pointed to def-zl-weil-ind-sheaf-category for the actual derived Weil fixed-pair category. That node defines an ind-category of the constructible heart. These are different types: even at Spec(k), the pair with underlying Omega[1] is an object of the derived fixed-pair category, while its carrier is not an object of the constructible heart or its ind-category concentrated in degree zero. I corrected that reference to def-weil-weil-sheaf-complex, whose clauses (1) and (2) explicitly define the category and forgetful functor used by sfCommonStageWeilComplex. No hypothesis, conclusion, functor or intended domain was changed. The ind-node is retained only in proof steps 5 and 8, because its statement explicitly specifies the normalized composition comparison on rationalized integral representatives and the Frobenius square; nothing about its ind-adjunction is used.

The imported proof omitted the exchange and shift constructions, did not cite geometric finiteness results needed by its identity comparison, and described fixed-pair lifting without a node for that argument. Its last step called the whole uniqueness comparison elementary without writing its existence or its normalization. The replacement gives the actual square adjunct and connecting-map formula, the two stage-coherence calculations, the finite-type/Noetherian/dimension checks, the invertibility hypothesis for the Frobenius mate, and the transpose construction of the counit-normalized isomorphism.

I also avoided applying prop-weil-pbc-descent-functors to the right family before proving exactness: its statement assumes exact functors. Step 4 constructs the ordinary right functor directly by the common-stage representative formula and the coherence proved in steps 2–3; no exactness premise for this right-family descent is hidden. Step 6 uses the existing exact left-family descent only for pullback's shift comparisons.

## Not duplicates

lem-sf-fixed-pair-adjunction-lift vs lem-weil-mate-iso-along-equivalences: the existing node proves invertibility of a square mate under equivalence/fully-faithful assumptions. The new node assumes an invertible mate and states the adjunction on fixed pairs, with its underlying unit and counit. It does not repeat or prove mate invertibility.
lem-sf-fixed-pair-adjunction-lift vs lem-fix-weil-operations: the latter is a geometric package for separated finite-type maps and all six operations; its dependencies include substantial geometric results. The new node is the smaller categorical lifting argument for arbitrary categories and supplied invertible exchanges, with no coefficient, scheme, preservation, or separatedness assumptions. It is already stated by the project declaration recorded above. It cannot replace the geometric coefficient descent, Frobenius equivalence, or normalization arguments of the item.
lem-sf-fixed-pair-adjunction-lift vs def-weil-endofunctor-fixed-pair-category: the existing node defines the objects, arrows and faithful forgetful functor; it does not assert that an adjunction lifts.

Whole-DAG searches used mapOfNatIsoAdjunction, IsoAlgebra.mateIso, fixed pairs, endofunctor and adjunction. Whole-blueprint searches included adjunction, common-stage, invertible Frobenius, adjunction to, endofunctor, fixed pairs, invertible structure, mates and shift structure. None states this general lifting result. Searches did find lem-weil-pbc-adjunction-shift-compatibility-unique, so the contemplated new shift leaf was not created. That existing node already owns Mathlib's rightAdjointCommShift and its compatibility/uniqueness statements.

## Review by Q10

I read the worker contract, stage-1 rules, the three levels in SETUP, GOAL, the item's chapter/unit records and both copies of delivery-errors sections B–E. The unit's ordinary direct-image clause remains the route. The maintenance-created item is not the key statement of the unit, so I changed no unit realization field. I read the current main-20261015 derived-direct-image and pullback definitions, Bhatt–Scholze Proposition 6.8.14 and Remark 6.8.15 from the local PDF, and Stacks 099N (proetale.tex, lemma-pushforward-Noetherian-case), particularly its completed adjunction and inverse-limit descriptions. These justify the coefficient convention but are not falsely cited as a theorem specifically about our common-stage model. The detailed formal construction follows SfCommonStageDirectImage.lean, read in full, so proof_origin is agent. For the new node I read IsoAlgebraAdjunction.lean in full, especially lines 47–105 and 108–125. Its statement writes the categories, exchange orientations, mate equation and all functors explicitly and contains no proof sketch.

For step 1 I checked that lem-sf-rational-direct-image-adjunctions states the normalized left family, each rational right adjoint and the invertible scalar-change mates with their counit equation. It expressly does not supply the right-family coherence or common-stage adjunction: those are proved in steps 2–4, not attributed to it. def-weil-algebraically-closed-coefficients supplies the actual pair categories, without Karoubi completion.

For steps 2 and 3 I checked the displayed maps' domains using S for coefficient extension on Y and T on X. Transposing the two unit composites gives c in both cases by naturality and the left triangle. Transposing the associator equation gives the two explicitly written composites, equal by c's coherence and associator naturality. These are direct categorical calculations from the cited adjunction data, with no unnamed theorem about geometry or scalar change. The identity comparison is checked as well; no inductive or circular coherence assertion is used.

For step 4 I checked the right representative formula from S(i,m)R_i to S(j,m)R_j, refining representatives by step 3 and composing with cancellation of the middle comparison. Units/counits are actual stage representatives, their cross-stage compatibility is step 2, and the triangle equations are stage equations. The quoted pullback definition supplies exactly the object and conjugated representative formula used to identify the descended left functor. The selected right adjoint is determined by this universal property; it is not a hollow arbitrary functor.

For step 5 I reread the statement of def-zl-weil-ind-sheaf-category and the defining zlPullComp/zlFrobeniusSquare formulas in WeilIndSheafCategory.lean. The statement really specifies the normalized composition on rationalized integral representatives. Here it is used only for that data. The exchange is defined by the explicit Hom transpose with the counit, which is exactly the operation in def-weil-pbc-adjunction-mate. No invertibility of an arbitrary base-change exchange is asserted.

For step 6 I read every clause of lem-weil-pbc-adjunction-shift-compatibility-unique and Mathlib/CategoryTheory/Shift/Adjunction.lean:388–411. Clause (iii) supplies existence of the right shift structure; clauses (i)–(ii) give counit compatibility and uniqueness. Its hypothesis is the already specified left shift structure. The image of a connecting arrow includes R(L[1]) to (RL)[1], matching the source definition; it is not silently identified with R(w) alone.

For step 7 I checked the statements of lem-sfb-finite-type-composition-base-change, lem-weil-pbc-finite-type-over-noetherian and lem-kun-dimension-finite-type. Base change requires no separatedness. The last node's actual project declaration AlgebraicGeometry.exists_topologicalKrullDim_le was read at FiniteType.lean:212–223 and supplies precisely a finite bound even for an empty scheme. A field is Noetherian since each ideal is zero or the unit ideal. Stalk invertibility is justified via the local residue quotient, not confused with the coefficient field. No finite-dimensionality of an arbitrary Noetherian scheme is assumed.

For step 8 I checked lem-fd-rational-coefficient-category-comparison's simultaneous comparisons and identity/composition compatibility, and the full hypothesis list of lem-sf-common-stage-pullback-identity: Noetherian, finite topological dimension, stalk units, plus the coefficient system and coherence. Step 7 supplies the geometric hypotheses. The separated-model Frobenius special case of the coefficient comparison is not used. def-weil-frobenius-detailed gives a scheme automorphism and its inverse, not a k-linear automorphism. The two inverse-composition isomorphisms exhibit an equivalence, and the equality of scheme maps is justified on the two fibre-product projections.

For step 9 I checked that the mate-isomorphism node is applied with the Frobenius equivalences, hence satisfies both its source-equivalence and target-full-faithfulness hypotheses. I then matched each of e, b, their orientation and the mate equation to the new node's project declaration. The latter supplies precisely the lifted adjunction and underlying unit/counit. def-weil-weil-sheaf-complex explicitly gives the derived fixed-pair category and forgetful functor used here, with no triangulated structure on pairs required.

For step 10 I checked existence by transposing the selected counit into the explicit lifted right adjoint. The transpose back is inverse by the two adjunction identities. Forgetting the counit equation uses the new node's carrier formula. Equality of two normalized comparisons is componentwise injectivity of the geometric Hom bijection, so there is no unproved preservation claim or unrestricted uniqueness of arbitrary isomorphisms.

I tested the new lemma at identity functors and identity exchanges: it reduces to the given adjunction on fixed pairs. Empty categories satisfying the adjunction hypotheses cause no exception; if an endofunctor lacks an invertible mate, the lemma simply cannot be applied. For the item I checked identity f, empty and disconnected schemes, zero complexes, a square without a Cartesian or open assumption, and a nonzero shifted complex on a point. The exchange is only a natural map, and no statement claims its invertibility for a general square. Models need not be separated, and no such hypothesis was added.

All new-node searches were actually run with msearch.py and read. Both semantic searches found generic adjunction-lifting or monad-equivalence APIs with extra/different data; exact-name Loogle and Endofunctor grep found no Mathlib match. I read the candidate lifting files: constructLeftAdjointEquiv assumes regular-epimorphic counits and constructRightAdjointEquiv regular-monomorphic units; these are not one-line instances of the fixed-pair result. The project declaration supplies the exact result. No unavailable service was recorded as a negative result. The new node has no proof or proof_deps and no new Stacks tag invented for a project-specific lemma. All ten step texts are below 2000 characters. Every citation in citations.json is a verbatim full statement from the cited node, and the dependency union is computed from the step uses.

## Tool uses

The split_report declares generic uses of common-stage descent, the simultaneous coefficient comparison, the finite-type/Noetherian theorem and the mate-equivalence theorem. The ind-definition is used only for its explicitly stated normalized composition. The base-change and shift results are existing Mathlib leaves, and the finite-dimension result already has a closed project declaration. The new categorical lifting lemma stays in this unit. No chapter route or unit proof step is replaced.

## What remains

No stage-1 work was intentionally left unfinished. The maintainer must independently verify the proposed project attachment for the new node. No Lean was written, no compiler or Lake command was run, and the read-only repository and launcher files were not modified. Validation and delivery results follow below.

## Validation

Server-only review_split: PASS. Server-only check_dag: no finding introduced by the sandbox or on its nodes. The required deliver.py --no-push finished successfully at 1bf30980484 with preflight passed. The item and one new statement node were packaged by the delivery tool; no local check_dag/review_split/preflight or git invocation was used.
