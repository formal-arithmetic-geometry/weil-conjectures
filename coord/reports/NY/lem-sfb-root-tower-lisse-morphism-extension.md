# Worker report

1. Files written:
   - dag/nodes/sec-six-functors-basics/lem-sfb-root-tower-lisse-morphism-extension.json: statement, split in eight steps; no Mathlib match.
   - dag/nodes/sec-six-functors-basics/lem-sfb-snc-root-limit-normal-charts.json: one new statement-only geometric lemma, unsplit; no Mathlib match.
   - citations.json: verbatim statement excerpts for every cited node at every step.
2. Attachments: none. Searched WeilConjectures/ for the blueprint id, root-tower terminology, and lisse/dense/restriction/full-faithfulness terminology. LisseMonodromyPullback.lean concerns finite-dimensional adic monodromy, not the stated arbitrary infinite root-limit all-continuous coefficients. RegularLocalization.lean proves domain localizations of weakly etale algebras, not normality plus the root-limit boundary nonzerodivisor.
3. WANTED: an exact published reference for the combined infinite root-limit weakly-etale chart normality formulation in lem-sfb-snc-root-limit-normal-charts. The finite geometric source is ILO Expose IX Proposition 2.1, printed p.133; the infinite and weakly-etale extensions are agent-formulated. WANTED: an exact reference stating full faithfulness for these all-continuous root-limit lisse modules. The proof here is explicitly agent-written, using the available sources below.
4. The imported item was unsplit, with no proof. No statement dispute was found and no hypothesis or conclusion was changed. Removed the unused derived-pushpull statement dependency: this is an underived Hom assertion. The inherited unit record still refers to the older six-functors chapter while the node and its actual source belong to six-functors-basics; neither unit nor chapter is changed. The ancestor command returns None; preserved that inherited value and its via chain, giving the exact current blueprint proof place.
5. Nothing required for this one-level split is left unwritten. The new geometric lemma remains unsplit as required for newly introduced nodes. No Lean was written and no compiler or build tool was run.

## Proof and source reading

Read the current main-20261015 direct-images proof, especially paragraph (3), the chapter record, and the inherited sk-thm-sf-ctf-stability unit. This item supplies only extension of morphisms between already supplied lisse extensions; it does not claim existence of extensions or higher-direct-image vanishing. Read ILO Expose IX Proposition 2.1 proof at printed pp.133–134 (PDF pp.139–140): the finite simultaneous parameter-root algebra is the finite geometric model; its normalization argument is not an infinite all-continuous coefficient theorem. No SGA source is invoked, including the SGA reference mentioned in ILO's separate essential-surjectivity argument, which is not used here.

Read Stacks algebra.tex Tag 034M, lemma-normal-ring-integrally-closed, and Tag 00EE, lemma-disjoint-decomposition; also Tag 037D, lemma-colimit-normal-ring, for the new geometric node's context. Read the statement and proof of Tag 092W in more-algebra.tex: it assumes a normal domain and proves integral closure inside the generic tensor algebra, and does not directly assert normality of all charts on our non-Noetherian root limit. Read Hemo–Richarz–Scholbach Example 3.1, printed p.6: the pulled-back ring is all continuous functions on pro-etale objects. Read Bhatt–Scholze Theorem 2.3.4 and the surrounding weakly-etale/ind-etale refinement discussion. The continuous-function factorization through component quotients is written out, not attributed to a finite-coefficient theorem.

The intended future proof of the new geometric lemma is independent of lisse modules: first the finite SNC parameter-root algebras are regular (the parameters through a point remain a regular parameter system after roots, and unit parameters give etale factors). They are finite free over the original chart with the monomial basis, so the boundary product remains a nonzerodivisor. A weakly-etale base change preserves normality, by ind-etale refinement, normality for etale algebras, filtered-colimit normality, and faithfully-flat descent of normality; flatness preserves the boundary nonzerodivisor. Filtered colimit normality then handles the full root ring; repeat the weakly-etale argument for its arbitrary chart Q. These substantial geometric assertions are isolated as an unsplit lemma rather than hidden in an elementary step. Its statement applies to all weakly-etale A-algebras R, which includes the item's U under either affine-ind-etale or small-site weakly-etale convention.

## Review by NY

I checked the item against its source paragraph and each cited node's actual statement, with the following uses and hypotheses.

Step 1 uses the new normal-chart lemma for the actual affine etale SNC chart B and weakly-etale A-to-R, then the small pro-etale site definition for S-to-Q. The new conclusion explicitly includes both normality and injective multiplication by the product; it does not assert that the infinite rings are Noetherian. The localization description of the open is its universal property.

Step 2 uses exactly the conclusion of lem-weil-pbc-normal-ring-integrally-closed-total, for the normal Q supplied in step 1. Its total quotient ring includes Q[1/s] because s is a nonzerodivisor. Idempotents satisfy a monic quadratic, so the lemma applies. The statement of lem-weil-pbc-spec-clopen-idempotent gives both existence and uniqueness and identifies D(e); it therefore gives the actual inverse-image clopen bijection, not just equality of cardinalities. This step is elementary relative to those two explicitly cited results.

Step 3 uses the affine-scheme-qcqs lemma on both affine spectra, then qcqs-scheme-spectral on both spaces, then the spectral-clopen-component-homeomorphism lemma with precisely the inverse-image clopen bijection from step 2. Its statement includes the quotient-topology homeomorphism and the normalization equation used in step 4. No assumption that connected components are open is made.

Step 4 is an explicit topological argument: clopen ultrametric balls separate points of E, continuous functions are constant on components, the quotient topology gives continuous factorizations, and h inverse supplies the extension. Checking the normalization gives both inverse identities. Precomposition and uniqueness give naturality on affine charts. The formula uses all continuous functions and allows infinite image; compactness or discreteness of E is never substituted.

Step 5 uses lem-weil-pbc-condensed-field-continuous-realization, whose statement applies to any scheme and a totally disconnected normed field, exactly the hypotheses checked in step 4. Its canonical normalization gives the actual restriction map. HRS Example 3.1 directly confirms this coefficient realization. The older normal-generic-continuous-sections lemma is not cited: its normal integral locally Noetherian base is not the root limit here.

Step 6 uses the actual finite-free-local definition of lisse from def-sfb-lisse-coefficient-module, covering refinements from def-weil-pbc-proetale-site, and the module/morphism/regular-module definitions from sk-def-sfb-module-objects. A linear map from a regular module is determined by the image of 1; taking finite direct sums gives exactly the stated matrix calculation. Thus the argument needs no separate monodromy or lattice theorem. Joint affine trivializations follow by fibre products and affine open refinement of the two covers. Finite ranks may vary between charts.

Step 7 restricts both maps to any affine refinement of an overlap and uses the already proved coefficient injectivity on the matrix of their difference, in one common pair of bases. This explicitly handles possible changes of basis. Applying the sheaf axiom to images of sections glues maps, and verifies the module equations locally. This is ordinary sheaf gluing, not an unstated descent theorem about extending objects.

Step 8 uses the actual coefficient inverse-image isomorphism of sk-prop-sfb-cartesian-coefficients, whose first clause applies to E and arbitrary scheme maps. The root presentation commutes with the affine base change by its algebraic universal properties. Restriction commutes with pullback, and uniqueness on the new chart proves compatibility of inverse Hom bijections; it does not assume a general open-direct-image base-change theorem.

For the new node, I checked self-containedness, the characteristic and invertibility conditions at every finite prime-to-p exponent, the weakly-etale meaning, the normal-ring meaning at every prime, and the explicit s-injectivity conclusion. It has no proof steps, no proof dependencies, no circular reference to the item and no module/coefficient conclusion. It is strictly geometric, rather than a restatement of full faithfulness. Tested small cases: n=1; r=0 where S=R and s=1; a point off the divisor (unit parameters); the one-parameter affine line; two coordinate axes (independent parameters); disconnected regular charts; the empty chart and zero Q. The regular-crossing hypothesis matters: if the base is a node with boundary deleting its crossing, clopens can split after deletion, so the coefficient argument is not valid on arbitrary reduced singular bases. Injective s multiplication matters: a whole component lying in V(s) would lose its morphisms on restriction. The geometric lemma retains both protections.

I searched the entire DAG for root/regular/normal, parameter roots, weakly-etale normality, and Tags 037D/092W/034M, and searched the blueprint with blueprint_refs.py for lisse restriction, root normal, parameter root, normal Cartier, integrally closed, Kummer and normal crossings. Existing finite-root structure, filtered-normal-colimit, normal-total-fractions, and generic-continuous-section nodes have different scopes, listed below. I searched WeilConjectures/ for both the exact id and relevant concepts; no exact attachment was found. Mathlib searches all ran through msearch.py, and their output was read; logs are in searches.jsonl. Two semantic phrasings were tried for the item and for the new lemma. Hits are condensed locally-constant functor full faithfulness, ordinary scheme normalization, standard etale algebras, and polynomial regular elements. Reading Condensed/Discrete/Module.lean, Etale/StandardEtale.lean and AlgebraicGeometry/Normalization.lean confirms that these do not state the geometric root-limit theorem or this Hom restriction. The new node has no Mathlib match. No step exceeds 2000 characters.

Checks B–E: the sole new node is statement-only and self-contained; definitions are cited or expanded inline; TeX escapes are written once; sources distinguish their exact finite content from agent extensions. All non-elementary proof inputs are named nodes, all cited statement parts have verbatim citations.json entries, the proof does not use the interior proof of another node, and no step simply applies a new restatement of the item. Edge cases and all hypotheses are addressed above. Corrections made during this review: removed the unused derived dependency and avoided the tempting but invalid application of the Noetherian generic-section lemma to T.

## Not duplicates

lem-sfb-snc-root-limit-normal-charts vs lem-per-smooth-colimit-regular: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-pc-flat-semilinear-equiv: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-pc-localized-approximation-colimits: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-pc-localized-module-colimit-comparison: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-pc-localized-ring-colimit-comparison: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-weil-pbc-canonical-localized-approximation-limit: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-weil-pbc-etale-colimit-normal-local-domain: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-weil-pbc-filtered-colimit-localization-at-prime-data: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-weil-pbc-filtered-colimit-localization-at-prime: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-weil-pbc-filtered-colimit-normal-ring-domain: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-weil-pbc-filtered-colimit-normal-ring-integrally-closed-common-stage: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-weil-pbc-filtered-colimit-normal-ring-integrally-closed: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-weil-pbc-filtered-colimit-normal-ring: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-weil-pbc-limit-module-ring-data-core: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-weil-pbc-localize-filtered-ring-system: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-weil-pbc-localized-approximation-cocones: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-weil-pbc-smooth-over-normal-ring-normal: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs new-filtered-colimit-domain-cocone: this existing node concerns abstract filtered-colimit/localization or smooth-normal algebra; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-trf-normal-tensor-component-join-model: this existing node concerns normal integral generic tensor products; it does not assert normality and the boundary nonzerodivisor for SNC parameter-root rings and their arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-per-snc-root-algebra-structure: the existing lemma assumes a strictly henselian regular local base and treats a single finite root algebra with a chosen primitive root of unity; the new lemma treats arbitrary affine weakly-etale charts of the infinite root limit without those local or root-of-unity assumptions.

lem-sfb-snc-root-limit-normal-charts vs lem-sfb-normal-generic-continuous-sections: the existing lemma is about continuous functions on the generic fibre of a normal integral locally Noetherian scheme, not normality and nonzerodivisors on root limits.

lem-sfb-snc-root-limit-normal-charts vs lem-weil-pbc-weak-etale-integral-closure: the existing lemma assumes a normal domain base and gives integral closure inside a generic tensor algebra, not the SNC root-limit normality and regular boundary equation.

lem-sfb-snc-root-limit-normal-charts vs lem-sbc-root-algebra-regular-at-root: the existing lemma treats localizations of one single-root algebra at primes containing the root; it does not treat simultaneous infinite root rings and arbitrary weakly-etale charts.

lem-sfb-snc-root-limit-normal-charts vs lem-weil-pbc-normal-ring-integrally-closed-total: the existing lemma starts with normality and proves integral closure in total fractions, while the new lemma supplies normality and injectivity of the boundary equation in the geometric root-limit setting.
