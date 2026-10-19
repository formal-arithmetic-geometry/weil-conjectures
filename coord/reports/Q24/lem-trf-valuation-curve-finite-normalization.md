# Worker report: lem-trf-valuation-curve-finite-normalization

Group Q24; stage 1; direct delivery, 2026-10-18.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-valuation-curve-finite-normalization.json: item, split into seven steps, statement unchanged.
- dag/nodes/sec-trace-formula/lem-trf-reduced-fibre-modification.json: new statement-only node, Temkin's general reduced-fibre existence theorem; Mathlib searches found no match.
- citations.json: exact statement quotations for each step/node citation.

One new node, zero Mathlib leaves. No Lean, unit, library, launcher or live repository file was written. No compiler, Lake or build was invoked.

## Attachments and searches

No attachment. Searches in WeilConjectures/ of slopmaster2 for the item's id, valuation/normalization, finite normalization and reduced-fibre modifications found no declaration giving all clauses. The source has geometric-reducedness and slicing lemmas, not the existence of a finite reduced-fibre modification after an alteration. The exact upstream master was also used only as reference, not as evidence of a finished proof.

The whole DAG and blueprint were searched for normalization over a valuation ring, reduced-fibre modification, Theorem 3.5.5, Temkin 4.1, geometric reducedness and generically etale alteration. The blueprint_refs ancestor is lem-trf-local-term-locality; searches for reduced fibre theorem and generically etale alteration returned no blueprint match. The new node retains the full existing ancestry of this Temkin subargument, putting this item first in via. No same_as match was found. The current blueprint ancestor's contraction/local-term proof and the unit sk-i-curve-zero were read; this delivery refines the already-existing valuation-normalization branch and does not replace the unit route.

Actual Mathlib searches ran through msearch.py and are preserved in searches.jsonl. The child records two semantic phrasings, LeanSearch, Loogle and two source greps, with hit counts, names and digests. I read Mathlib/AlgebraicGeometry/Geometrically/Reduced.lean: it supplies definitions, stability under base change and reducedness of flat total spaces, not a reduced-fibre existence theorem. The item search found IsIntegralClosure.finite; reading RingTheory/DedekindDomain/IntegralClosure.lean:175 shows that it assumes a Noetherian integrally closed base and a finite separable field extension, so it cannot prove this relative-curve statement. The unsuccessful Loogle query with unknown IsFinite is recorded as unavailable. Earlier searches inherited with the item were retained. A discarded exploratory affine-normalization query is separated in discarded-searches.jsonl; it is not represented as a new-node search or used to justify the child.

## Literature wanted

WANTED: literature/temkin-stable-modification-arXiv-0707.3953v3.pdf, Theorem 3.5.5 printed p. 21, Proposition 3.5.2 printed pp. 20--21, and §4.1 printed p. 25, for this item and lem-trf-reduced-fibre-modification. The public primary PDF https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf was read online. No copy was downloaded. The local archival PDF is absent, so the item's expanded proof is marked proof_origin.by = agent.

For the reused algebra inputs I also read the cited Stacks source loci: algebra.tex, Tag 0307, lemma-integral-closure-localize; Tag 00GK, lemma-finite-is-integral; and morphisms.tex, Tag 01TS, lemma-base-change-finite-presentation. No SGA source is used.

## Faults and unfinished work

The imported item had no proof. Its statement agrees with the smooth-generic-fibre case of the normalization assertion in Temkin §4.1. I found no statement dispute and changed no hypothesis or conclusion. In particular the field need only be separably closed, the valuation ring need not be Noetherian or discrete, X need not be separated, and empty special fibres are allowed. The finite-height assumption is retained; the given proof actually does not require it once the general reduced-fibre theorem is available.

An initially considered affine normalization-finiteness child would merely have moved a clause into a new node. I did not create it. Instead the child is the general reduced-fibre theorem explicitly invoked by the source, while all specialization to the valuation base, normality and identification with normalization remain in the item's steps.

There is no remaining stage-1 work on the item; the new child is deliberately left unsplit. Nothing claims its Lean proof is complete.

## Not duplicates

lem-trf-reduced-fibre-modification vs lem-trf-geometrically-reduced-eta-normal: the new theorem constructs a finite modification after an alteration of an arbitrary integral qcqs base; the existing proposition starts with a normal base and already-reduced geometric fibres and proves eta-normality, with no existence assertion.

lem-trf-reduced-fibre-modification vs lem-trf-stable-modification-flat-curve-pair: the latter assumes an excellent Noetherian base, curves and markings, and constructs a nodal modification; it does not give a finite reduced-fibre modification for arbitrary-dimensional dominant finitely presented schemes over arbitrary integral qcqs bases.

lem-trf-reduced-fibre-modification vs lem-trf-geometric-reduced-fibre-locus-base-change: the latter identifies an already-existing reduced-fibre locus after base change and constructs no modification or alteration.

lem-trf-reduced-fibre-modification vs lem-trf-valuation-curve-finite-normalization: the new node has no valuation hypothesis and no dimension bound, and its conclusion is an alteration and a finite modification with reduced fibres. It says neither that the modification is normal nor that it is the normalization, nor that an alteration can be removed. Those are precisely the substantive arguments supplied by steps 3--6 of the item.

lem-trf-reduced-fibre-modification vs def-trf-birational-quasi-modification: this definition specifies a separated finite-type birational map; it contains no existence or reduced-fibre assertion.

lem-trf-reduced-fibre-modification vs def-trf-centred-valuation: this defines a valuation with a centre, not an alteration or reduced-fibre theorem.

lem-trf-reduced-fibre-modification vs def-trf-modification: the definition specifies modifications and their canonical generic base change; it is now explicitly cited for that notion, but does not assert that a finite such modification with reduced fibres exists.

lem-trf-reduced-fibre-modification vs def-trf-multipointed-curve-modification: this defines modifications and stability for marked curves; the new theorem is an existence result in arbitrary dimensions with no markings.

lem-trf-reduced-fibre-modification vs def-trf-multipointed-curve: this defines flat finitely presented relative curves with markings and does not construct reduced-fibre modifications.

lem-trf-reduced-fibre-modification vs def-trf-nodal-dualizing-datum: this defines differential and Ext compatibility for a dualizing module in nodal local presentations, unrelated to reduced-fibre modification existence.

lem-trf-reduced-fibre-modification vs def-trf-rational-rank: this defines the rank of a rationalized abelian group, not a scheme-modification existence assertion.

lem-trf-reduced-fibre-modification vs def-trf-schematically-dense-open: this defines schematic density of an open and is now explicitly cited for that notion; it does not assert any modification exists.

lem-trf-reduced-fibre-modification vs def-trf-semistable-multipointed-pair: this defines marked semistable pairs and fibrewise stability, not the existence of reduced-fibre modifications of arbitrary-dimensional schemes.

lem-trf-reduced-fibre-modification vs def-trf-strict-semistable-curve: this defines the local etale nodal charts of a relative curve; no existence theorem for modifications is stated.

lem-trf-reduced-fibre-modification vs def-trf-strictly-semistable-curve: this defines a strictly semistable curve with standard local charts; reduced-fibre existence after alteration is not among its assertions.

## Review by Q24

I read the primary Temkin PDF at §1.2 (the standing integral qcqs base convention), Theorem 3.5.5 and its valuation-base discussion, Proposition 3.5.2, and the opening of §4.1. The item is the integral smooth-generic-fibre instance of the last assertion. The child's hypotheses reproduce the general reduced-fibre theorem: dominance, finite presentation and a geometrically reduced generic fibre over an integral qcqs base, without flatness or a dimension restriction. Its alteration has finite separable generic field, and its finite modification is flat finitely presented with reduced geometric fibres. It adds no normality assertion. The node introduces all its objects and defines dominant and schematically dense inline. It has statement dependencies, no proof or proof dependencies, genuine logged searches, and blueprint provenance. There is no use of an unarchived document disguised as a document-origin proof.

Step 1 uses the actual torsion-freeness assertion of lem-sc-flat-invertible-sections-torsion-free, with the structure sheaf as an invertible module, and the localization assertion of lem-weil-pbc-localization-base-change. The former has no properness or Noetherian hypothesis; the latter allows arbitrary algebras. These give nonzero domain generic affine rings and density. The valuation-ring integrally-closed argument is written out and also applies to all localizations, so the normal integral qcqs hypothesis for the base is really available.

Step 2 uses exactly the conclusions of lem-sc-smooth-normal and sbc-lem-smooth-geometrically-reduced on the smooth dimension-one generic fibre. It invokes the new theorem only after checking dominance and its base hypotheses. The definition def-kun-separably-closed says there is no nontrivial finite separable extension; it is not being used as algebraic closedness or perfection.

Step 3 uses the proper-valuative-existence API, whose statement explicitly covers every valuation ring and every proper target. It needs no discreteness, excellence or finite-height input. Extending the generic point gives a section because the lift is over T. This avoids the stronger and unnecessary assertion that the alteration itself is an isomorphism. The finite-map base-change argument uses the finite-algebra definition and gives a finite generating set after tensoring. The precise finite-presentation base-change clause of lem-weil-pbc-qcqs-morphism-permanence, the arbitrary-base-change flat-module statement of lem-pc-relatively-flat-module-pullback, and the equality of geometric-reducedness loci in lem-trf-geometric-reduced-fibre-locus-base-change give the three required properties of Y. These cited nodes do not require the section to be flat.

Step 4 repeats the same section-injectivity and localization inputs for affine opens of Y. Their nonempty generic fibres are opens of the integral X_eta. This proves integrality and generic density rather than assuming a base change of a modification remains a modification. For each affine open the qcqs-permanence node's affine-source clause gives finite presentation, and flatness and fibre reducedness restrict. The statement of lem-trf-geometrically-reduced-eta-normal then says every finite eta-modification is an isomorphism, precisely the property used next. All its normal-base, integral-base, qcqs, flatness, finite-presentation and geometric-fibre hypotheses have been verified.

Step 5 supplies the normality argument rather than calling eta-normality normality. A rational integral element lies in the generic affine ring by generic smooth normality; it is a single fraction c/a. The monic equation gives a finite power generating set for B[b], the finite-proper lemma supplies properness, and inversion of a gives the common dense open. Injectivity into the common field gives schematic density. Thus this particular finite map satisfies the full eta-modification definition in the previously cited theorem and is an isomorphism. The integral-closure-localization node (Tag 0307) then gives normality of the local rings. No finiteness of the full integral closure is assumed here.

Step 6 uses the finite-morphism definition for affine inverse images, the finite-algebra-is-integral statement (Tag 00GK) for B contained in Abar, and the normality already proved for the opposite inclusion. Generic identity identifies the fraction fields. The normalization definition really is integral closure in the function field, without a built-in finiteness assertion; Tag 0307 checks compatibility on principal opens, so this is an identification of schemes over X, not just an abstract algebra isomorphism.

Step 7 uses finite-proper and the universally-closed part of the proper-morphism definition to prove surjectivity from generic density. It applies the flat/dense-generic-fibre pure-dimension node only with flatness, local finite type, density and generic dimension one established. That node states purity of every nonempty fibre, exactly the item's final clause; nothing is inferred from a mere upper bound on dimension.

I checked delivery-errors B--E point by point. Every quoted fact above is in the cited statement, not its proof; citations.json copies those statements verbatim. All non-elementary inputs have nodes, including finite implies proper, flat base change, generic smooth normality and dimension propagation. The elementary residual arguments are monic equations, finite module generators after tensoring, and equality of two subrings of a common function field, and are written explicitly. No proof step exceeds 2000 characters and no child restates a clause of the item. The off-unit nodes are recorded as generic tools in split_report.tool_uses with a purpose for each; they support the inherited Temkin route.

Small cases: V=K reduces to a smooth integral curve with identity normalization; arbitrary valuation rank and non-discrete non-Noetherian V still satisfy the section and torsion-freeness inputs; an open curve lying wholly over the generic point has empty special fibres and is covered without asserting surjectivity over T. For the child, a field base with X already geometrically reduced permits the identity alteration and modification, and arbitrary dimension (including dimension zero) is allowed. A nonnormal or nonflat input is not silently assumed normal or flat; this is exactly what the theorem alters and modifies. The test modification B[b] uses a nonzero a, so D(a) is schematically dense on both domains. I corrected the proposed clause-level helper before creating any child and made the eta-normal-to-normal argument explicit. No statement was weakened.

The first dry run requested comparisons with eleven further nodes because the shared arXiv number 0707 in their Temkin source filenames was recognized as a tag. I opened all eleven statements: they are definitions, not this existence theorem. The comparisons are above; I also reused the canonical modification and schematic-density definitions in the child and specified that the source open is the inverse image of the target open.
