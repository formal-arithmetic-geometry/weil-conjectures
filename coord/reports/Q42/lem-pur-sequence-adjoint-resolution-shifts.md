## Worker report

Files written: the unchanged-statement item `dag/nodes/sec-smooth-purity/lem-pur-sequence-adjoint-resolution-shifts.json` and three statement-only nodes in the same directory:

- lem-pur-sequence-projection-hom-normalization: statement, unsplit; no Mathlib match. Ordinary projection construction and conditional identification of whole-system derived Hom adjunctions.
- lem-pur-sequence-kflat-comparison-shifts: statement, unsplit; no Mathlib match. Left comparison, strict quotient transitions, finite comparisons and all integer shifts.
- lem-pur-sequence-kinjective-comparison-shifts: statement, unsplit; no Mathlib match. Right comparison, arbitrary simultaneous replacements and all integer shifts.

Attachments: none. Searches of `lean/WeilConjectures/` for the blueprint tag, sequence-adjoint and sequence-projection notions found no exact finished declaration. The item's recorded `lean/Sheaf/Paper/PurSequenceAdjointResolutionShifts.lean` theorem at line 255 ends in `sorry` at line 263, so it is not an attachment.

WANTED: none. All source texts used are present locally.

The released stage-1 repair order dated 2026-10-22 explicitly reopens the reviewed 8306-character proof, keeps its statement/route and requires at least two comparable argument nodes. This delivery creates three (ordinary/Hom, left, right). The new assembly is 1732 characters. No imported statement is disputed or corrected. The old nine arguments are transcribed verbatim below, including every old citation, rather than shortened into the assembly. The new nodes are statements only: the source-specific arguments below are handoff material for their future workers. Their statement dependencies cite notions and the comparison data appearing in their hypotheses; no hidden proof sketch or proof dependency was put in their statements.

Nothing remains unfinished within this one-level stage-1 split. The new nodes intentionally await their own proofs. No Lean was written and no compiler, Lake or local server-only checker was run. No repository or launcher file was changed.

## Sources and blueprint route

I read GOAL.md, the three levels in SETUP.md, the chapter record and the current compatibility unit, the released repair note, the old nine-step split and the blueprint `fix-prop-coherence.proof.md` coefficient-comparison sentence. The unit keeps the comparison of operations through the actual units, counits and evaluation maps; this delivery preserves it. `blueprint_refs.py ancestor` gives `thm-pur-rational-and-qbar-purity`; the new nodes' `via` adds this item before the old via list. The item keeps its existing filled blueprint place. Searches of all imported blueprint nodes for sequence/resolution/adjunction normalization, K-flat, K-injective and sequence notions found no equivalent combined normalization statement.

For the projection/Hom node I read Stacks `sites-modules.tex`, Tag 03D7, label `lemma-adjoint-pullback-pushforward-modules` (1197 onward); `sites-cohomology.tex`, Tag 0940, label `section-derived-limits` (5016 onward), and Tag 07A6, label `lemma-adjoint` (3990 onward); and `derived.tex`, Tag 09T5, label `lemma-derived-adjoint-functors` and its preceding pre-derived Hom argument (9517–9605). These give the ordinary formulas and the canonical derived extension. The comparison with the particular supplied coefficient calculus is the agent normalization argument of old step 7, not a claim that Stacks literally names that calculus. The node assumes the two canonical normalized isomorphisms in this conditional derived-Hom clause; it does not assume their existence or the conclusion of the parent.

For the left node I read `sites-cohomology.tex`, Tag 06YY, label `lemma-derived-base-change` (3585 onward), including the resolving class of K-flat complexes with flat terms, and Tag 06YN, label `definition-K-flat` (2999 onward). The quotient-system identification uses the statement of `lem-coef-derived-system-evaluation-calculus` and the canonical maps in `lem-weil-pbc-ringed-topoi-derived-pullback`, not merely evaluated object isomorphisms. Its shift sign is the explicit direct-sum total calculation retained below.

For the right node I read `sites-cohomology.tex`, Tag 0D6E, label `lemma-derived-pushforward-composition` (4011 onward) and Tag 0940, label `section-derived-limits`. Tag 0D6E itself supplies the composition isomorphism; the precise `lim j` normalization is supplied by the separately stated DAG node `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`. I opened that statement and did not infer the normalization from the Stacks proof alone. The extension to any supplied replacement is old step 6 using Hom into K-injectives and the unique comparison formulas, not the assertion that U preserves K-injectives.

## Review by Q42

The four assembly steps cite only the new statements, which I reread after writing them. Step 1 takes the projection, exact factorization and particular ordinary transpose from the first node's first conclusion. Step 2 takes existence and normalization of alpha, finite comparison and coherent shifts from the left node. Step 3 takes existence and normalization of kappa, the arbitrary replacement clause and shifted degree formula from the right node. Step 4 applies the first node's conditional whole-derived-Hom conclusion: its two hypotheses are the canonical alpha of step 2 and the canonical kappa of step 3. Thus the two comparisons concern the same projection and the same supplied calculus, not unrelated naturally isomorphic functors. Its conclusion is an identification on entire system Hom sets, so taking identity transposes really identifies units and counits. All cited conclusions, including these hypotheses, are copied verbatim into citations.json. The first dry run listed additional same-tag candidates in the server delivery tree; I opened all 34 returned records, found them to concern scalar slices, point sections, geometric coefficient changes or supplied data types, and added the explicit comparisons below. I found no C4 mismatch in these four applications.

I also checked all inherited arguments against the statements they will use in the new workers' splits. Old step 1 uses the ringed sequence site's actual tower description and exact scalar restriction; step 2 uses the tensor-formula module adjunction and writes both inverse maps. Old step 3 uses the existence of a flat-term K-flat resolution, the universal comparison on every such resolution (including maps and third-resolution composition), the supplied calculus's strict quotient representative, and canonical derived change of rings at each n. The new left statement preserves those clauses. Step 4 uses the K-flat definition and direct-sum tensor differential, not an unsupported claim that the quotient map is flat. For the d_T term the exponents on the two sides are r(p+1); for d_Q they are rp+p+r. Cohomology reindexing preserves quasi-isomorphisms. These are the sign and resolution hypotheses needed for the left shift.

Old step 5 uses exact-localization factorization only after checking U is exact levelwise. The sites are small: the fixed skeleton is small and the sequence index is countable. Thus K-injective existence applies on both ringed sites. The composition lemma explicitly allows replacing UI: it does not require UI itself to be K-injective. Old step 6 uses the stated Hom_K-to-Hom_D bijection into J to lift the inverse of Ui and then uses two-out-of-three. The unique homotopy class satisfies b Ui homotopic to v, and the derived-map computation statement gives independence, identities, compositions and resolution cocycles. These exact clauses, not just objectwise model existence, are retained in the new right node.

Old step 7 uses the full fraction extension in the sequence-projection derived-adjunction statement, plus resolving-derived-adjunction normalization: the transpose is adj_0(f) followed by lim j. The projection comparison statement identifies the transported unit/counit and the supplied calculus explicitly says its adjunction is canonical. I did not infer equality of arbitrary system maps from their evaluated components; the new Hom node retains this distinction. Old step 8 uses the K-injective shift theorem, the exact same shifted replacement j[r], and degreewise inverse limit; its unique comparison for v[r] is b[r]. The map-computation statement supplies naturality for arbitrary derived morphisms. Step 9 is the common representative argument for zero, addition and inverse shifts. Its left and right portions are explicitly conclusions of the corresponding new statements.

Small cases checked for the new statements: W empty, the zero complex and zero chain maps; shift r=0, r=1 and r=-1, then two shifts r+s; resolution maps equal to identities; arbitrary unbounded Q and N. The formulas stay valid for non-flat quotient A to B_n: the left proof uses K-flatness of Q rather than flatness of the ring map. No arbitrary product-exactness assumption or completeness of P was introduced. The right arbitrary-replacement hypothesis is a quasi-isomorphism to a K-injective tower, never a claim about individual I_n. In the Hom lemma alpha and kappa are universal-resolution-normalized: an arbitrary twist of the supplied adjunction is not silently admitted.

B–E review: each statement introduces all its objects and cites the exact definition nodes for the site, complexes, flatness, K-injectivity and ringed morphism. Statements contain TeX, no proof steps, no proof_deps and no hidden claim of construction from an unproved arbitrary choice. I searched the whole DAG and blueprint as well as the project Lean source before creating them, and inspected nearby sequence lemmas. The repair order expressly requires extracting the old substantive arguments: no new node states the whole parent, and the Hom conclusion is conditional on comparisons established separately by the other two nodes. No cycle or route change is intended. All old arguments remain available below. Each assembly step is under 2000 characters and is a direct application of the precise extracted statements.

## Mathlib searches

All recorded queries were run through the required msearch.py command and are retained unchanged in searches.jsonl. Each new node has its own concept's LeanFinder query, a second phrasing, Loogle and grep; LeanSearch attempts received HTTP rate-limit responses and are marked unavailable. Candidate source readings included Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:60 (ordinary sheaf-module adjunction), Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean:144 (abstract absolute derived adjunction), and Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean:95 (K-injective shifts). None states the simultaneous quotient-ring comparison to the supplied calculus with these normalization equations. The left second query gives ordinary pullback composition and free-object results, the right second query bounded injective-resolution results, and the Hom second query ordinary module/constant-sheaf adjunctions. They do not turn the entire extracted arguments into one-line Mathlib specializations. There are zero Mathlib leaves in this delivery.

## Not duplicates

lem-pur-sequence-projection-hom-normalization vs lem-sfb-internal-module-operations-transport: the existing statement concerns Internal and sectionwise module operations agree; the new lemma identifies the supplied quotient-system adjunction on whole derived Hom sets under canonical left/right comparison hypotheses and includes its ordinary projection construction.

lem-pur-sequence-projection-hom-normalization vs lem-sbc-raw-module-abelian-hom-target-formula: the existing statement concerns Abelian expansion of the scalar raw class; the new lemma identifies the supplied quotient-system adjunction on whole derived Hom sets under canonical left/right comparison hypotheses and includes its ordinary projection construction.

lem-pur-sequence-projection-hom-normalization vs lem-sbc-raw-scalar-sheaf-composition: the existing statement concerns Scalar forgetting commutes with inverse-image composition on sheaves; the new lemma identifies the supplied quotient-system adjunction on whole derived Hom sets under canonical left/right comparison hypotheses and includes its ordinary projection construction.

lem-pur-sequence-projection-hom-normalization vs lem-sbc-raw-module-scalar-source-class-formula: the existing statement concerns Scalar source and class coherence before coefficients; the new lemma identifies the supplied quotient-system adjunction on whole derived Hom sets under canonical left/right comparison hypotheses and includes its ordinary projection construction.

lem-pur-sequence-projection-hom-normalization vs lem-sbc-raw-scalar-coefficient-square-shift-transport: the existing statement concerns Shift transport for the coefficient square; the new lemma identifies the supplied quotient-system adjunction on whole derived Hom sets under canonical left/right comparison hypotheses and includes its ordinary projection construction.

lem-pur-sequence-projection-hom-normalization vs def-sbc-raw-module-scalar-source-prefix: the existing statement concerns Concrete common source prefix; the new lemma identifies the supplied quotient-system adjunction on whole derived Hom sets under canonical left/right comparison hypotheses and includes its ordinary projection construction.

lem-pur-sequence-projection-hom-normalization vs lem-sbc-raw-scalar-derived-pullback-shift: the existing statement concerns Derived scalar pullback comparison commutes with shifts; the new lemma identifies the supplied quotient-system adjunction on whole derived Hom sets under canonical left/right comparison hypotheses and includes its ordinary projection construction.

lem-pur-sequence-projection-hom-normalization vs lem-sbc-raw-module-abelian-hom-map-naturality: the existing statement concerns The fixed raw scalar comparison intertwines pullback; the new lemma identifies the supplied quotient-system adjunction on whole derived Hom sets under canonical left/right comparison hypotheses and includes its ordinary projection construction.

lem-pur-sequence-projection-hom-normalization vs def-sbc-raw-module-abelian-hom-map: the existing statement concerns The explicit scalar-forgetting map of raw derived Hom; the new lemma identifies the supplied quotient-system adjunction on whole derived Hom sets under canonical left/right comparison hypotheses and includes its ordinary projection construction.

lem-pur-sequence-projection-hom-normalization vs lem-sbc-raw-scalar-coefficient-unshifted: the existing statement concerns Unshifted coefficient-factor square; the new lemma identifies the supplied quotient-system adjunction on whole derived Hom sets under canonical left/right comparison hypotheses and includes its ordinary projection construction.

lem-pur-sequence-projection-hom-normalization vs lem-sbc-raw-module-abelian-hom-source-formula: the existing statement concerns Module source and class factors after scalar forgetting; the new lemma identifies the supplied quotient-system adjunction on whole derived Hom sets under canonical left/right comparison hypotheses and includes its ordinary projection construction.

lem-pur-sequence-projection-hom-normalization vs lem-sbc-raw-scalar-coefficient-square: the existing statement concerns The shifted coefficient factors of scalar forgetting commute with pullback; the new lemma identifies the supplied quotient-system adjunction on whole derived Hom sets under canonical left/right comparison hypotheses and includes its ordinary projection construction.

lem-pur-sequence-kflat-comparison-shifts vs lem-pe-kflat-roos-representative-invariance: the existing statement concerns K-flat representative invariance of augmented scalar-extension Roos cones; the new lemma compares Lp* with the supplied strict quotient reduction on one resolution and proves its simultaneous integer-shift normalization, not only a finite scalar extension, a unit, or a Roos-complex comparison.

lem-pur-sequence-kflat-comparison-shifts vs lem-pe-two-term-reduction-cohomology: the existing statement concerns Cohomology and quotient maps of a two-term integral coefficient complex; the new lemma compares Lp* with the supplied strict quotient reduction on one resolution and proves its simultaneous integer-shift normalization, not only a finite scalar extension, a unit, or a Roos-complex comparison.

lem-pur-sequence-kflat-comparison-shifts vs lem-pe-restricted-kflat-tensor-identification: the existing statement concerns Restricted scalar-first K-flat tensor models identify derived scalar extensions; the new lemma compares Lp* with the supplied strict quotient reduction on one resolution and proves its simultaneous integer-shift normalization, not only a finite scalar extension, a unit, or a Roos-complex comparison.

lem-pur-sequence-kflat-comparison-shifts vs def-pe-integral-presentation-encoding: the existing statement concerns Specified integral coefficient presentation encoding; the new lemma compares Lp* with the supplied strict quotient reduction on one resolution and proves its simultaneous integer-shift normalization, not only a finite scalar extension, a unit, or a Roos-complex comparison.

lem-pur-sequence-kflat-comparison-shifts vs lem-pe-kflat-scalar-tower-realization: the existing statement concerns K-flat realization of the augmented derived scalar-extension tower; the new lemma compares Lp* with the supplied strict quotient reduction on one resolution and proves its simultaneous integer-shift normalization, not only a finite scalar extension, a unit, or a Roos-complex comparison.

lem-pur-sequence-kflat-comparison-shifts vs lem-pe-integral-reduction-transition-comparison: the existing statement concerns Quotient transitions under normalized integral coefficient comparison; the new lemma compares Lp* with the supplied strict quotient reduction on one resolution and proves its simultaneous integer-shift normalization, not only a finite scalar extension, a unit, or a Roos-complex comparison.

lem-pur-sequence-kflat-comparison-shifts vs lem-pe-integral-normalized-restriction-squares: the existing statement concerns Normalized finite restriction squares for the integral coefficient presentation; the new lemma compares Lp* with the supplied strict quotient reduction on one resolution and proves its simultaneous integer-shift normalization, not only a finite scalar extension, a unit, or a Roos-complex comparison.

lem-pur-sequence-kflat-comparison-shifts vs lem-sbc-derived-scalar-extension-counit-shift: the existing statement concerns Counit-compatible shift structure of derived change of rings on a site; the new lemma compares Lp* with the supplied strict quotient reduction on one resolution and proves its simultaneous integer-shift normalization, not only a finite scalar extension, a unit, or a Roos-complex comparison.

lem-pur-sequence-kflat-comparison-shifts vs lem-sbc-scalar-extension-counit-properties: the existing statement concerns K-flat computation and triangulatedness of a specified scalar-extension counit; the new lemma compares Lp* with the supplied strict quotient reduction on one resolution and proves its simultaneous integer-shift normalization, not only a finite scalar extension, a unit, or a Roos-complex comparison.

lem-pur-sequence-kflat-comparison-shifts vs lem-sbc-derived-coefficient-map-descent: the existing statement concerns Descent of a termwise coefficient map through a resolving counit; the new lemma compares Lp* with the supplied strict quotient reduction on one resolution and proves its simultaneous integer-shift normalization, not only a finite scalar extension, a unit, or a Roos-complex comparison.

lem-pur-sequence-kflat-comparison-shifts vs lem-weil-pbc-scalar-extension-unit-triangles: the existing statement concerns Scalar-extension maps form morphisms of distinguished triangles; the new lemma compares Lp* with the supplied strict quotient reduction on one resolution and proves its simultaneous integer-shift normalization, not only a finite scalar extension, a unit, or a Roos-complex comparison.

lem-pur-sequence-kflat-comparison-shifts vs def-sf-integral-hom-reduction-comparison: the existing statement concerns Canonical integral internal Hom reduction comparison; the new lemma compares Lp* with the supplied strict quotient reduction on one resolution and proves its simultaneous integer-shift normalization, not only a finite scalar extension, a unit, or a Roos-complex comparison.

lem-pur-sequence-kinjective-comparison-shifts vs lem-pur-sequence-adjoint-resolution-shifts: the parent combines all three arguments; this extracts only the right comparison/replacement argument under the explicit human re-split order, without the left comparison or adjunction identification.

lem-pur-sequence-kinjective-comparison-shifts vs lem-coef-enriched-sequence-projection-formula: the existing statement concerns Uncurried finite projections of the enriched sequence adjunction; the new lemma retains the canonical lim-j comparison for every arbitrary supplied UN-to-J replacement and its precise integer-shift normalization; it is not a sections comparison, projection formula or existence of a model.

lem-pur-sequence-kinjective-comparison-shifts vs lem-coef-sequence-sections-limit-comparison: the existing statement concerns Derived sections and total limit with specified projections; the new lemma retains the canonical lim-j comparison for every arbitrary supplied UN-to-J replacement and its precise integer-shift normalization; it is not a sections comparison, projection formula or existence of a model.

lem-pur-sequence-kinjective-comparison-shifts vs lem-coef-sequence-pushforward-limit-projections: the existing statement concerns Restricted total-limit comparison with adjunction projections; the new lemma retains the canonical lim-j comparison for every arbitrary supplied UN-to-J replacement and its precise integer-shift normalization; it is not a sections comparison, projection formula or existence of a model.

lem-pur-sequence-kinjective-comparison-shifts vs lem-coef-sequence-global-sections-evaluation: the existing statement concerns Derived termwise global sections with finite evaluation and transition normalization; the new lemma retains the canonical lim-j comparison for every arbitrary supplied UN-to-J replacement and its precise integer-shift normalization; it is not a sections comparison, projection formula or existence of a model.

lem-pur-sequence-kinjective-comparison-shifts vs lem-sf-ambient-adjunction-compositor-normalization: the existing statement concerns Adjunction and resolution normalization of ambient direct-image and open compositors; the new lemma retains the canonical lim-j comparison for every arbitrary supplied UN-to-J replacement and its precise integer-shift normalization; it is not a sections comparison, projection formula or existence of a model.

lem-pur-sequence-kinjective-comparison-shifts vs lem-coef-restricted-tower-resolution-acyclicity: the existing statement concerns Acyclicity and projection equations for a restricted varying-ring resolution; the new lemma retains the canonical lim-j comparison for every arbitrary supplied UN-to-J replacement and its precise integer-shift normalization; it is not a sections comparison, projection formula or existence of a model.

lem-pur-sequence-kinjective-comparison-shifts vs lem-coef-derived-sections-scalar-coherence: the existing statement concerns Coherent unit-normalized scalar comparison for unbounded derived global sections; the new lemma retains the canonical lim-j comparison for every arbitrary supplied UN-to-J replacement and its precise integer-shift normalization; it is not a sections comparison, projection formula or existence of a model.

lem-pur-sequence-kinjective-comparison-shifts vs def-trf-completion-unit-models: the existing statement concerns Ordinary quotient adjunction and normalized derived completion models; the new lemma retains the canonical lim-j comparison for every arbitrary supplied UN-to-J replacement and its precise integer-shift normalization; it is not a sections comparison, projection formula or existence of a model.

lem-pur-sequence-kinjective-comparison-shifts vs lem-trf-completion-unit-canonical-models: the existing statement concerns Compatible ordinary and derived presentations of the coefficient adjunction; the new lemma retains the canonical lim-j comparison for every arbitrary supplied UN-to-J replacement and its precise integer-shift normalization; it is not a sections comparison, projection formula or existence of a model.

lem-pur-sequence-kinjective-comparison-shifts vs lem-sfb-finite-principal-support-unit-assembly: the existing statement concerns Finite principal-support vanishing assembles the specified derived open unit; the new lemma retains the canonical lim-j comparison for every arbitrary supplied UN-to-J replacement and its precise integer-shift normalization; it is not a sections comparison, projection formula or existence of a model.

lem-pur-sequence-kinjective-comparison-shifts vs lem-sfb-internal-scalar-mate-projection: the existing statement concerns Restriction of an internal coefficient mate is the specified projection map; the new lemma retains the canonical lim-j comparison for every arbitrary supplied UN-to-J replacement and its precise integer-shift normalization; it is not a sections comparison, projection formula or existence of a model.

lem-pur-sequence-kflat-comparison-shifts vs def-a1-integral-completed-tower-pullback-universes: the existing node defines tower-valued resolving pairs and scheme pullback data; it asserts neither this ringed-sequence comparison nor its shift normalization.

lem-pur-sequence-kflat-comparison-shifts vs def-per-scalar-extension-unit: the existing node defines the tensor multiplication unit for the identity ring map, not the quotient-sequence left-derived comparison.

lem-pur-sequence-kflat-comparison-shifts vs lem-per-proetale-scalar-slice-comparison: the existing node compares scalar extension with restriction to a slice object, not with a simultaneous quotient sequence and its shifts.

lem-pur-sequence-kflat-comparison-shifts vs lem-pod-derived-reduction-sheaf-resolution-independence: the existing node compares sections with one principal quotient and proves independence, with exact sections assumed; it has no sequence projection or all-integer shift equation.

lem-pur-sequence-kflat-comparison-shifts vs lem-pod-point-sections-derived-reduction-cone: the existing node identifies restricted reduction on point modules with a principal cone; the new node is about arbitrary W and a strict sequence projection, without a cone or sections hypothesis.

lem-pur-sequence-kflat-comparison-shifts vs lem-pod-point-sections-derived-reduction-homology: the existing node is a homology-functor comparison for point sections, whereas the new comparison is an isomorphism of whole derived sequence objects and normalized shifts.

lem-pur-sequence-kflat-comparison-shifts vs lem-pod-point-sections-derived-reduction-iso: the existing node identifies two point-sections functors; it does not specify the quotient-sequence left comparison or cochain shifts.

lem-pur-sequence-kflat-comparison-shifts vs lem-pod-principal-derived-tensor-cone: the existing node is an algebraic one-quotient cone model with injective multiplication by t, not a ringed-sequence projection model.

lem-pur-sequence-kflat-comparison-shifts vs lem-pod-principal-quotient-quasi-iso: the existing node preserves quasi-isomorphisms under one principal quotient assuming termwise t-injectivity; the new statement identifies canonical functors and all shifts, with K-flat input instead.

lem-pur-sequence-kflat-comparison-shifts vs lem-pod-principal-reduction-comparison: the existing node compares exact sections and a principal derived quotient over a domain; no sections functor or domain hypothesis occurs in the new assertion.

lem-pur-sequence-kflat-comparison-shifts vs lem-pod-principal-reduction-flat-comparison: the existing node proves invertibility of that exact-sections comparison on K-flat inputs, not the simultaneous strict quotient-system comparison and shift identities.

lem-pur-sequence-kflat-comparison-shifts vs lem-pod-scalar-reduction-cochain-comparison: the existing node identifies one normalized cochain model with prescribed finite reduction, but does not identify Lp* on the sequence site or its all-integer shifts and transitions.

lem-pur-sequence-kinjective-comparison-shifts vs def-weil-pbc-adjunction-conjugate: the existing node defines the categorical conjugation bijection and its composition rules; it contains no K-injective replacement or inverse-limit computation.

lem-pur-sequence-kinjective-comparison-shifts vs def-weil-pbc-derived-direct-image-composition: the existing node defines bounded-below abelian etale scheme direct-image composition as a mate; the new node computes unbounded module sequence projection on arbitrary replacements.

lem-pur-sequence-kinjective-comparison-shifts vs lem-weil-pbc-frobenius-exchange-restriction: the existing node compares finite coefficients with ambient Frobenius exchange transformations; it neither concerns sequence inverse limit nor computes arbitrary shifted replacements.

lem-pur-sequence-kinjective-comparison-shifts vs lem-weil-pbc-ordinary-ringed-exchange-coherence: the existing node gives identity and pasting equations for geometric exchange maps, not the derived inverse-limit resolution normalization.

lem-pur-sequence-kinjective-comparison-shifts vs lem-weil-pbc-ring-sheaf-change-adjunction-existence: the existing node asserts coefficient-change direct-image comparisons with unit normalization, not the arbitrary UN-to-J replacement and coherent shift formulas.

lem-pur-sequence-kinjective-comparison-shifts vs lem-weil-pbc-ring-sheaf-change-adjunction: the existing node concerns two identified-coefficient pullbacks/direct images for a scheme morphism; it does not give the sequence-site arbitrary-replacement comparison or its precise shifted map.

lem-pur-sequence-kinjective-comparison-shifts vs lem-weil-pbc-ringed-topoi-derived-pushforward-composition: the existing node is the reused generic composition lemma with lim-j specialization available; the new argument adds arbitrary supplied simultaneous replacements, their unique b comparisons and all integer-shift/naturality equations.

lem-pur-sequence-kinjective-comparison-shifts vs def-sfb-ringed-derived-comparison-data: the existing node defines supplied comparisons for internal and ringed module operations; it does not prove existence of the sequence-limit comparison or its arbitrary shifted replacement equations.

lem-pur-sequence-kinjective-comparison-shifts vs lem-sfb-coefficient-ringed-square-normalization: the existing node is a coefficient-change square normalization for scheme operations, not the sequence-projection inverse-limit comparison on arbitrary replacements.

lem-pur-sequence-kinjective-comparison-shifts vs lem-sfb-derived-composition-adjunction-normalization: the existing node identifies direct-image compositors with mates of pullback compositors, not the concrete lim-j/arbitrary-replacement shift formula.

lem-pur-sequence-kinjective-comparison-shifts vs lem-sfb-exact-compactification-unit-composition: the existing node concerns compactification units and exact functors, not the ring-change/constant-sequence factorization and arbitrary K-injective tower replacement.

lem-pur-sequence-projection-hom-normalization vs def-pd-proetale-section-module-functors: the existing node defines internal/section module operations and tensor comparisons for scheme maps, not the supplied coefficient-calculus sequence adjunction or full normalized Hom formula.

lem-pur-sequence-projection-hom-normalization vs def-pd-section-module-operations-data: the existing node defines scheme-map operations and internal/section equivalences, rather than proving the quotient projection and its normalized derived Hom identification.

lem-pur-sequence-projection-hom-normalization vs lem-pd-composite-module-oplax-mate: the existing node identifies oplax tensor maps as mates for internal module pullback, not the sequence projection tensor/limit Hom bijection.

lem-pur-sequence-projection-hom-normalization vs lem-pd-internal-direct-image-lax-realization: the existing node compares internal and sectionwise ordinary adjunctions/lax tensor structures; the new node identifies a supplied derived reduction/limit adjunction under resolution-normalized comparisons.

lem-pur-sequence-projection-hom-normalization vs lem-pd-ringed-tensor-adjunction-mate: the existing node identifies ordinary tensor oplax mates for a geometric morphism with scalar extension, not the whole derived Hom comparison with the supplied sequence calculus.

lem-pur-sequence-projection-hom-normalization vs lem-pod-canonical-module-adjunction-unit: the existing node is an ordinary unit-section formula for a scheme map with an isomorphism of coefficient sheaves; the new node constructs a quotient sequence projection and compares full derived Hom adjunctions.

lem-pur-sequence-projection-hom-normalization vs def-pbc-successive-derived-scalar-normalization-data: the existing node defines families of scalar-extension normalization data, without asserting their existence or the quotient-sequence supplied-adjunction comparison.

lem-pur-sequence-projection-hom-normalization vs def-weil-pbc-ringed-tensor-section-calculus: the existing node constructs ordinary scalar extension and its pure-tensor unit on one site, not the sequence projection and derived limit Hom comparison.

lem-pur-sequence-projection-hom-normalization vs def-weil-pbc-strict-local-module-sections-set-equiv: the existing node defines a sections/set equivalence over a strict henselization, without a sequence ring or derived reduction/limit adjunction.

lem-pur-sequence-projection-hom-normalization vs def-weil-pbc-successive-derived-quotient-data: the existing node defines successive scalar-extension presentations and normalizations, not the claimed ordinary projection existence and conditional full Hom identification.

lem-pur-sequence-projection-hom-normalization vs def-weil-pbc-system-scalar-model: the existing node defines a normalized extension/restriction model for one ring map; the new node proves a projection/limit correspondence for an entire sequence and identifies the supplied calculus under its two canonical resolution comparisons.

Additional nearby statements read: `lem-pur-sequence-site-completion-projection` constructs the ordinary projection and the unshifted K-flat model, but supplies neither the all-integer shift normalization nor the supplied-calculus Hom identification. `lem-coef-sequence-projection-derived-adjunction` states the ordinary/fraction adjunction but not its identification with any supplied calculus under both normalized comparisons. `lem-coef-sequence-adjunction-cochain-transposes` states unit/counit formulas, not that entire normalized comparison or arbitrary shifted right replacement. `lem-coef-sequence-pushforward-limit-projections` gives a projection-preserving comparison, not the lim-j and arbitrary-replacement shift equations. `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` is a generic ingredient used below, not the simultaneous shift/naturality comparison. `lem-pur-quotient-expression-kflat-normalization` is about normalized finite tensor/pullback expressions and transition adjoints across schemes, not the sequence projection and its cochain shift comparison. The new statements are not new definition nodes for these existing notions.

## Preserved argument handoff (verbatim old steps)

The allocation is Hom node = steps 1, 2, 7; left node = steps 3, 4 and the left part of 9; right node = steps 5, 6, 8 and the right part of 9. The integer addition/zero/inverse argument in step 9 is shared by both shift nodes. Every original sentence follows, with its exact dependencies and sources. These are handoff arguments, not proof fields on the unsplit nodes.

### Old step 1

Construct the underlying geometric morphism directly from the sequence-site description in [def-coef-ringed-sequence-site]. A sheaf is a tower of sheaves on $\mathcal V$. The constant-tower functor $c$ is left adjoint to limit: a map $cF\to H$ is a compatible family $F\to H_n$, equivalently a map $F\to\lim H_n$. Finite limits of towers are levelwise, so $c$ preserves finite limits. Thus $(c,\lim)$ is a geometric morphism $g$. Give its source the constant ring $A^{\mathrm{const}}=cA$. The compatible projections $A\to B_n$ are a ring map $cA\to B$ on the sequence site; with the identity geometric morphism this defines $a:(\mathcal T,B)\to(\mathcal T,cA)$. Put $p=g\circ a$. Its scalar restriction $a_*=U$ is exact: kernels and cokernels of a semilinear system are levelwise, and restriction changes only the scalar action, not the underlying additive maps. On modules $g_*=\lim$, hence $p_*=\lim U$. The sites remain small, since the index set is countable and $\mathcal V$ was fixed small.

Uses: def-coef-ringed-sequence-site.

Source: literature/stacks-project/sites-cohomology.tex, Tag 0940 (section-derived-limits), paragraphs constructing g and its constant-system inverse image; changing the ring by cA to B.

### Old step 2

The module pullback for $p$ is the strict system $p^*Q=(Q\otimes_A B_n)_n$, by the tensor formula of [lem-weil-pbc-ringed-topoi-module-adjunction]. Write $\pi_n:\lim UM\to UM_n$ for the ordinary limit projections. The forward Hom correspondence sends $h:Q\to\lim UM$ to $f_n(x\otimes b)=b\pi_nh(x)$. Conversely $f=(f_n)_n$ sends $x$ to $(f_n(x\otimes1))_n$. Compatibility of $f$ with the quotient transitions is exactly compatibility of this family in the limit. The two constructions are inverse by $B_n$-linearity, commute with restriction to every object of the site, and are natural in $Q,M$. This identifies the ordinary adjunction, including its particular Hom bijection, rather than merely proving existence of some adjoint.

Uses: lem-weil-pbc-ringed-topoi-module-adjunction.

Source: literature/stacks-project/sites-modules.tex, Tag 03D7 (lemma-adjoint-pullback-pushforward-modules), specialized tensor-Hom formulas.

### Old step 3

Choose one flat-term K-flat resolution $q:Q\to P$ using [lem-pc-kflat-resolution]. Apply [lem-weil-pbc-ringed-topoi-derived-pullback] to $p$. Its canonical comparison identifies $Lp^*P$ with $p^*Q$, naturally in maps of resolutions and with the canonical comparison for a third resolution. The latter strict system is exactly the representative defining $\mathcal R(P)$ in the supplied [lem-coef-derived-system-evaluation-calculus]. Both comparisons use the same termwise functor and its universal left-derived comparison, so their composite defines $Lp^*\cong\mathcal R$ on the derived category; it also identifies maps, not just objects. At level $n$, [lem-pur-derived-change-of-rings] computes $-\otimes_A^LB_n$ on the same $Q$. The comparison there is consequently the canonical finite scalar-extension comparison. Every horizontal map is still induced by $B_{n+1}\to B_n$; no independently chosen finite resolutions or transitions have been substituted.

Uses: lem-pc-kflat-resolution, lem-weil-pbc-ringed-topoi-derived-pullback, lem-coef-derived-system-evaluation-calculus, lem-pur-derived-change-of-rings.

Source: literature/stacks-project/sites-cohomology.tex, Tags 06YS (lemma-K-flat-resolution), 06YY (lemma-derived-base-change), 06YT (lemma-derived-tor-quasi-isomorphism-other-side).

### Old step 4

The shift of this representative is literal. Indeed, for any acyclic $T$, the map $T\otimes Q[r]\to(T\otimes Q)[r]$ multiplying the summand $T^p\otimes Q^{q+r}$ by $(-1)^{rp}$ is a chain isomorphism: the $d_T$ coefficients on both sides are $(-1)^{r(p+1)}$, and the $d_Q$ coefficients are $(-1)^{rp+p+r}$. Hence $Q[r]$ is K-flat by [def-pc-kflat-complex] and [def-pc-tensor-complex-sheaves]; its terms remain flat and $q[r]$ remains a quasi-isomorphism since cohomology is reindexed. For scalar extension, $p^*(Q[r])$ and $(p^*Q)[r]$ both have degree-$i$ term $Q^{i+r}\otimes_A B_n$ and differential $(-1)^r(d_Q\otimes1)$. Their comparison is the identity on these terms, on maps of resolutions, and on quotient transitions. Using $Q[r]$ in step 3 proves the required left shift equation, also for each finite scalar extension.

Uses: def-pc-kflat-complex, def-pc-tensor-complex-sheaves.

Source: literature/stacks-project/sites-cohomology.tex, Tag 06YN (definition-K-flat), with the tensor-total differential and the cochain shift convention.

### Old step 5

Since $U$ is exact, its derived functor is its termwise localization, with the identity shift comparison [lem-weil-pbc-exact-functor-derived-factorization]. Apply [lem-weil-pbc-ringed-topoi-derived-pushforward-composition] to $a,g$ from step 1. It gives $\kappa:Rp_*\xrightarrow{\sim}Rg_*D(U)=\mathcal L$, where $Rg_*=R\lim$ is the strict-tower total limit of [lem-weil-pbc-ringed-strict-tower-homotopy-limit]. Specifically, if $I$ is K-injective over $B$ and $j:UI\to J$ is a K-injective replacement over $A^{\mathrm{const}}$, its normalization says that $\lim j:\lim UI\to\lim J$ is a quasi-isomorphism representing $\kappa_I$. Such replacements exist on both small ringed sites by [prop-pur-kinjective-resolutions-exist]. This application does not require $UI$ to be K-injective: its replacement $j$ is precisely the intermediate replacement in the cited composition theorem.

Uses: lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lem-weil-pbc-ringed-strict-tower-homotopy-limit, prop-pur-kinjective-resolutions-exist.

Source: literature/stacks-project/sites-cohomology.tex, Tag 0D6E (lemma-derived-pushforward-composition), normalized K-injective comparison; Tag 0941 (lemma-derived-limit-is-ok).

### Old step 6

For completeness fix any complex $N$ and any simultaneous replacement $v:UN\to J$. Choose $i:N\to I$ K-injective over $B$. Exactness of $U$ makes $Ui$ a quasi-isomorphism. By [lem-weil-pbc-kinjective-hom-derived], precomposition with $Ui$ induces a bijection into the K-injective $J$ on homotopy classes. Thus there is a unique class $b:UI\to J$ with $bUi\simeq v$; it is a quasi-isomorphism by two-out-of-three. Step 5 applies with $j=b$ and represents $\kappa_N$ by $\lim b:\lim UI\to\lim J$ under the resolution identifications. This gives the asserted model $\mathcal L(N)\cong\lim J$ for this particular $v$, not only for replacements obtained by first resolving $N$. Changes of $I$ and $J$, and arbitrary derived morphisms in $N$, are computed by the unique homotopy classes of comparison maps in [lem-sf-kinjective-derived-map-computation]; their composition and cocycle formulas imply independence and naturality of these identifications.

Uses: lem-weil-pbc-kinjective-hom-derived, lem-sf-kinjective-derived-map-computation, lem-weil-pbc-ringed-topoi-derived-pushforward-composition.

Source: literature/stacks-project/derived.tex, Tags 070I (lemma-K-injective) and 070Y (lemma-K-injective-defined); sites-cohomology.tex Tag 0D6E for the comparison represented by lim b.

### Old step 7

Identify the adjunctions using their full Hom correspondences. By [lem-coef-sequence-projection-derived-adjunction], the adjunction $Lp^*\dashv Rp_*$ is the derived fraction extension of the ordinary correspondence in step 2. The normalization in [lem-sfb-resolving-derived-adjunction-normalization] makes this explicit: a chain map $f:p^*Q\to I$ transposes to $Q\to p_*I=\lim UI$, followed, under step 5, by $\lim j:\lim UI\to\lim J$. Thus its transpose is the class of $(\lim j)\operatorname{adj}_0(f)$. The canonical comparison and transported adjunction in [lem-coef-sequence-pushforward-limit-projections] are this reduction/total-limit construction: their projections are the reduction maps and their counit is the scalar-extension transpose of the actual total-limit projections. These are the canonical constructions stipulated by the supplied [lem-coef-derived-system-evaluation-calculus]. Hence steps 3 and 5 identify its adjunction with $Lp^*\dashv Rp_*$ by the normalized derived Hom correspondence. In particular, units and counits agree: each is the inverse image of the identity under this same Hom bijection. This argument uses the derived extension on whole system Hom sets, rather than inferring equality of arbitrary system maps from equality of evaluated maps.

Uses: lem-coef-sequence-projection-derived-adjunction, lem-sfb-resolving-derived-adjunction-normalization, lem-coef-sequence-pushforward-limit-projections, lem-coef-derived-system-evaluation-calculus.

Source: literature/stacks-project/sites-cohomology.tex, Tag 07A6 (lemma-adjoint); derived.tex Tags 0DVC (lemma-pre-derived-adjoint-functors) and 09T5 (lemma-derived-adjoint-functors), with the specified resolution normalization.

### Old step 8

For any integer $r$, [lem-weil-pbc-kinjective-shift] makes $I[r]$ and $J[r]$ K-injective and makes $j[r]:U(I[r])=(UI)[r]\to J[r]$ a valid replacement. Apply the normalization of [lem-weil-pbc-ringed-topoi-derived-pushforward-composition] to exactly this map. It represents $\kappa_{I[r]}$ by $\lim(j[r])$. Degreewise limit commutes with reindexing and multiplication of a differential by $(-1)^r$, so $\lim(J[r])=(\lim J)[r]$ and $\lim(j[r])=(\lim j)[r]$, with degree-$i$ map $\lim j^{i+r}$. Therefore the shift square for $\kappa$ commutes on these representatives. For the arbitrary $v$ in step 6 use $v[r]$ and $b[r]$: $b[r]U(i[r])\simeq v[r]$, and uniqueness of the class into $J[r]$ shows that it is exactly the comparison for the shifted replacement. The comparison and change-of-resolution formulas in [lem-sf-kinjective-derived-map-computation] now give the same equation for arbitrary derived inputs and morphisms. This is the prescribed total-limit shift, not a new shift structure chosen through an abstract adjunction.

Uses: lem-weil-pbc-kinjective-shift, lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lem-sf-kinjective-derived-map-computation.

Source: literature/stacks-project/derived.tex, Tag 070H (definition-K-injective) and its following shift observation; Tag 070Y (lemma-K-injective-defined); sites-cohomology.tex Tag 0D6E.

### Old step 9

Finally, for two shifts $r,s$ use the same representatives $Q[r+s]$, $I[r+s]$, and $j[r+s]$. Shifting twice gives these same terms and maps, since $(-1)^r(-1)^s=(-1)^{r+s}$; shifting by zero is the identity, and shifting by $-r$ is inverse to shifting by $r$. Thus the comparisons in steps 4 and 8 respect addition, zero and inverse shifts with the usual cochain shift identifications. Their already established naturality makes these equations coherent in all derived inputs. The arguments cover $r<0$, the zero complex and the empty scheme. They used neither a normalized-system condition nor completeness of $P$, and no product-exactness assertion occurred.

Uses: .

Source: literature/stacks-project/derived.tex, Coherent cochain shift convention; representative calculations in steps 4 and 8.

