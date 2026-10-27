## Worker report

Files written:
- dag/nodes/sec-six-functors/lem-coef-sequence-global-sections-evaluation.json: existing statement, unchanged; five-step assembly, 2332 characters instead of 6989.
- dag/nodes/sec-six-functors/lem-coef-tower-right-derived-evaluation.json: new statement-only unsplit lemma, no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-derived-sections-scalar-coherence.json: new statement-only unsplit lemma, no Mathlib match.
- citations.json: verbatim statement quotations for every citation in every assembly step.

Attachments: none. I searched WeilConjectures for the blueprint tag, coefficientSequenceGlobalSectionsEvaluation and tower/sections terminology. The matching live Sheaf theorem is at Sheaf/CategoryTheory/CoefficientSequenceGlobalSections.lean:319 and has sorry at line 323; it is not an attachment. No Lean file was written and no compiler was run.

WANTED: none.

The live node has a Q11 stage-1 acceptance of 2026-10-21, but coord/repair-notes/lem-coef-sequence-global-sections-evaluation.json explicitly reopens it on 2026-10-22 under the human's finer-split decision: at most 3000 proof characters and at least two new independent statement-only nodes. That note explains why an apparently accepted split is assigned again. There is no statement dispute. All old statement, Lean-interface, import and maintainer metadata are preserved.

Unfinished work: the proofs of the two new lemmas are deliberately deferred, as required for this stage-1 re-split. There is no unresolved mathematical gap in the assembly conditional on their stated conclusions.

## Argument allocation

Old step 1 stays in assembly step 1: changing an action preserves kernels and sheafified cokernels, hence exactness; compatible coefficient maps make the arrows A-linear and exact localization gives U. This is a short consequence of existing statements and definitions, so no separate node is created for it.

Old step 2 stays in assembly step 2: small diagram module categories are Grothendieck, so functorial K-injective tower replacements exist. Individual module replacements exist separately. The tower lemma assumes these replacement properties, so it makes no unsupported general claim that an arbitrary abelian category has them.

Old steps 3-4 become lem-coef-tower-right-derived-evaluation, for arbitrary additive F between abelian categories. The future proof must apply F degreewise on homotopy categories; addition preserves homotopies, shifts, and mapping cones since every cone degree uses a finite biproduct. Apply the universal total-right-derived construction in the source and its tower category. A tower replacement P -> I evaluates to a quasi-isomorphism by exact evaluation and to K-injective I_n by the exact left adjoint to tower evaluation. Both expressions in beta_n are then the same F(I_n), with the derived units fixing their identification. A derived input map is represented by a map between K-injective tower complexes using the K-injective Hom-bijection. Its evaluated chain map calculates both sides; chain homotopies remain homotopies after applying F. This proves independence and naturality for derived maps, not only for chosen representatives. Applying the same computation to I_m -> I_n proves the transition equation, including identities and composites. These are explicit computational and normalization clauses of the new statement. The main item applies this result to ordinary global sections and defines the actual composite functor G.

Old steps 5-6 become lem-coef-derived-sections-scalar-coherence, on arbitrary ring sheaves R -> S -> T on a small site. Its future proof must construct sigma from the universal derived unit, not from an unspecified comparison. Restriction is the identity-topos ringed direct image. The global-sections geometric morphism has inverse image the constant sheaf: the constant presheaf preserves finite limits, as does sheafification, and its right adjoint is Hom(1,-) by the sheafification universal property. The structural ring map is the unit from the constant integers to R; modules on the singleton integer-ringed site are abelian groups by the existing exact equivalence. Compose these morphisms and apply the normalized ringed-topos derived composition theorem. For S-K-injective L and R-K-injective replacement j:Res L -> K, Gamma(j) is a quasi-isomorphism; it is precisely the map computing sigma under the derived units. Every derived object has such L, hence sigma is invertible without scalar restriction preserving K-injectives. For R -> S -> T, both sigma_{R,T} and (sigma_{R,S} Res_{S,T}) sigma_{S,T}, after precomposition with eta_T, equal eta_R Res_{R,T}; uniqueness in the universal property makes them equal. The identity comparison follows in the same way. The new statement requires the ringed-topos construction, the representative formula, unit normalization, naturality and cocycle, so none of this work disappears in the re-split.

Old step 7 stays as assembly step 5. Its displayed cancellation explicitly moves the derived map past the natural scalar comparison and cancels the inverse factors, then combines with beta's actual-transition equation. It proves the main item's varying-ring transition statement without introducing a node that merely restates it.

## Sources and searches

I read Stacks sites-cohomology.tex, Tag 0941, label lemma-derived-limit-is-ok, including the paragraph constructing the exact left adjoint to constant-coefficient evaluation, and Tag 0D6E, label lemma-derived-pushforward-composition, including its derived-adjunction proof. I also read derived.tex, Tag 070Y, label lemma-K-injective-defined and the following enough-K-injectives lemma. The two new statements are agent formulations of the extracted arguments, not assertions that either Stacks tag literally states the entire normalized result.

I read the main-20261015 ancestor at blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.md, which gives the statement but no proof. I also read its master predecessor at blueprint/sec-six-functors/sk-prop-sf-biduality-general/prop-coef-integral-exceptional-adjoint.md: the first and last derived mapping-complex comparisons in its second proof paragraph are the inherited place served, through lem-coef-derived-system-evaluation-calculus. The existing ancestor and via chain are retained. The live unit and chapter records were read; no unit or chapter route is changed. Sources for the assembly are the two Stacks tags, not the disallowed SGA sources mentioned historically in the chapter.

Before creating the nodes I searched the whole DAG by statements/titles, tags 0941 and 0D6E, and Lean declaration concepts; blueprint_refs.py ancestor and searches for derived sections, tower evaluation, scalar restriction, derived functor, restriction of scalars, tower right derived, and sections scalar found no blueprint replacement. In particular I read the statements of lem-sp-levelwise-kinjective-tower-image, lem-weil-pbc-tower-derived-evaluation-normalization, lem-cbc-derived-tower-evaluation-normalization, lem-pe-left-module-derived-evaluation-forget, lem-coef-semilinear-derived-sections, lem-pur-diagram-ring-restriction-pushforward, lem-pur-ringed-derived-composition-cocycle, lem-pur-proetale-direct-image-global-evaluation, lem-weil-proetale-direct-image-restriction-of-scalars, and the ring-sheaf-change-adjunction pair. None states either new result under its actual hypotheses.

All new Mathlib searches were executed through msearch.py and are recorded verbatim in searches.jsonl and in each new node. Both nodes have LeanFinder, Loogle, LeanSearch and grep, with a second semantic phrasing and additional grep. I read the results, including RightDerived's rightDerivedDesc, rightDerivedUnique and the naturality formulas, and ChangeOfRings.lean:36-43 (ordinary restrictScalars and Additive). The abstract universal-property declarations do not prove evaluation preservation or coefficient-invariance of unbounded global sections in one line; ordinary restriction of scalars and degreewise cohomology results are not these derived natural isomorphisms. There is no Mathlib leaf. The item's previously logged searches and their 2026-10-21 verdicts are retained.

## Review by Q76

I checked the unchanged item against the live Lean theorem and its package docstring, and checked both extracted statements against the source paragraphs and the full old proof. The human's repair instruction is answered by two separate arguments of comparable substantive size, not by abbreviating the old proof or moving the whole theorem into one new node.

Step 1 cites def-pc-sheaf-restrict-scalars for the unchanged underlying sheaf/action, def-weil-sheaf-of-modules-category for sectionwise kernels and sheafified cokernels, lem-weil-tower-category-levelwise-abelian for componentwise exactness, and lem-weil-pbc-exact-functor-derived-factorization for exact descent to ordinary derived categories. I opened all four statements: they say exactly these facts. There is no flatness hypothesis needed here.

Step 2 uses lem-weil-pbc-small-module-diagrams-grothendieck with the small positive-integer opposite index category and the given small site; lem-weil-pbc-kinjective-functorial-existence gives functorial tower replacements, and prop-pur-kinjective-resolutions-exist gives the individual module replacements. The module-category definition supplies the elementary sectionwise additivity observation. All relevant sheaves, covering indices and tower indices are in the given universe; neither countable-product exactness nor boundedness was inserted.

Step 3 uses the new tower lemma's statement: existence, computation by the same replacement, beta_n, naturality on all derived inputs and the actual-transition equation are explicitly included. Its input assumptions were established in step 2. The lemma requires neither F exact nor an exact left adjoint, which matters for Mod(F_p) -> Ab. Its beta equation has source e_n R(F^Tow) and target (RF)e_n; it is an isomorphism of derived functors rather than merely separate cohomology groups.

Step 4 uses the new scalar lemma's unique unit-normalized isomorphism sigma and its direct-image realization, not a fact hidden in its future proof. The coefficient direction is R -> S and r:D(S) -> D(R). The global ringed morphism goes from (Sh C,R) to (Set,Z), with structural map underline Z -> R, and the comparison is H_S -> H_R r. Its inverse after beta gives the requested direction. No claim that varying-ring evaluation preserves K-injectives is made.

Step 5 uses exactly beta's transition equation and sigma's naturality and cocycle. I expanded the equation algebraically: sigma_{A,S}^{-1} = sigma_{C,S}^{-1}(sigma_{A,C}r_{C,S})^{-1}; naturality moves H_A(r d) past sigma_{A,C,J_{n+1}}, and the middle factors cancel. The remaining map is sigma_{C,S,J_n}^{-1}H_C(d), precisely finite derived sections of the given semilinear transition. This is an elementary cancellation from the cited statements. The argument applies to all m >= n as well as the consecutive case. Every citation has a genuine verbatim quote in citations.json; no proof-only material is cited.

Both new nodes are self-contained statements, with empty proof and proof_deps, no sketches in statement, all notions introduced or defined by explicit dependencies, proper TeX and filled blueprint ancestry. The stored ancestry adds this item ahead of its former via list, as required. I tested the tower result on the identity and zero functors, zero input, non-exact F=Hom(Z/2,-) on Ab, and nonconstant and zero transitions: it needs only additivity and K-injective resolutions. I tested scalar comparison on the one-point site, identity coefficient maps, Z -> Z/2 (non-flat), zero modules and the zero ring. In the one-point test it is the ordinary underlying-complex comparison; the cocycle becomes composition of restrictions. Unbounded inputs are covered by the stated resolution assumptions. No terminal object of C is required, since global sections are Hom(1,-), not evaluation at an unstated final object of the site.

I corrected my initial reading that the accepted live split was simply a stale assignment by finding the later explicit re-split repair note. I retained its seven-step mathematical argument through the two new statement specifications and the allocation above, and removed no statement clause. There are no proof steps above 2000 characters; the assembly is below 3000. No other group, repository file, launcher file or Lean source has been edited.

## Validation

The server dry run exited successfully at c91e3c517c5 with preflight passed, including check_dag and review_split. After that run I clarified the blueprint source paragraph: main-20261015 contains the ancestor statement, while the detailed mapping-complex proof is in the inherited master predecessor. A final dry run follows this report-only clarification.

## Not duplicates

lem-coef-tower-right-derived-evaluation vs def-a1-lisse-section-evaluation: the existing node is about Canonical evaluation of ordinary common-stage sections at a geometric point; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-coef-ringed-sequence-site: the existing node is about Canonical ringed sequence site for the coefficient quotient tower; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-coef-tower-derived-evaluation-transition: the existing node is about Canonical localized transitions between derived tower evaluations; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-fd-integral-pullback-shift-coordinates: the existing node is about Signed integral pullback Roos shift coordinates and derived descent; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-pod-integral-completed-comparison-data: the existing node is about Integral completed-pullback comparison data and signed shift normalization; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-pur-adic-site-strict-quotient-interface: the existing node is about Small-site adic strict quotient interface and canonical normalizations; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-pur-integral-operation-shift-data: the existing node is about Representative-normalized operation and independent-slot shifts; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-pur-principal-cone-tower: the existing node is about Augmented positive-power cone tower of a chain endomorphism; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-pur-principal-koszul-quotient-towers: the existing node is about Canonical principal Koszul and quotient towers with tensor augmentations; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-pur-principal-quotient-completion-model: the existing node is about Principal quotient-completion model with its normalized unit; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-pur-sequence-adjoint-resolution-data: the existing node is about Resolution data for the coefficient sequence projection; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-pur-strict-quotient-completion-data: the existing node is about Strict quotient reduction towers and their canonical completion data; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-pur-synchronized-canonical-maps: the existing node is about The same canonical map at two independent input families; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-pur-tower-product-functor: the existing node is about Termwise product functor on strict tower complexes; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-sbc-strict-projection-tower-data: the existing node is about Normalized strict tower limit and direct-image data; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-sf-adic-module-quotient-data: the existing node is about Canonical adic module quotient functors and transitions; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-sf-integral-open-operations: the existing node is about Pinned integral open coefficient and operation presentation; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-sf-integral-open-reduction-comparison-data: the existing node is about Normalized integral open tensor and reduction comparison data; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-sf-open-semilinear-tensor-model-data: the existing node is about Simultaneous semilinear open tensor model data; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-sf-strict-roos-coordinate-interface: the existing node is about The published strict Roos product, shifted cone, and signed coordinates; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-sf-strict-roos-square-map: the existing node is about Shifted Roos map induced by a commuting square; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-sp-constant-quotient-projection: the existing node is about The canonical single-quotient reduction projection; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-sp-constant-reduction-models: the existing node is about Coupled universal models for strict constant-coefficient reduction; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-trf-coefficient-tower-operations: the existing node is about Coefficient tower operations and point sections; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-trf-compact-support-system-evaluation-diagram: the existing node is about The actual compact-support system evaluation diagram; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-trf-completion-unit-models: the existing node is about Ordinary quotient adjunction and normalized derived completion models; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-trf-integral-tower-inverse-image-unit: the existing node is about Canonical inverse-image tensor unit on entire quotient towers; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-weil-pbc-derived-reduction-model-data: the existing node is about Derived reduction model data and normalized complex comparisons; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-weil-pbc-koszul-reconstruction-models: the existing node is about The fixed Koszul and quotient reconstruction models; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-weil-pbc-ringed-koszul-system: the existing node is about The finite strict Koszul system and its derived-limit presentations; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-weil-strict-roos-model: the existing node is about StrictRoosModel; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs def-zl-field-weil-shriek-shift-data: the existing node is about Canonical field-coefficient Weil compact support and shift data; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-a1-normalized-roos-shift-comparison: the existing node is about The normalized Roos comparison respects integer shifts; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-a1-roos-intrinsic-unit-comparison: the existing node is about The canonical Roos, strict-limit and intrinsic Koszul units agree; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-cbc-completed-pullback-triangles: the existing node is about Completed pullback preserves shifts and distinguished triangles; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-cbc-derived-tower-evaluation-normalization: the existing result derives a left tensor functor using objectwise K-flat resolutions; the new result derives an arbitrary additive functor to the right using K-injectives.

lem-coef-tower-right-derived-evaluation vs lem-coef-constant-tower-roos: the existing node is about Canonical Roos triangle of a completed-coefficient derived tower; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-coef-derived-system-evaluation-calculus: the existing node is about Coherent derived reduction, limit adjunction and fiberwise evaluation; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-coef-derived-tower-counit-projections: the existing node is about Derived constant/limit adjunction with its actual projection counit; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-coef-finite-adjunction-diagram-realization: the existing node is about Finite exceptional operations and enriched adjunction on coherent coefficient systems; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-coef-sequence-global-sections-evaluation: the existing item concerns strict varying-ring systems and the composite sections functor with its finite transitions; this new lemma isolates the reusable arbitrary-additive-functor tower evaluation argument.

lem-coef-tower-right-derived-evaluation vs lem-coef-sequence-projection-derived-adjunction: the existing node is about Derived adjunction of a ringed sequence projection; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-coef-sequence-pushforward-limit-projections: the existing node is about Restricted total-limit comparison with adjunction projections; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-coef-sequence-roos-model: the existing node is about Normalized DVR tower carried by a normalized derived coefficient sequence; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-coef-sequence-sections-limit-comparison: the existing node is about Derived sections and total limit with specified projections; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-fix-cofinal-roos-restriction: the existing node is about Cofinal subsequence comparison of strict Roos complexes; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pod-integral-pullback-system-comparison: the existing node is about For every morphism f:X→Y of schemes with ell invertible, the actual constructible completed integral pullback followed by coherent system reduction is naturally isomorphic to coherent system reduction followed by exact finite-system inverse image; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pod-integral-system-pullback-lift-associativity: the existing node is about Associativity of a fixed fully faithful integral pullback lift; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pod-integral-system-reduction-fully-faithful: the existing node is about Coherent reduction is fully faithful on the full category of derived-complete bounded constructible integral coefficient objects; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-common-stage-tensor-line-coherence: the existing node is about Natural associativity and regular right unit for common-stage tensor; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-compact-support-completed-projection-coherence: the existing node is about Completion coherence for the integral projection mate; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-compact-support-roos-cofinality: the existing node is about Cofinal restriction of a Roos tower complex; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-completed-coefficient-site-data: the existing node is about Exact scalar restrictions, strict-system restriction and derived limit on one site; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-completed-primitive-counit-comparison: the existing node is about Quotient-limit realization and primitive coherent-counit comparisons; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-derived-complete-koszul-reconstruction: the existing node is about Koszul reconstruction of a derived-complete reduction tower; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-finite-free-completion-exchange: the existing node is about Finite free change of rings exchanges quotient completion on arbitrary complexes; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-finite-free-completion-exchange-coherence: the existing node is about Coefficient-tower coherence of the specified quotient-completion exchange; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-finite-free-quotient-roos-comparison: the existing node is about Finite free comparison of the actual quotient Roos complexes before localization; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-injective-tower-roos-shifts: the existing node is about Injective-tower Roos comparison with normalized integer shifts; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-integral-coherence-tower: the existing node is about Coherence identities on normalized integral comparison towers; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-integral-principal-cone-local-criterion: the existing node is about Local vanishing criterion for the independent-universe principal cone completion; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-integral-principal-cone-quotient-augmentation: the existing node is about Normalized levelwise principal-cone augmentation to actual integral quotients; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-integral-principal-cone-quotient-comparison: the existing node is about Unit-preserving scalar-cone comparison with actual finite integral quotients; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-integral-tower-limit-comparison: the existing node is about Derived limit of the strict integral comparison tower; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-principal-koszul-roos-presentation-comparison: the existing node is about Normalized comparison of principal Koszul Roos completion with dual Koszul presentations; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-principal-koszul-roos-reflector: the existing node is about Reflection property of the principal Koszul Roos complex; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-principal-quotient-completion-exists: the existing node is about Existence of unbounded principal quotient completion with normalized unit; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-principal-quotient-roos-derived: the existing node is about Universal derivation of the principal quotient Roos functor on K-flat complexes; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-roos-additive-comparison: the existing node is about Additive comparison for the strict Roos cone; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-pur-strict-quotient-diagonal-normalization: the existing node is about Strict quotient reduction model and completion-unit normalization; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-sf-canonical-open-restriction-model: the existing node is about Canonical open restriction on augmented quotient models; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-sf-cbc-compact-support-composition-limit: the existing node is about Normalized reconstruction of composites of completed operations; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-sf-cbc-extension-zero-completion: the existing node is about Strict reduction of completed extension by zero; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-sf-completion-unit-finite-projection: the existing node is about Projection of the completion unit is the finite scalar-extension unit; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-sf-integral-compactification-system-realization: the existing node is about Coherent integral realization of compactification expressions and their maps; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-sf-open-reduction-adjunction-transport: the existing node is about Open restriction and adjunction transport through actual completion units; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-sf-open-restriction-completeness: the existing node is about Completeness and the actual completion unit after ordinary open restriction; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-sf-perfect-tensor-roos-completion: the existing node is about Perfect tensor quotient coaugmentation and its completion diagrams; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-sf-quotient-tower-evaluation-complex: the existing node is about Explicit finite evaluation of a quotient-tower complex; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-sfb-adic-complete-hom-section-surjective: the existing node is about Compatible finite-reduction morphisms lift into a complete target; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-sfb-adic-complete-reduction-cone: the existing node is about Normalized quotient homotopy-limit cone for a complete object; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-sfb-exact-completed-koszul-pullback: the existing node is about Exact product-preserving inverse image transports the actual Koszul unit; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-sp-completion-mate-comparison: the existing node is about The strict quotient-tower exchange realizes the completed-adjunction mate; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-sp-constant-perfect-quotient-projection: the existing node is about Perfect projection for one constant quotient; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-sp-levelwise-kinjective-tower-image: the existing lemma assumes the input tower is already levelwise K-injective and proves its acyclicity for the tower functor; the new statement compares total right derived functors on every input, with a universal-unit-normalized evaluation isomorphism.

lem-coef-tower-right-derived-evaluation vs lem-sp-proper-open-tower-comparison: the existing node is about Open-adjunction normalization of proper/open interchange on strict coefficient towers; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-sp-slice-restriction-strict-derived-limit: the existing node is about Slice restriction commutes with total derived inverse limit of strict towers; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-trf-compact-support-system-evaluation-coherence: the existing node is about Comparison of strict and enhanced system operation models; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-trf-completion-unit-canonical-models: the existing node is about Compatible ordinary and derived presentations of the coefficient adjunction; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-trf-completion-unit-strict-quotient-model: the existing node is about Actual completion unit on a strict K-flat quotient cone; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-trf-counit-realization-substitution: the existing node is about Whole-counit substitution and scalar normalization for realized operations; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-trf-integral-composition-counit-images: the existing node is about Counit images of the two integral comparison composites; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-trf-integral-cone-counit-realization: the existing node is about The derived-limit counit recovers a compatible tower family from its cone lift; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-trf-integral-pullback-reduction-counit: the existing node is about K-flat reduction-unit counit calculation for integral inverse image; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-trf-isomorphism-multiplication-cone-descent: the existing node is about Multiplication and product comparison descend from strict quotient cones; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-trf-scalar-model-associativity: the existing node is about Scalar-model realization preserves ordinary associativity before completion is inverted; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-trf-scalar-model-unit: the existing node is about The identity scalar model preserves the actual reconstruction unit; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-compact-support-reduction-tower-functor: the existing node is about Coherent compact-support reduction tower functor; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-pbc-completed-fiber-cech-comparison: the existing node is about Published completed Koszul fiber compared with Cech internal Hom; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-pbc-completed-fiber-roos-representative-comparison: the existing node is about The explicit Koszul comparison is compatible with every derived representative; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-pbc-completed-fiber-strict-limit-comparison: the existing node is about Published completed Koszul fiber computes the strict derived limit; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-pbc-completed-koszul-product-comparison: the existing node is about Finite Koszul comparison induces the normalized product-fiber comparison; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-pbc-exact-products-roos-comparison: the existing node is about The normalized Roos fibre computes derived inverse limit with exact products; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-pbc-finite-perfect-adic-coefficient-limit: the existing node is about Actual coefficient limits, finite powers, and compatible finite-projective complex retracts; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-pbc-finite-perfect-adic-complex-roos: the existing node is about Roos limit of a termwise epimorphic completed-module complex tower; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-pbc-finite-perfect-adic-marked-roos: the existing node is about Roos limit of the canonical finite-projective quotient diagram; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-pbc-finite-perfect-adic-realization: the existing node is about Completed realization of uniform finite perfect quotient models; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-pbc-finite-perfect-adic-tower-limit: the existing node is about Specified completed strict limit from a compatible finite-projective marking; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-pbc-ringed-cech-koszul-comparison-existence: the existing node is about Existence of the normalized ringed Koszul Cech comparison; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-pbc-ringed-cech-koszul-comparison-on-site: the existing node is about A unit-compatible Cech Koszul comparison on one ringed site; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-pbc-ringed-cech-koszul-dual-limit: the existing node is about Extended Cech complex and Koszul dual limit; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-pbc-ringed-cech-koszul-hom-limit-comparison: the existing node is about Telescope Hom comparison for a prescribed strict Koszul limit; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-pbc-ringed-strict-tower-homotopy-limit: the existing node is about Strict tower homotopy limit; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-pbc-tower-derived-evaluation-normalization: the existing result requires an exact left adjoint to F; the new result only assumes F additive and enough K-injectives in the source and its tower category. For F:Mod(F_p) -> Ab the left adjoint is tensor with F_p, which is not exact.

lem-coef-tower-right-derived-evaluation vs lem-weil-roos-transition-homotopy: the existing node is about The forward Roos subsequence transition and its explicit homotopy; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-strict-roos-comparison: the existing node is about Natural comparison of strict derived inverse limit and the product cone; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-strict-roos-derivation: the existing node is about StrictRoosDerivation; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-weil-strict-roos-normalization: the existing node is about StrictRoosNormalization; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs lem-zl-left-derived-equivalence-square: the existing node is about Left derived squares under exact equivalences; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-tower-right-derived-evaluation vs prop-weil-pbc-koszul-reconstruction-comparison: the existing node is about Comparison of completed Koszul and quotient derived limits; the new statement is the universal-unit evaluation comparison for an arbitrary additive F and does not require ringed direct image, geometric maps, completions or reduction towers.

lem-coef-derived-sections-scalar-coherence vs def-pur-completed-pushforward-models: the existing node is about Normalized models for completed-coefficient direct image; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs def-pur-ringed-coefficient-change-presentations: the existing node is about Normalized coefficient changes between counit presentations; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs def-pur-ringed-coefficient-counit-presentations: the existing node is about Normalized ringed coefficient counit presentations; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs def-pur-sequence-adjoint-resolution-data: the existing node is about Resolution data for the coefficient sequence projection; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs def-sfb-ringed-derived-comparison-data: the existing node is about Data of normalized derived monoidal comparisons of ringed topoi; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs def-trf-completion-unit-models: the existing node is about Ordinary quotient adjunction and normalized derived completion models; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs def-weil-pbc-adjunction-conjugate: the existing node is about Conjugate transformations of adjoint functors; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs def-weil-pbc-derived-direct-image-composition: the existing node is about Composition isomorphisms of derived direct images (conjugates of those of inverse images); the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-asd-proper-finite-coefficient-extension: the existing node is about Canonical unbounded proper direct-image comparison for finite coefficient extension; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-asd-proper-finite-coefficient-extension-core: the existing node is about Unbounded proper coefficient comparison and restricted projection identity; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-cbc-etale-derived-direct-image-coherence: the existing node is about Ordinary etale derived direct-image composition and its coherence; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-cbc-strict-tower-direct-image-coherence: the existing node is about Coherence of canonical strict-tower direct image and its square mates; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-coef-enriched-sequence-projection-formula: the existing node is about Uncurried finite projections of the enriched sequence adjunction; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-coef-sequence-global-sections-evaluation: the existing item concerns strict varying-ring systems and the composite sections functor with its finite transitions; this new lemma isolates the coefficient comparison for arbitrary composable ring-sheaf maps, with no tower input.

lem-coef-derived-sections-scalar-coherence vs lem-coef-sequence-pushforward-limit-projections: the existing node is about Restricted total-limit comparison with adjunction projections; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-coef-sequence-sections-limit-comparison: the existing node is about Derived sections and total limit with specified projections; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-kun-etale-module-abelian-ringed-presentation: the existing node is about Simultaneous ringed presentations of coefficient forgetting and abelian etale direct image; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-kun-module-abelian-kinjective-direct-image-acyclic: the existing node is about Abelian direct-image acyclicity of a module K-injective complex; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-pe-left-module-derived-evaluation-forget: the existing statement is bounded below and uses constant coefficient rings and evaluation over an object; the new result treats arbitrary ring sheaves, unbounded inputs and all composable coefficient maps.

lem-coef-derived-sections-scalar-coherence vs lem-pur-completed-coefficient-direct-image-diagrams: the existing node is about Normalized completed-coefficient direct image on strict diagrams; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-pur-completed-coefficient-pushforward-comparison: the existing node is about Completed-coefficient pushforward restriction and strict reduction towers; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-pur-completed-coefficient-site-data: the existing node is about Exact scalar restrictions, strict-system restriction and derived limit on one site; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-pur-completed-coefficient-structure-map: the existing node is about Unique completed coefficient structural map from finite projections; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-pur-diagram-ring-restriction-pushforward: the existing statement compares geometric module direct image with coefficient restriction on diagram topoi. It does not identify derived global sections in Ab with the unique universal-unit coefficient comparison or give its coefficient-map cocycle.

lem-coef-derived-sections-scalar-coherence vs lem-pur-perfect-quotient-exchange-normalization: the existing node is about Perfect quotient coefficient exchange with augmentation and completion-unit normalization; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-pur-proetale-direct-image-global-evaluation: the existing node is about Normalized derived global sections after pro-etale direct image; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-pur-ringed-coefficient-change-normalization: the existing node is about Normalized coefficient changes and their naturality; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-pur-ringed-coefficient-derived-presentation-exists: the existing node is about Existence of a normalized derived coefficient presentation; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-pur-ringed-coefficient-projection-cocycle: the existing node is about Coefficient projection cocycle for ordinary derived ringed diagrams; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-pur-ringed-coefficient-restriction-counit: the existing node is about Derived ringed-topos counit under coefficient restriction; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-pur-ringed-derived-composition-cocycle: the existing result assumes normalized ringed-topos morphisms and composition comparisons already supplied; the new statement constructs the global-sections scalar comparisons and identifies them with universal derived units.

lem-coef-derived-sections-scalar-coherence vs lem-pur-ringed-triple-resolution-formulas: the existing node is about Common-resolution formulas for two triple direct-image paths; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-pur-sequence-adjoint-resolution-shifts: the existing node is about Resolution-normalized identification of the sequence-site derived adjoints; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-pur-system-pushforward-restriction-transition: the existing node is about Restriction-form transition of simultaneous derived direct image; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-sf-compact-support-restriction-of-scalars: the existing node is about Finite-level compact-support direct image commutes with restriction of scalars; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-sfb-derived-composition-adjunction-normalization: the existing node is about Derived composition preserves the specified adjunction normalization; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-sfb-exact-compactification-unit-composition: the existing node is about Composition of normalized exact compact-support units; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-sfb-exact-compactification-unit-refinement: the existing node is about Normalized exact compactification units respect canonical refinements; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-sfb-integral-quotient-direct-image-comparison: the existing node is about Unbounded quotient-scalar refinement of integral direct image; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-sfb-proper-open-tower-derived-unit: the existing node is about Derived-unit resolution calculation in a proper/open tower; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-sfb-proper-open-tower-single-unit-formula: the existing node is about Single derived-unit formula in a proper/open tower; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-sfb-proper-open-tower-successive-unit-formula: the existing node is about Successive derived-unit formula in a proper/open tower; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-sfb-ringed-comparison-tensor-adjunction: the existing node is about Tensor and adjunction compatibility of canonical ringed-topos path comparisons; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-sfb-ringed-derived-composition-comparison: the existing node is about Composition comparison with normalized representative formulas; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-sfb-ringed-derived-identity-comparison: the existing node is about Identity comparison with normalized representative formulas; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-sfb-ringed-derived-monoidal-comparisons: the existing node is about Monoidal and adjunction normalization of derived ringed-topos comparisons; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-sfb-ringed-kunneth-factorizations: the existing node is about Two factorizations of the ringed-topos external product comparison; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-sp-restriction-transition-transpose: the existing node is about Scalar-adjunction transpose of a compact-support mixed-coefficient map; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-trf-completion-unit-canonical-models: the existing node is about Compatible ordinary and derived presentations of the coefficient adjunction; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-weil-pbc-frobenius-exchange-restriction: the existing node is about Finite-level exchange is the restricted ambient exchange; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-weil-pbc-ordinary-ringed-exchange-coherence: the existing node is about Identity and pasting for ordinary ambient ringed exchange; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-weil-pbc-ring-sheaf-change-adjunction: the existing node is about Derived adjunctions under compatible changes of ring sheaves; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-weil-pbc-ring-sheaf-change-adjunction-existence: the existing node is about Existence of the normalized derived direct-image comparison; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-weil-pbc-ringed-topoi-derived-pushforward-composition: the existing theorem gives a two-morphism composition isomorphism; the new assertion constructs the global-sections ringed morphism and identifies its coefficient comparison with the unique universal-unit comparison, including scalar cocycles.

lem-coef-derived-sections-scalar-coherence vs lem-weil-proetale-direct-image-restriction-of-scalars: the existing node is about Derived pro-etale direct image commutes with restriction of scalars; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

lem-coef-derived-sections-scalar-coherence vs lem-weil-ringed-tower-pushforward-limit-acyclic: the existing node is about Inverse-limit acyclicity of levelwise pushforward of a K-injective tower; the new statement is the global-sections comparison for arbitrary coefficient-ring sheaf maps, with its universal derived-unit normalization and scalar cocycle, rather than that construction or geometric comparison.

