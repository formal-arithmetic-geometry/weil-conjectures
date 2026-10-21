## Worker report

This repairs A6/D and carries out `coord/repair-notes/det-prop-scalar-six-pullback.json`, the human decision of 2026-10-21 10:53. The returned attempt added no nodes; the retained unpublished retry instead marked a new node split, and its initial dry run in this session failed precisely that status check. Neither retry answered the instruction for statement-only extractions. This delivery has seven new nodes, all status unsplit with empty proof and proof_deps and null proof_origin. The item statement is byte-for-byte unchanged from both the retained returned version and the current read clone. Its complete proof is now a short assembly, rather than the old 11663-character argument. No Lean was written or compiled.

Files written, in the requested report order:

- `dag/nodes/sec-six-functors-basics/det-prop-scalar-six-pullback.json`: split item; statement, stmt_deps, Lean and maintainer review metadata retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-closed-supported-scalar-comparison.json`: statement, unsplit; no exact or one-line Mathlib match. It isolates the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.
- `dag/nodes/sec-six-functors-basics/lem-sfb-exact-open-closed-unbounded-calculus.json`: statement, unsplit; no exact or one-line Mathlib match. It isolates unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.
- `dag/nodes/sec-six-functors-basics/lem-sfb-internal-section-scalar-adjunction.json`: statement, unsplit; no exact or one-line Mathlib match. It isolates transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.
- `dag/nodes/sec-six-functors-basics/lem-sfb-kflat-scalar-comparison-normalization.json`: statement, unsplit; no exact or one-line Mathlib match. It isolates equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.
- `dag/nodes/sec-six-functors-basics/lem-sfb-normalized-immersion-comparison-coherence.json`: statement, unsplit; no exact or one-line Mathlib match. It isolates conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-open-scalar-conjugate-normalization.json`: statement, unsplit; no exact or one-line Mathlib match. It isolates the explicit restriction equation for the already published derived open scalar conjugate.
- `dag/nodes/sec-six-functors-basics/lem-sfb-scalar-inverse-image-tower-diagram.json`: statement, unsplit; no exact or one-line Mathlib match. It isolates the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

Attachments: none. Searching the project source by the item tag and scalar-six notion found the local `Sheaf/SixFunctors/ScalarSixPullback.lean` declaration `AlgebraicGeometry.ProEtale.CondensedRing.scalarSixPullback` at line 534, whose proof is `sorry` at line 541. There is no exact completed project declaration under WeilConjectures. The new-extraction tag/concept search had only an unrelated adic middle-extension comment. Ordinary Mathlib sheaf pullbacks and module scalar adjunctions prove pieces, not these extracted normalizations.

WANTED: none. All source passages needed here are already in the repository.

What was wrong: the earlier proof put all normalization, support-detection and coherence arguments inside the item. The retained report also asserted that the human had authorized proved/split new nodes; the actual repair brief explicitly requires statement-only unsplit nodes. That assertion is corrected here. No statement dispute, hypothesis change, new route or weakened conclusion is involved. The draft's unauthorized additions to the maintainer-owned tool_uses were removed; the live value is preserved, and generic tools needing approval are declared only in split_report.tool_uses.

What is unfinished: the seven extracted lemmas intentionally have no proof steps and join the stage-1 queue. Their arguments are outlined below to make the extraction auditable; these outlines are not installed as proofs in the new nodes. The retained earlier proof, report and full search logs remain under repair/ in this sandbox. Searches already logged were read and reused; new searches were run through msearch.py and their exact tool/query strings copied from searches.jsonl. No search was invented. The item search remains the previously recorded searches, since its statement has not changed.

## The six requested extractions

(a) The retained internal/sectionwise scalar-adjunction lemma is now statement-only. The K-flat normalization lemma isolates the actual balanced coequalizer comparison, its first-factor linearity, descent, mate normalization and geometric composition. This is a technical representative theorem for arbitrary ring sheaves on small topoi; it is not a condensed-scheme restatement of item clause (1).

(b) The new exact-open/closed calculus lemma is stated for abstract abelian categories and supplied exact localization data. It performs the unbounded passage once. I opened both lem-weil-pbc-proetale-ringed-open-closed and det-sf-open-closed-sequence-ring-sheaf: the former supplies exact open/closed functors, invertible restrictions, cross-vanishing and the sheaf short exact sequence for a quasi-compact complement; the latter also requires qcqs and states base-change clauses that this proof does not use. I cite the former, plus the specified module adjunctions in def-weil-pbc-proetale-operations. Neither source is used as if it already asserted unbounded adjunctions. The abstract extraction proves those and detection from exactly the supplied datum. The existing condensed-support-derived-localization node already states the condensed instance, so no second condensed-specific support node is created.

(c) The open-normalization lemma assumes beta_j is the published def-sfb-derived-open-immersion-shriek-iso. Its new content is the explicit equation after applying j^*, with the actual invertible open units and the specified balanced theta. It does not replace that definition or assert existence of another open comparison.

(d) The closed-supported comparison lemma names the three actual arrows of the unit / inverse-theta / counit composite. Its equation and uniqueness characterize this supported B-linear morphism; it does not merely say scalar extension commutes with i_*. It assumes the unbounded support calculus rather than concealing a recollement theorem.

(e) The normalized immersion-coherence lemma is conditional on given functors, coherent restriction maps q and already supplied normalized open/closed isomorphisms d. It proves independence and all mixed composition laws. It does not construct scalar or pullback comparisons. The old locally-closed-extension-coherence node supplies the extension functors, their gamma and restriction Hom bijections, but has no comparison functors F or d, so it cannot replace this extraction.

(f) Existing lem-sfb-successive-derived-quotient-normalization gives tau on arbitrary ring sheaves, including its explicit multiplication and unit formulas, so repeating it would be a duplicate. The new ordinary tower-diagram lemma isolates the missing inverse-image/tau equality before localization. The last conditional assertion of the new immersion-coherence lemma supplies the beta/tau square once this equality is known. Thus both tower squares leave the item proof, without a new node that simply asserts all of clause (3).

## Review by Q20

I read the current main-20261015 chapter and sk-prop-scalar-six unit, especially its pullback/extension-by-zero step 2, the item statement and all three paragraphs of its proof source, the human repair note, and the returned entry. I retained the alternative open-adjunction route and the closed supported-unit calculation already independently reviewed by Q60. I read Stacks sites-modules.tex Section 03EK and Tag 0GMW for balanced sheaf tensors and sheafification, Tag 03EL (lemma-tensor-product-pullback), sites-cohomology.tex Tags 0G7E (lemma-pullback-K-flat) and 0D6D (lemma-derived-pullback-composition), proetale.tex Tags 09BM and 09AH for the retrocompact exactness and actual sheaf sequence, and categories.tex Tag 0B65 for conjugation normalization. These are supporting passages for the agent-extracted technical lemmas, not a claim that Stacks states the new multi-clause normalizations verbatim. No SGA route is used.

For step 1 I checked that the new scalar-transport statement supplies exactly the restriction/extension adjunction identification, including derived units, and that the existing operations-transport statement handles geometric and open operations. It does not handle changing the scalar ring; that missing comparison is why the retained new node is necessary. lem-sfb-alpha-iso is for every condensed ring, not only admissible rings. The coefficient-change statement explicitly supplies the commuting ring square. Consequently the rings and their maps on X are the inverse images required by the next lemma.

For step 2 I checked that the new K-flat normalization statement supplies both the specified theta and its composition equation, not merely an unrelated pullback isomorphism. Its inverse-image comparison is B-linear on the first factor. Both K-flatness and flatness of the terms are required, and the resolution node supplies both. The mate is identified by its scalar-unit formula, avoiding the error of silently replacing a chosen comparison by an arbitrary isomorphism.

For step 3 I verified the field/finite-type Noetherian argument, and that the open-Noetherian lemma applies on every affine chart as well as globally. Thus the complements are retrocompact, the precise hypothesis needed by 09BM; no assertion about exact i_* for arbitrary complements is used. The ring-sheaf node supplies exact functors, the two invertible restriction maps and both cross-vanishings. The operations definition explicitly constructs i^* adjoint to i_* and proves inverse image exact; its specified unit/counit are those used in the sheaf sequence. These give all the abstract calculus hypotheses. That lemma states actual unbounded adjunctions and joint detection, so step 3 uses its statement rather than a bounded-below result or a proof hidden in another node.

For step 4 I checked the open definition and its cited derived restriction square. The new lemma identifies the restriction of that very conjugate with theta inverse using the actual open units. The formula is typed from j_B^* T_X j_! M to T_U M. It is not an assumption that two arbitrary scalar isomorphisms agree. For step 5 the new closed statement supplies exactly the B-linear three-arrow formula, invertibility and epsilon normalization. In its formula theta_i is evaluated on i_{*,A}M, so its inverse has the source i_B^*H required by the unit arrow. Vanishing on U follows from theta_j and j^*i_*=0; closed detection is therefore applicable. No B-linearity is inferred just by forgetting to A-modules.

For step 6 I checked the coherence lemma's hypotheses against steps 2, 4 and 5, using q=theta inverse. The extension-coherence statement gives the canonical gamma maps, factorization identifications and the restriction Hom bijection. A source F_X E_a M lies in the target extension image because the open/closed composite is already an isomorphism to E_a F_S M; faithfulness is used only after that fact. This is also why the factorization-comparison and mixed composition assertions are justified. For step 7 I checked that the existing successive-derived-quotient-normalization statement covers arbitrary ring sheaves, contains the unit formula, and asserts no coefficient flatness. It combines with the new scalar transport, not with an implicit identification of coefficient categories.

For step 8 I checked the ordinary tower equation and its direction. Its two routes start at h_C^*(C tensor_B (B tensor_A P)) and end at C_X tensor_{A_X} h_A^*P. They agree by the two balanced relations. A flat-term K-flat P and the K-flat-preservation lemma give common representatives for successive scalar changes and geometric pullback, so the localized equality is exactly the theta/tau square. With q=theta inverse, this is the t-compatibility premise in the last assertion of the new immersion lemma, which states exactly the required beta/tau equation. No comparison square is left as an unproved assertion inside the item. citations.json quotes the entire verbatim statement of each node used by each item step; each part taken above occurs in that quoted statement.

I tested identity and empty immersions, the zero ring and zero complexes, pure open and pure closed factorizations, and identity coefficient maps. The supported-unit formula reduces to the adjunction triangle for the identity immersion. Empty strata give maps between zero objects. The abstract calculus works also for a zero component category. For a non-flat test Z/ell^2 -> F_ell, the derived tensor can be unbounded; the new statements use flat-term K-flat representatives and impose no boundedness, so none accidentally replaces derived tensor by ordinary tensor on the original complex. The tower diagrams also permit a zero or identity intermediate ring. All of these checks preserve the exact item statement.

Mathlib hits were read: SheafOfModules.pullbackComp, conjugateEquiv_pullbackComp_inv and pullback_assoc concern ordinary pullback functors; ModuleCat.extendScalarsComp and homEquiv_extendScalarsComp concern ordinary modules; iterated_mateEquiv_conjugateEquiv and unit_mateEquiv are generic mate identities. They do not supply the ring-sheaf derived normalizations, support construction, or conditional immersion assembly in one line. The generic mate nodes already present in the DAG can be used when the extracted lemmas are split. The exact-functor search found Functor.mapDerivedCategory and its factorization, which is only the descent part of the abstract support theorem. Invalid Loogle identifiers were recorded as invalid patterns, never counted as absence evidence; both semantic services and source grep were also run for those nodes.

No new node has proof steps, so there is no new proof longer than the requested module scale. The item has eight short steps, none longer than 400 characters. The previous complete arguments are archived, not discarded or installed as oversized new proofs.

## Not duplicates

The entire DAG was searched by concepts and source tags, and the imported blueprint was searched by scalar/pullback, open/conjugate, closed/unit/comparison, factorization/faithfulness, unbounded/detection, balanced tensors and coefficient towers. Search outputs are retained under repair/. The ancestor is the item itself; all new from.place fields identify its precise proof paragraph and same_as is empty. Particularly close nodes were opened in full: internal-module-operations-transport has no scalar-ring-change theorem; internal-section-tensor-comparison fixes one ring; proetale-inverse-image-tensor-comparison is underived and has no scalar-adjunction mate; sf-scalar-pullback-composition has constant ordinary rings on etale sites; condensed-support-derived-localization is a concrete internal-coefficient instance; locally-closed-extension-coherence has no F/d comparison data; successive-derived-quotient-normalization already supplies tau and is reused. The extraction source tags also occur on many remote topics; the per-pair inventory below identifies their distinct subjects, rather than treating a shared tag as an exact match.

lem-sfb-closed-supported-scalar-comparison vs det-formal-closed-support-ii-left-exact: existing subject is "Left $t$-exactness of sections with closed support"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs det-formal-closed-support-ii-limits: existing subject is "Closed support commutes with derived limits of sequences"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs det-lem-formal-closed-support-sheaves: existing subject is "Sections with support: the sheaf-level adjunction"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs det-lem-int-ext-bound: existing subject is "Uniform vanishing of Ext between integral constructible sheaves"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs det-prop-closed-adjoint-constructible-support: existing subject is "Sections with support of a constructible complex are constructible"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs det-proper-heart-bound-lattice: existing subject is "The lattice bound $2d+1$"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs det-sf-comp-coherence-refinement: existing subject is "The refinement map on the localizing category"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs det-sf-comp-composition-base-change: existing subject is "Base change for $Rf_!$ on the localizing category"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs det-sf-comp-composition-interchange: existing subject is "Interchanging proper direct image and extension by zero"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs det-sfb-dc-restricted-functors-closed-image: existing subject is "Extension by zero and closed direct image preserve integral constructible complexes"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs det-uniform-constructible-ext-integral: existing subject is "The integral stratum bound"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-cbc-extension-zero-stratified-perfect: existing subject is "Extension by zero preserves stratified perfect local models"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-formal-closed-pullback-derived-products: existing subject is "Closed coefficient-compatible pullback preserves derived products"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-pur-closed-support-exceptional-comparison: existing subject is "Comparison of closed support with the transported finite exceptional value"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-sf-proetale-open-closed-sequence: existing subject is "Open-closed short exact sequence on the pro-etale site"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-sf-ring-sheaf-closed-localization: existing subject is "Closed localization for arbitrary pro-etale ring-sheaf module objects"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-sf-ringed-closed-kernel-adjoint: existing subject is "The support-kernel adjoint for an arbitrary pro-etale ring sheaf"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-sfb-condensed-support-derived-localization: existing subject is "Open/closed localization for ordinary derived condensed module objects"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-sfb-condensed-support-projection-formula: existing subject is "Natural support tensor projection formulas on unbounded condensed modules"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-sfb-local-integral-perfect-model-cohomology: existing subject is "Cohomology of a local integral perfect scalar model"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-sfb-locally-closed-extension-coherence: existing subject is "Restriction and composition for locally closed extension by zero"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-sfb-locally-closed-module-extension-coherence: existing subject is "Normalized locally closed extension on module sheaves"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-sfb-open-closed-flatness: existing subject is "Flatness detected on a complementary open and closed pair"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-sfb-open-filtration-successor: existing subject is "Natural quotient for two nested open module pieces"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-sfb-proetale-fixed-scalar-zero-detection: existing subject is "Complementary restrictions detect zero fixed-scalar pro-etale sheaves"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-sfb-proetale-identified-open-closed: existing subject is "Exact open and closed extensions with identified inverse-image coefficients"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-sfb-proetale-identified-supported-reconstruction: existing subject is "Normalized supported reconstruction for actual tensor pullbacks"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-sfb-proetale-locally-closed-extension: existing subject is "Pointwise exact locally closed extension"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-sfb-proetale-open-disjoint-direct-image: existing subject is "Direct image restricts to zero on a disjoint pro-etale open"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-sfb-proetale-supported-reconstruction: existing subject is "Normalized reconstruction from two successive support conditions"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-weil-pbc-condensed-open-closed-recollement: existing subject is "Open/closed recollement for condensed coefficient modules"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-weil-pbc-noetherian-stratum-detection: existing subject is "Finite stratified restrictions detect pro-etale sheaves"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-weil-pbc-proetale-abelian-closed-counit: existing subject is "The closed counit on abelian pro-etale sheaves"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-weil-pbc-proetale-abelian-closed-support: existing subject is "Closed support for abelian pro-etale sheaves"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-weil-pbc-proetale-immersion-limit-preservation: existing subject is "Inverse images along immersions preserve pro-etale limits"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-weil-pbc-proetale-inverse-image-limits-zariski-local: existing subject is "Zariski locality of preservation of pro-etale inverse-image limits"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-weil-pbc-proetale-restriction-preserves-limits: existing subject is "Limits preserved by weakly etale pro-etale restriction"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-weil-pbc-proetale-ringed-closed-counit: existing subject is "Closed ringed counit is invertible"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-weil-pbc-proetale-ringed-localization-sequence: existing subject is "Ringed local open-closed short exact sequence"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-weil-pbc-proetale-ringed-open-closed: existing subject is "Ringed pro-etale open-closed localization"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs lem-weil-pbc-wcontractible-closed-localization: existing subject is "Closed localization of a w-contractible ring"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs new-lem-weil-pbc-condensed-finite-model-immersion-restriction: existing subject is "finite model on immersion range"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs new-lem-weil-pbc-condensed-surjective-closed-equivalence: existing subject is "condensedSurjectiveClosedPullback isEquivalence"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs new-lem-weil-pbc-condensed-surjective-closed-local-presentation: existing subject is "lfp lowerStar of surjective closed"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs sk-lem-formal-closed-support-ii: existing subject is "Closed support, truncation and derived limits"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs sk-lem-int-ext: existing subject is "Continuity and boundedness of Ext"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs sk-lem-int-tensor: existing subject is "Inverse image and tensor product"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs sk-lem-proper-heart-bound: existing subject is "A uniform bound for proper direct image"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-closed-supported-scalar-comparison vs sk-lem-uniform-constructible-ext: existing subject is "Uniform Ext bound"; this extraction specifies the new-coefficient-linear supported-unit formula and its unique closed-restriction normalization.

lem-sfb-exact-open-closed-unbounded-calculus vs def-a1-finite-adic-open-section-data: existing subject is "Finite adic open extension and fibre data"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs def-coef-semilinear-derived-calculus: existing subject is "Ordinary derived semilinear calculus interfaces"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs def-pd-proetale-section-module-functors: existing subject is "Normalized tensor structures on existing pro-etale section-module functors"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs def-pd-section-derived-realization: existing subject is "Canonical derived section-module realization"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs def-pd-section-derived-tensor-data: existing subject is "Canonical derived section-module tensor data"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs def-pd-section-module-operations-data: existing subject is "Existing section-module operations and pure-tensor data"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs def-sf-open-normalization-data: existing subject is "Geometric and operation data for open tensor normalization"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs def-sfb-adic-residue-lift-comparisons: existing subject is "The coefficient comparisons and actual finite-reduction Hom tower"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs def-sp-varying-ring-operations: existing subject is "Canonical geometric operations on varying-ring systems"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs def-weil-pbc-local-coefficient-localization: existing subject is "Coefficient localization and local section multiplication on a ringed site"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs def-weil-pbc-ringed-derived-restriction: existing subject is "RingedDerivedRestriction"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs det-formal-closed-support-ii-left-exact: existing subject is "Left $t$-exactness of sections with closed support"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs det-lem-formal-closed-support-sheaves: existing subject is "Sections with support: the sheaf-level adjunction"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs det-prop-closed-adjoint-constructible-support: existing subject is "Sections with support of a constructible complex are constructible"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs det-proper-heart-bound-lattice: existing subject is "The lattice bound $2d+1$"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs det-sf-comp-coherence-refinement: existing subject is "The refinement map on the localizing category"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs det-sf-comp-composition-base-change: existing subject is "Base change for $Rf_!$ on the localizing category"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs det-sf-comp-composition-interchange: existing subject is "Interchanging proper direct image and extension by zero"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs det-sfb-dc-restricted-functors-closed-image: existing subject is "Extension by zero and closed direct image preserve integral constructible complexes"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs det-uniform-constructible-ext-integral: existing subject is "The integral stratum bound"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-cbc-extension-zero-stratified-perfect: existing subject is "Extension by zero preserves stratified perfect local models"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-cbc-localized-extension-zero-linear-derived: existing subject is "Module extension by zero is linear on the unbounded derived category"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-pc-inverse-image-open-free-sheaf: existing subject is "Inverse image of a represented open free abelian sheaf"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-pc-open-embedding-sheaf-pullback-injectives: existing subject is "Open embedding sheaf pullback preserves injectives"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-pc-open-free-restriction-hom: existing subject is "Restriction of morphisms from the image-open free sheaf"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-pc-open-inverse-image-injectives: existing subject is "Open inverse image preserves injective abelian sheaves"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-pc-open-restriction-ext-bijective: existing subject is "Bijectivity of the constructed open-restriction Ext maps"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-pur-closed-support-exceptional-comparison: existing subject is "Comparison of closed support with the transported finite exceptional value"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-pur-site-restriction-module-adjunction-exact: existing subject is "Restriction and extension by zero for modules on a localized site"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sf-open-operation-models: existing subject is "Open operation comparisons with fixed tensor models and right square"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sf-proetale-open-closed-sequence: existing subject is "Open-closed short exact sequence on the pro-etale site"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sf-ring-sheaf-closed-localization: existing subject is "Closed localization for arbitrary pro-etale ring-sheaf module objects"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sf-ringed-closed-kernel-adjoint: existing subject is "The support-kernel adjoint for an arbitrary pro-etale ring sheaf"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sf-site-finite-projective-lift: existing subject is "exists local lift overMap from finiteFree"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sf-site-finite-projective-section: existing subject is "exists local section overMap of finiteFree retract"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sf-site-perfect-derived-restriction-iso: existing subject is "overFunctor derivedRestrictionIso"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sf-site-perfect-lower-model: existing subject is "exists strictPerfect lower model"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sf-site-perfect-opcycles-retract: existing subject is "exists local retract opcycles of perfect tor"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sf-site-perfect-opcycles-retract-transport: existing subject is "transport slice retract"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sf-site-perfect-overmap-additive: existing subject is "sitePerfectOverMap additive"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sf-site-perfect-overmap-comp: existing subject is "sitePerfectOverMapComp"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sf-site-perfect-overmap-exact: existing subject is "overMap exact ofUniverses"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sf-site-perfect-package-map: existing subject is "StrictPerfectCoefficientPackageOnSite.map"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sf-site-perfect-restriction-additive: existing subject is "sitePerfectOverFunctor additive"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sf-site-perfect-restriction-exact: existing subject is "overFunctor exact ofUniverses"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sf-site-perfect-upper-model: existing subject is "exists strictPerfect upper model"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sfb-condensed-support-derived-localization: existing subject is "Open/closed localization for ordinary derived condensed module objects"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sfb-condensed-support-projection-formula: existing subject is "Natural support tensor projection formulas on unbounded condensed modules"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sfb-locally-closed-extension-coherence: existing subject is "Restriction and composition for locally closed extension by zero"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sfb-locally-closed-module-extension-coherence: existing subject is "Normalized locally closed extension on module sheaves"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sfb-open-closed-flatness: existing subject is "Flatness detected on a complementary open and closed pair"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sfb-open-filtration-successor: existing subject is "Natural quotient for two nested open module pieces"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sfb-proetale-fixed-scalar-zero-detection: existing subject is "Complementary restrictions detect zero fixed-scalar pro-etale sheaves"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sfb-proetale-identified-open-closed: existing subject is "Exact open and closed extensions with identified inverse-image coefficients"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sfb-proetale-identified-supported-reconstruction: existing subject is "Normalized supported reconstruction for actual tensor pullbacks"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sfb-proetale-locally-closed-extension: existing subject is "Pointwise exact locally closed extension"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sfb-proetale-open-disjoint-direct-image: existing subject is "Direct image restricts to zero on a disjoint pro-etale open"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sfb-proetale-supported-reconstruction: existing subject is "Normalized reconstruction from two successive support conditions"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sp-slice-restriction-strict-derived-limit: existing subject is "Slice restriction commutes with total derived inverse limit of strict towers"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-weil-pbc-condensed-open-closed-recollement: existing subject is "Open/closed recollement for condensed coefficient modules"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-weil-pbc-element-presheaf-extension: existing subject is "Direct-sum computation and left exactness of presheaf element extension"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-weil-pbc-extension-by-zero-exact: existing subject is "Extension by zero is exact (étale site)"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-weil-pbc-noetherian-stratum-detection: existing subject is "Finite stratified restrictions detect pro-etale sheaves"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-weil-pbc-proetale-abelian-closed-support: existing subject is "Closed support for abelian pro-etale sheaves"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-weil-pbc-proetale-ringed-localization-sequence: existing subject is "Ringed local open-closed short exact sequence"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-weil-pbc-proetale-ringed-open-closed: existing subject is "Ringed pro-etale open-closed localization"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-weil-pbc-ringed-slice-extension-preserves-exact: existing subject is "Ringed-slice extension preserves exactness"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-weil-pbc-site-extension-by-zero-exact: existing subject is "Extension by zero on a localized site is exact"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-weil-pbc-site-restriction-exact: existing subject is "Restriction to a localized site is exact"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-weil-pbc-site-restriction-injectives: existing subject is "Extension by zero and restriction on a localized site"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-weil-pbc-wcontractible-closed-localization: existing subject is "Closed localization of a w-contractible ring"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-weil-pbc-zariski-etale-pushed-resolution: existing subject is "Local vanishing gives the pushed injective-resolution augmentation as a quasi-isomorphism"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-weil-pbc-zariski-etale-pushed-resolution-finite-limits: existing subject is "Finite-limit preservation for the pushed resolution"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-weil-pbc-zariski-etale-pushed-resolution-quasi-iso: existing subject is "Quasi-isomorphism of the pushed resolution augmentation"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-weil-pbc-zariski-extension-by-zero-exact: existing subject is "Extension by zero of abelian Zariski sheaves is exact"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs new-lem-weil-pbc-condensed-finite-model-immersion-restriction: existing subject is "finite model on immersion range"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs new-lem-weil-pbc-condensed-surjective-closed-equivalence: existing subject is "condensedSurjectiveClosedPullback isEquivalence"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs new-lem-weil-pbc-condensed-surjective-closed-local-presentation: existing subject is "lfp lowerStar of surjective closed"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs new-localized-restriction-extension-exists-universes: existing subject is "Exact extension adjoint for localized restriction with independent coefficient universe"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs new-open-embedding-sheaf-pullback-adjunction: existing subject is "Extension by zero adjunction for open embeddings"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs new-open-embedding-sheaf-pullback-preserves-monomorphisms: existing subject is "Open embedding sheaf pullback preserves monomorphisms"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs new-over-pullback-adjunction-mono: existing subject is "Extension by zero adjunction preserving monomorphisms"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs new-over-pullback-preserves-injectives: existing subject is "Restriction to a slice Grothendieck site preserves injective abelian sheaves"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs sk-lem-int-tensor: existing subject is "Inverse image and tensor product"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs sk-lem-proper-heart-bound: existing subject is "A uniform bound for proper direct image"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-exact-open-closed-unbounded-calculus vs sk-lem-uniform-constructible-ext: existing subject is "Uniform Ext bound"; this extraction specifies unbounded descent, detection and supported-unit normalization for arbitrary exact abelian localization data.

lem-sfb-internal-section-scalar-adjunction vs adic-unit-exists-data: existing subject is "Existence of the identity scalar-extension unit map"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-kun-prime-coefficient-complexes: existing subject is "Degree zero complexes and localization"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-kun-prime-coefficient-complexes-input-output: existing subject is "Ordinary source and target tensor complexes"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-kun-prime-coefficient-constructions: existing subject is "Canonical quotient coefficient tensor arrow"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-kun-prime-coefficient-functors: existing subject is "Punctual tensor source and target functors"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-kun-prime-coefficient-iso: existing subject is "Derived coefficient tensor isomorphism type"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-kun-prime-coefficient-localization-compatibility: existing subject is "Localized termwise coefficient compatibility"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-kun-prime-coefficient-normalization: existing subject is "Derived normalization by the quotient tensor map"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-kun-prime-coefficient-pullbacks: existing subject is "Canonical coefficient pullback maps"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-kun-prime-coefficient-term-map: existing subject is "Degree zero coefficient term map"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-kun-prime-coefficient-termwise-normalization: existing subject is "Termwise normalization of the quotient tensor arrow"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-pd-proetale-section-module-functors: existing subject is "Normalized tensor structures on existing pro-etale section-module functors"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-pd-section-module-operations-data: existing subject is "Existing section-module operations and pure-tensor data"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-pur-finite-tate-site-comparison: existing subject is "Finite Tate tensor generators and root-normalized site comparison predicates"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-pur-inverse-image-tensor-hom-sections: existing subject is "Tensor, scalar and unit-section conventions for module inverse image"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-pur-kummer-module-coefficients: existing subject is "Kummer sheaves with module coefficients and their scalar actions"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-pur-operation-scalar-transport: existing subject is "Pure-tensor and derived-counit normalized operation scalar transport"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-pur-presheaf-tensor-product: existing subject is "Presheaf tensor product of modules"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-pur-sheaf-tensor-product: existing subject is "Tensor product of sheaves of modules on a site"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-pur-twist-coefficient-rings: existing subject is "The canonical discrete and completed scalar square of the Tate twist"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-sfb-internal-section-total-comparison: existing subject is "Canonical internal-to-sectionwise total-complex comparison"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-sp-scalar-tensor-comparison-data: existing subject is "Normalized tensor and scalar-extension comparison data"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-sp-semilinear-constant-ring-operations: existing subject is "Constant-ring semilinear system operations and normalized evaluation mates"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-trf-singleton-site-operations: existing subject is "Punctual ringed-site operations and normalized comparison predicates"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-weil-pbc-ringed-tensor-section-calculus: existing subject is "Section calculus for the actual sheaf tensor and scalar extension"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs def-zl-pbc-finite-raw-scalar-comparison: existing subject is "Canonical comparison of normalized and embedding finite-field scalar extension"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-exc-constant-field-sheaf-tensor-cohomology: existing subject is "Tensoring over a constant field sheaf commutes with cohomology"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-exc-intrinsic-realization-tensor-complex: existing subject is "Intrinsic realization commutes with ordinary total tensor complexes"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pc-balanced-sheaf-tensor-comparison-isIso: existing subject is "Invertibility of the canonical balanced sheaf tensor map"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pc-balanced-sheaf-tensor-contraction: existing subject is "Balanced contraction on sheaf tensors"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pc-balanced-sheaf-tensor-original-sections-ext: existing subject is "Original-section extensionality for restricted balanced sheaf tensors"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pc-sheaf-modules-tensor-closed: existing subject is "Sheaves of modules on a site form a symmetric monoidal closed category"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pc-sites-module-sheafification-bilinear-extension: existing subject is "Bilinear maps extend through module sheafification"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pc-sites-module-sheafification-bilinear-extension-existence: existing subject is "Existence of bilinear sheafification extension"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pc-sites-module-sheafification-bilinear-extension-uniqueness: existing subject is "Uniqueness of bilinear sheafification extension"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pc-sites-module-sheafification-tensor: existing subject is "Tensor and sheafification for modules over a presheaf of rings"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pc-sites-sheaf-tensor-bilinear-universal: existing subject is "Universal property of sheaf tensor product"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pe-internal-section-tensor-comparison: existing subject is "Relative tensor and K-flatness under the internal-to-sectionwise module equivalence"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-per-galois-descent-monodromy-tensor: existing subject is "Monodromy and tensor of modules descended along a finite Galois cover"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-per-local-system-tensor-monodromy: existing subject is "Tensor comparison for arbitrary torsion local systems"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-change-of-rings-tensor-cancellation: existing subject is "Natural cancellation of scalar extension in sheaf tensors"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-change-of-rings-tensor-cancellation-independent: existing subject is "Natural tensor cancellation in independent coefficient universes"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-change-of-rings-tensor-comparison: existing subject is "Natural comparison of restricted scalar extension and sheaf tensor"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-constant-finite-free-power-iso: existing subject is "Finite-basis coordinates for constant scalar extension"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-constant-finite-free-products: existing subject is "Countable products and finite-free constant scalar extension"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-constant-finite-free-section-basis: existing subject is "Compatible sectionwise bases of constant coefficient extensions"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-etale-constant-module-flat: existing subject is "Flatness under constant-scalar realization"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-etale-constant-module-tensor: existing subject is "Constant-coefficient realization commutes naturally with right tensor"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-inverse-image-scalar-comparison: existing subject is "Inverse image commutes with extension of scalars, with its unit formula"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-inverse-image-tensor-comparison: existing subject is "The unit-normalized tensor comparison for an isomorphic base change"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-kummer-finite-biproducts: existing subject is "Integral finite-basis cohomology and Kummer exactness"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-kummer-finite-free-comparison: existing subject is "Normalized finite free Kummer cohomology comparison"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-kummer-integral-root-comparison: existing subject is "Integral basis reduction for the Kummer root sheaf"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-module-tensor-generator-calculus: existing subject is "Pure tensors and normalized insertion naturality for sheaf modules"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-module-tensor-monoidal-equations: existing subject is "Associativity and symmetry of the canonical ordinary module tensor comparison"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-proetale-inverse-image-tensor-comparison: existing subject is "Pure-tensor description and coherence of the pro-etale inverse-image tensor comparison"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-system-cochain-tensor-reduction: existing subject is "Cochain scalar-adjoint tensor formula for strict systems"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-system-ordinary-tensor-reduction: existing subject is "Ordinary scalar-adjoint tensor formula for strict systems"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-tensor-pushout-action: existing subject is "A sectionwise scalar pushout acts uniquely on a balanced tensor sheaf"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-twist-coefficient-comparison: existing subject is "The canonical coefficient pushout comparison is invertible"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-twist-coefficient-tensor: existing subject is "Finite integral coefficient extension commutes with sheafwise completion"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-pur-twist-integral-local-models: existing subject is "Scalar-extension local models of the integral root line"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sc-hom-tensor-comparison-natural: existing subject is "Naturality of the sheaf tensor comparison isomorphism"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sc-hom-tensor-reverse-pair: existing subject is "Reverse currying for one pair of module sheaves"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sc-hom-tensor-section-natural: existing subject is "Naturality of the canonical presheaf-to-sheaf tensor map"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sc-hom-tensor-summand-localized-ext: existing subject is "Localized pure-tensor extensionality for a sheaf tensor"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sc-hom-tensor-summand-restriction-ext: existing subject is "Internal Hom maps determined by total tensor summand restrictions"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sc-internal-hom-coproduct-fan: existing subject is "Internal Hom of a coproduct is a product"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sc-internal-hom-product-fan: existing subject is "Internal Hom preserves integer-indexed product fans"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sc-local-bilinear-sheafification-tensor: existing subject is "Local bilinear presheaf pairings extend to sheaf tensor products"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sf-completed-tensor-finite-shift: existing subject is "Signed right shifts of the strict finite tensor tower"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sf-finite-field-local-tensor-model: existing subject is "Localized inverse-image constant models under field scalar extension"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sf-proetale-residue-module-tensor-homology: existing subject is "Ordinary tensor homology for modules over a constant field quotient"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sf-proetale-sheafification-tensor-comparison: existing subject is "Tensor/sheafification comparison in the pro-etale site universes"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sfb-proetale-intrinsic-tensor-comparison: existing subject is "Right-tensor comparison for intrinsic constant-ring realization"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sfb-scalar-ordinary-tensor-comparison: existing subject is "Normalized ordinary scalar tensor comparison in independent site universes"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sp-finite-free-scalar-models: existing subject is "Existence of normalized actual-restriction scalar models"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sp-scalar-extension-binary-coherence: existing subject is "Normalized binary scalar-extension comparisons"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sp-scalar-extension-dual-evaluation: existing subject is "Explicit scalar-extension evaluation on internal duals"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sp-scalar-extension-dual-local-iso: existing subject is "Local rank-one scalar extension and dual invertibility"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-sp-scalar-extension-dual-tower-core: existing subject is "Dual comparisons and binary scalar-extension tower squares"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-w2-inverse-image-change-of-rings-unit-smul: existing subject is "Scalar compatibility of the inverse-image change-of-rings unit"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-weil-pbc-continuous-module-encoding-lattices: existing subject is "Local freeness and lattice compatibility of the explicit continuous encodings"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-weil-pbc-continuous-module-encoding-scalar-extension: existing subject is "Scalar extension under the continuous integral and rational module encodings"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-weil-pbc-extension-tensor-comparison: existing subject is "Restricted scalar extension as a sheaf tensor product"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-weil-pbc-free-sheaf-flat: existing subject is "The sheafified free presheaf on a representable with flat coefficients is flat (j_{X!} of a constant flat sheaf is flat)"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-weil-pbc-scalar-extension-tensor-comparison: existing subject is "Scalar extension preserves the normalized sheaf tensor"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-weil-pbc-scalar-localization-complex-colimit: existing subject is "Ordinary scalar-sequence colimit of complexes"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-weil-pbc-scalar-localization-module-colimit: existing subject is "Scalar localization as an ordinary module-sheaf colimit"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-weil-pbc-scalar-tensor-comparison-universes: existing subject is "Scalar-extension tensor associativity on underlying abelian sheaves in independent universes"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-weil-pbc-sheaf-tensor-closed: existing subject is "A-valued sheaves on an essentially small site: Grothendieck abelian, symmetric monoidal closed under the sheafified tensor product"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-weil-pbc-tensor-local-bijection-universes: existing subject is "Tensoring a local module bijection commutes with sheafification in independent universes"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-weil-point-sections-tensor-shift: existing subject is "Sections-tensor comparison commutes with shifts"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-internal-section-scalar-adjunction vs lem-weil-sheaf-scalar-extension-ring-iso: existing subject is "Scalar extension along an isomorphism of ring sheaves"; this extraction specifies transport of the scalar adjunction between internal and sectionwise module categories, including its derived units.

lem-sfb-kflat-scalar-comparison-normalization vs def-a1-proper-sections-germ-and-moving-point: existing subject is "Canonical proper compact rational germs and semilinear moving points"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-coef-semilinear-geometry-base: existing subject is "Geometry base fields for coefficient linear operations"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-coef-semilinear-geometry-derived: existing subject is "Derived geometric system operations and normalization"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-coef-semilinear-geometry-ops: existing subject is "Canonical geometric mate and projection words"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-coef-semilinear-system-models: existing subject is "Generic strict semilinear system constructions and representative normalization"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-per-derived-hom-pullback: existing subject is "Canonical pullback on shifted etale derived Hom"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-pur-change-of-rings-complex: existing subject is "Termwise change of rings of a cochain complex"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-pur-cochain-coefficient-arrows: existing subject is "Canonical scalar-association and transition arrows on cochain sheaves"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-pur-cochain-coefficient-universe-transport: existing subject is "Canonical common-universe transport of ring and module sheaves"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-pur-cochain-tensor-coherence-data: existing subject is "Canonical cochain ringed-pullback and coherence data"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-pur-derived-constant-pullback-comparison: existing subject is "Canonical derived constant-sheaf pullback comparison"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-pur-etale-scalar-pullback-iso: existing subject is "Canonical derived scalar and pullback isomorphism"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-pur-open-coefficient-normalizations: existing subject is "Exact-pullback and open-unit coefficient normalizations"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-pur-ringed-coefficient-projection-data: existing subject is "Normalized coefficient projection interfaces"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-sf-evaluation-hom-site-comparison: existing subject is "Evaluation-induced derived Hom comparison for the etale-proetale morphism"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-sf-open-normalization-data: existing subject is "Geometric and operation data for open tensor normalization"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-sf-semilinear-proper-open-comparisons: existing subject is "Canonical semilinear proper/open compositors and intrinsic clopen comparison"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-sfb-condensed-pullback-tensor-comparison: existing subject is "Normalized condensed-module pullback tensor comparison"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-sfb-module-object-projection-map: existing subject is "Canonical derived projection map for condensed module objects"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-sfb-proetale-projection-exchange-maps: existing subject is "Canonical projection and exchange maps on internal pro-etale modules"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-sfb-proetale-trace-coefficient-interfaces: existing subject is "Canonical internal-module trace coefficient interfaces"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-sfb-ringed-derived-comparison-data: existing subject is "Data of normalized derived monoidal comparisons of ringed topoi"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-sfb-ringed-projection-coherence-data: existing subject is "Recorded data for tensor projection coherence"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-sfb-ringed-slice-comparison-model: existing subject is "Normalized ringed slice comparison data"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-sfb-scalar-hom-comparison-data: existing subject is "Actual scalar-adjunction and normalized tensor-Hom comparison data"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-sp-constant-scalar-pullback-comparison: existing subject is "Canonical constant-coefficient scalar extension, direct image and pullback comparison"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-trf-integral-comparison-realization-models: existing subject is "Normalized realization interfaces for integral quotient systems"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-trf-integral-comparison-sequence-systems: existing subject is "Canonical pullback and scalar change of whole quotient systems"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-weil-pbc-canonical-ringed-tensor-comparison: existing subject is "Normalized ordinary tensor comparison data"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-weil-pbc-derived-direct-image-composition: existing subject is "Composition isomorphisms of derived direct images (conjugates of those of inverse images)"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-weil-pbc-derived-square-iso: existing subject is "Square isomorphism on bounded below derived categories"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-weil-pbc-ringed-tensor-square-presentation: existing subject is "Representative presentation of a commutative ringed tensor square"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-weil-pbc-strict-tower-operations: existing subject is "Specified derived operations and mate on strict pro-etale module towers"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs def-zl-pbc-finite-raw-scalar-comparison: existing subject is "Canonical comparison of normalized and embedding finite-field scalar extension"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-cbc-strict-tower-direct-image-coherence: existing subject is "Coherence of canonical strict-tower direct image and its square mates"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-coef-signed-single-dual-restriction: existing subject is "Normalized slice comparison for a single coefficient dual"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-exc-proetale-constant-support-projection: existing subject is "Constant-coefficient projection for compact support"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-fix-tensor-pullback-square: existing subject is "Tensor inverse-image comparisons commute around an open square"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-kun-derived-pullback-composition-monoidal: existing subject is "Canonical derived etale inverse-image composition is monoidal"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pd-module-ringed-topos-derived-comparison: existing subject is "Module-object and ringed-topos derived tensor comparison"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-per-galois-descent-monodromy-tensor: existing subject is "Monodromy and tensor of modules descended along a finite Galois cover"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-per-local-system-tensor-monodromy: existing subject is "Tensor comparison for arbitrary torsion local systems"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pod-constant-comparison-module-localization: existing subject is "Canonical finite-coefficient derived composition is ordinary module composition localized"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pod-etale-stalk-tensor-scalar: existing subject is "Geometric stalks commute with tensor products and scalar extension on the etale site"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pod-finite-system-pullback-coherence: existing subject is "Coherent composition of finite-coefficient pullback on strict systems"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pod-integral-pullback-composition: existing subject is "Composition isomorphism for integral derived pullbacks"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pod-lisse-tensor-and-scalar-extension: existing subject is "Tensor products, scalar extension and stalks of lisse sheaves of modules"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pod-point-extension-kflat: existing subject is "K-flatness of the point extension of a flat-term module complex"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-cochain-comparison-monoidal-equations: existing subject is "Monoidal equations for the canonical cochain pullback comparison"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-cochain-pullback-tensor-coherence: existing subject is "Signed tensor comparison and composition on cochain sheaf pullbacks"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-coefficient-associator-shifts: existing subject is "Shift compatibility of balanced derived scalar associators"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-coefficient-pullback-coherence: existing subject is "Balanced coherence of canonical coefficient pullback comparisons"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-coefficient-pullback-comparison: existing subject is "Canonical inverse-image coefficient comparison"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-coefficient-pullback-shifts: existing subject is "Shift compatibility of normalized inverse-image coefficient comparisons"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-coefficient-scalar-units: existing subject is "Multiplication units for derived scalar extension"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-etale-scalar-pullback-existence: existing subject is "Existence of normalized derived scalar/pullback comparison"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-etale-scalar-pullback-uniqueness: existing subject is "Uniqueness of normalized derived scalar/pullback comparison"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-independent-composite-algebraic-image: existing subject is "Algebraic inverse image and coefficient map for a composite"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-independent-inverse-image-tensor-comparison: existing subject is "Normalized tensor comparison for an algebraic inverse image at independent site sizes"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-independent-normalized-scalar-composition: existing subject is "Normalized composition of module scalar extensions"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-independent-ringed-tensorator-existence: existing subject is "Existence of the tensorator for fixed scalar insertion at independent site sizes"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-integral-operations-well-defined: existing subject is "The towers defining integral pullback and completed tensor product are invariant under change of K-flat resolution"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-inverse-image-scalar-comparison: existing subject is "Inverse image commutes with extension of scalars, with its unit formula"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-inverse-image-tensor-comparison: existing subject is "The unit-normalized tensor comparison for an isomorphic base change"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-isomorphism-inverse-image-tensor-hom: existing subject is "Inverse image along an isomorphism of schemes commutes with tensor products and sheaf Hom"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-kflat-change-of-rings: existing subject is "Change of rings preserves K-flat complexes with flat terms"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-kflat-change-of-rings-independent: existing subject is "Change of rings preserves K-flat complexes with flat terms in independent universes"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-module-tensor-coefficient-equations: existing subject is "Ordinary module tensor equations for coefficient change"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-module-tensor-composition-equation: existing subject is "Ordinary tensor square for composite module pullback"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-module-tensor-extension-equation: existing subject is "Ordinary scalar-extension tensor equation"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-module-tensor-generator-calculus: existing subject is "Pure tensors and normalized insertion naturality for sheaf modules"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-module-tensor-monoidal-equations: existing subject is "Associativity and symmetry of the canonical ordinary module tensor comparison"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-proetale-inverse-image-tensor-comparison: existing subject is "Pure-tensor description and coherence of the pro-etale inverse-image tensor comparison"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-ringed-site-pullback-dual-free-chart: existing subject is "Invertibility of a pulled evaluation comparison on a finite-free chart"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-ringed-site-pullback-pairing-transfer: existing subject is "Extension of module pairings along a ringed site morphism"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-scalar-tensor-pullback-normalization: existing subject is "Scalar/tensor pullback normalization on a K-flat representative"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-scalar-tensor-unit: existing subject is "Scalar action unitor for a normalized signed tensor comparison"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-tate-inverse-limit-base-change: existing subject is "Base change of an ell-adic inverse-limit tower and of its finite reduction tensor"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-varying-ring-tensor-comparison: existing subject is "Normalized tensor comparison for one varying-ring inverse image"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sbc-pullback-comparison-comp: existing subject is "Composition of coefficient pullback and single-complex comparisons"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sf-finite-field-local-tensor-model: existing subject is "Localized inverse-image constant models under field scalar extension"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sf-open-operation-models: existing subject is "Open operation comparisons with fixed tensor models and right square"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sf-open-pullback-support: existing subject is "Derived pullback preserves open support"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sf-reduction-pull-finite-evaluation: existing subject is "Finite evaluation respects the specified reduction/pullback comparison"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sf-scalar-pullback-composition: existing subject is "Composition coherence of normalized scalar/pullback comparisons"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-closed-scalar-hom-composition: existing subject is "Composition of the five closed-Hom bijections"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-closed-scalar-hom-transport: existing subject is "Transport of closed-Hom comparison along adjoint isomorphisms"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-condensed-support-projection-formula: existing subject is "Natural support tensor projection formulas on unbounded condensed modules"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-constant-module-kflat: existing subject is "Constant realization preserves flat-term K-flat complexes"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-constant-realization-derived-scalar-extension: existing subject is "Derived constant realization commutes with derived scalar extension"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-flat-term-kflat-functor: existing subject is "Flat-preserving colimit functors preserve flat-term K-flat complexes"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-localized-site-tensor-restriction: existing subject is "Restriction to a localized site commutes with the sheaf tensor product"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-proetale-intrinsic-tensor-comparison: existing subject is "Right-tensor comparison for intrinsic constant-ring realization"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-ringed-comparison-tensor-adjunction: existing subject is "Tensor and adjunction compatibility of canonical ringed-topos path comparisons"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-ringed-derived-composition-comparison: existing subject is "Composition comparison with normalized representative formulas"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-ringed-derived-identity-comparison: existing subject is "Identity comparison with normalized representative formulas"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-ringed-derived-monoidal-comparisons: existing subject is "Monoidal and adjunction normalization of derived ringed-topos comparisons"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-ringed-derived-tensor-diagrams: existing subject is "Coherence equations for explicit canonical derived comparison maps"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-ringed-derived-tensor-lift: existing subject is "Symmetric monoidal coherence of a canonical derived tensor lift"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-ringed-derived-two-iso-comparison: existing subject is "Specified geometric 2-isomorphism comparison on derived modules"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-ringed-projection-pullback-comparisons: existing subject is "Normalized identity, composition and section pullback comparisons"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-ringed-projection-tensor-compatibility: existing subject is "Tensor constraints and compatibility of normalized comparisons"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-ringed-projection-tensor-structure: existing subject is "Canonical tensor structure in arbitrary recorded presentations"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-ringed-site-point-kflat-resolution: existing subject is "K-flat resolution with K-flat stalk"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-scalar-extension-kflat: existing subject is "Scalar extension preserves all K-flat sheaf complexes"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-scalar-hom-tensor-coherence: existing subject is "Tensor coherence of the normalized scalar extension maps"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-scalar-internal-hom-tower-coherence: existing subject is "Coefficient-tower and identity coherence for normalized internal Hom"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-scalar-ordinary-tensor-comparison: existing subject is "Normalized ordinary scalar tensor comparison in independent site universes"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-scalar-tensor-tower-comparison: existing subject is "Simultaneous normalized scalar tensor comparisons with coefficient coherence"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-site-inverse-image-bilinear-adjunction: existing subject is "Bilinear adjunction for the inverse image of a morphism of sites"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-site-inverse-image-multimap-universal: existing subject is "Universality of inverse-image units for natural maps with finitely many inputs"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sfb-successive-derived-quotient-normalization: existing subject is "Successive derived scalar extensions agree with direct quotient extension"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sp-canonical-derived-pullback-normalization: existing subject is "Canonical derived composition is localized normalized ordinary composition"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sp-constant-scalar-pullback-cube: existing subject is "The canonical constant-ring scalar and geometric pullback cube"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sp-finite-free-balancing-coherence: existing subject is "Scalar units and associators commute with the canonical balanced pullback comparison"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sp-finite-free-direct-image-shift: existing subject is "Shift compatibility of the actual coefficient/direct-image mate"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-sp-scalar-tensor-pullback-square: existing subject is "Scalar tensor comparisons respect arbitrary pullback squares"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-trf-derived-pullback-coherence: existing subject is "Associativity of finite pro-etale derived pullback comparisons"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-trf-integral-pullback-comparison-realization: existing subject is "Strict-system realization and composition coherence of integral pullback comparisons"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-trf-pullback-coefficient-iterate-coherence: existing subject is "Canonical pullback comparisons intertwine coefficient-map iterates"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-etale-native-tensor-pullback: existing subject is "Native unbounded derived tensor commutes with etale inverse image"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-algebraic-inverse-image-pairing-isIso: existing subject is "Universality of the transported inverse-image pairing"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-algebraic-inverse-image-pure-pairing: existing subject is "The canonical bilinear pairing of the specified inverse image"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-algebraic-inverse-image-tensor-comparison: existing subject is "The normalized tensor comparison for the specified algebraic inverse image"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-canonical-ringed-tensor-comparison-construction: existing subject is "Construction of the normalized ordinary tensor comparison"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-completed-adic-koszul-kflat: existing subject is "K-flatness of the actual completed exterior Koszul complexes"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-completed-reduction-pullback-square: existing subject is "Completed reduction respects the strict inverse-image square"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-constant-derived-normalization-universal: existing subject is "Constant derived realization preserves universal coefficient arrows"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-continuous-module-encoding-lattices: existing subject is "Local freeness and lattice compatibility of the explicit continuous encodings"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-continuous-module-encoding-restriction: existing subject is "Continuous module encoding commutes with restriction along an etale morphism"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-continuous-module-encoding-scalar-extension: existing subject is "Scalar extension under the continuous integral and rational module encodings"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-derived-inverse-image-composition: existing subject is "Composition isomorphisms of derived inverse images and their coherence"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-derived-scalar-extension-local-systems: existing subject is "Coherent localized derived scalar extension and comparison"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-derived-square-iso-pasting: existing subject is "Identity and pasting laws of the derived square isomorphism"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-diagram-kflat-replacements: existing subject is "Objectwise K-flat replacements in strict diagram categories"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-finite-reduction-pullback-coherence: existing subject is "Finite reduction and the canonical pullback square"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-finite-reduction-pullback-square: existing subject is "Finite reduction respects the inverse-image square"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-frobenius-exchange-restriction: existing subject is "Finite-level exchange is the restricted ambient exchange"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-kflat-tensor-pullback-computation-universes: existing subject is "Derived pullback computes K-flat tensor representatives"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-left-exact-site-inverse-image-tensor: existing subject is "Inverse image induced by a continuous left-exact site functor and its tensor structure"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-localization-inverse-image-coherence: existing subject is "Coherent localization comparison for exact inverse image"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-normalized-derived-isomorphism-transport: existing subject is "Universal normalization and evaluation of source-site local Isom sheaves"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-proetale-derived-pullback-composition: existing subject is "Composition of derived pro-etale module pullbacks"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-ring-sheaf-change-adjunction: existing subject is "Derived adjunctions under compatible changes of ring sheaves"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-ringed-pullback-preserves-kflat: existing subject is "Ringed pullback kflat"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-ringed-slice-normalized-comparisons: existing subject is "Existence of normalized slice tensor, Hom and Koszul comparisons"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-ringed-square-localization: existing subject is "Ambient ringed square is exact localization of its ordinary square"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-ringed-square-tensor-compatibility: existing subject is "Tensor compatibility of a ringed square on flat K-flat representatives"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: existing subject is "Derived tensor comparison for arbitrary ringed topoi"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-existence: existing subject is "Canonical tensor comparison unit existence"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-uniqueness: existing subject is "Canonical tensor comparison unit uniqueness"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-ringed-topoi-module-pullback-tensor: existing subject is "Underived tensor comparison for pullback of modules on ringed topoi"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-ringed-topoi-module-pullback-tensor-tail: existing subject is "Tensor comparison tail for scalar-extended inverse-image modules"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-ringed-topos-acyclic-kflat-pullback: existing subject is "Ringed-topos pullback in the acyclic K-flat case"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-ringed-topos-kflat-pullback: existing subject is "Ringed-topos pullback preserves flat-term K-flat complexes"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-ringed-topos-pullback-adapted-flat-resolution: existing subject is "A flat resolution whose ringed-topos pullback is K-flat"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-scalar-extension-tensor-comparison: existing subject is "Scalar extension preserves the normalized sheaf tensor"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-kflat-scalar-comparison-normalization vs lem-weil-pbc-supplied-ringed-topos-kflat-pullback: existing subject is "Tensor pullback adjoint to a supplied ringed-topos module direct image"; this extraction specifies equality of the specified scalar mate and the balanced K-flat representative, with geometric composition, for arbitrary ring sheaves.

lem-sfb-normalized-immersion-comparison-coherence vs det-formal-closed-support-ii-limits: existing subject is "Closed support commutes with derived limits of sequences"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs det-lem-formal-closed-support-sheaves: existing subject is "Sections with support: the sheaf-level adjunction"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs det-lem-int-ext-bound: existing subject is "Uniform vanishing of Ext between integral constructible sheaves"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs det-prop-closed-adjoint-constructible-support: existing subject is "Sections with support of a constructible complex are constructible"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs det-sfb-dc-restricted-functors-closed-image: existing subject is "Extension by zero and closed direct image preserve integral constructible complexes"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-cbc-extension-zero-perfect-model-transport: existing subject is "Transport a single local completed constant model across open extension by zero"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-cbc-extension-zero-stratified-perfect: existing subject is "Extension by zero preserves stratified perfect local models"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-exc-etale-origin-open-restriction-transport: existing subject is "Canonical comparison preserves normalized derived open restriction"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-exc-proetale-cartesian-open-injective-acyclic: existing subject is "Proper acyclicity of injectives extended from an arbitrary Cartesian open"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-exc-proetale-derived-open-restriction: existing subject is "Unbounded pro-etale direct image commutes with open restriction"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-exc-proetale-proper-open-sheaf-comparison: existing subject is "Proper/open comparison for pro-etale module sheaves"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-formal-closed-pullback-derived-products: existing subject is "Closed coefficient-compatible pullback preserves derived products"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-pur-proetale-open-unit-evaluation: existing subject is "Canonical open pro-etale pullback evaluation and its unit"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-sf-ring-sheaf-closed-localization: existing subject is "Closed localization for arbitrary pro-etale ring-sheaf module objects"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-sf-ringed-closed-kernel-adjoint: existing subject is "The support-kernel adjoint for an arbitrary pro-etale ring sheaf"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-sfb-condensed-support-derived-localization: existing subject is "Open/closed localization for ordinary derived condensed module objects"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-sfb-condensed-support-projection-formula: existing subject is "Natural support tensor projection formulas on unbounded condensed modules"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-sfb-local-integral-perfect-model-cohomology: existing subject is "Cohomology of a local integral perfect scalar model"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-sfb-locally-closed-extension-coherence: existing subject is "Restriction and composition for locally closed extension by zero"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-sfb-locally-closed-module-extension-coherence: existing subject is "Normalized locally closed extension on module sheaves"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-sfb-proetale-identified-open-closed: existing subject is "Exact open and closed extensions with identified inverse-image coefficients"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-sfb-proetale-identified-supported-reconstruction: existing subject is "Normalized supported reconstruction for actual tensor pullbacks"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-sfb-proetale-locally-closed-extension: existing subject is "Pointwise exact locally closed extension"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-weil-pbc-condensed-open-closed-recollement: existing subject is "Open/closed recollement for condensed coefficient modules"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-weil-pbc-proetale-abelian-closed-counit: existing subject is "The closed counit on abelian pro-etale sheaves"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-weil-pbc-proetale-abelian-closed-support: existing subject is "Closed support for abelian pro-etale sheaves"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-weil-pbc-proetale-immersion-limit-preservation: existing subject is "Inverse images along immersions preserve pro-etale limits"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-weil-pbc-proetale-inverse-image-limits-zariski-local: existing subject is "Zariski locality of preservation of pro-etale inverse-image limits"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-weil-pbc-proetale-restriction-preserves-limits: existing subject is "Limits preserved by weakly etale pro-etale restriction"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-weil-pbc-proetale-ringed-closed-counit: existing subject is "Closed ringed counit is invertible"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-weil-pbc-proetale-ringed-open-closed: existing subject is "Ringed pro-etale open-closed localization"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs lem-weil-pbc-proetale-ringed-open-comparison: existing subject is "Arbitrary-coefficient open localization"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs new-lem-weil-pbc-condensed-finite-model-immersion-restriction: existing subject is "finite model on immersion range"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs new-lem-weil-pbc-condensed-surjective-closed-equivalence: existing subject is "condensedSurjectiveClosedPullback isEquivalence"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs new-lem-weil-pbc-condensed-surjective-closed-local-presentation: existing subject is "lfp lowerStar of surjective closed"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs sk-lem-formal-closed-support-ii: existing subject is "Closed support, truncation and derived limits"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs sk-lem-int-ext: existing subject is "Continuity and boundedness of Ext"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-normalized-immersion-comparison-coherence vs sk-lem-int-tensor: existing subject is "Inverse image and tensor product"; this extraction specifies conditional factorization, composition and tower coherence for already supplied normalized open/closed comparison maps.

lem-sfb-open-scalar-conjugate-normalization vs def-per-site-comparison-pullback-data: existing subject is "Canonical etale and pro-etale comparison pullback data"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs def-weil-boundary-exceptional-comparison-data: existing subject is "Specified etale to pro-etale exceptional Hom transport and counit compatibility"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs def-weil-pbc-etale-set-constant-pullback-comparison: existing subject is "Constant comparison for constructed etale inverse image"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-cbc-derived-extension-zero-base-change-vertical-pasting: existing subject is "Underived vertical pasting for open base change"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-fix-site-open-exchange-square: existing subject is "Specialized inverse-image comparison square for open exchange"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-pur-bounded-site-adjunction-transpose: existing subject is "Compactification comparison normalizes bounded etale-origin transposes"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-pur-mate-unit-compatibility: existing subject is "Units and the right mate of a functor square"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-pur-vector-integration-site-comparison: existing subject is "Finite-level site comparison of normalized vector-bundle integration"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-stage3-inverse-mate-equivalences: existing subject is "Inverse mates of invertible squares along equivalences are invertible"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-trf-adjoint-composition-coherence: existing subject is "Coherence of adjunction composition comparisons with isomorphic right composites"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-trf-iterated-square-mates: existing subject is "Iterating square mates equals conjugation for composite adjunctions"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-affine-etale-restriction-composition: existing subject is "Composition coherence of unit-preserving affine etale restriction comparisons"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-affine-etale-restriction-composition-gamma: existing subject is "Affine base-change composition lifts through full affine inclusion"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-affine-etale-restriction-composition-mates: existing subject is "Unit-preserving affine composition mates and restriction coherence"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-affine-etale-restriction-unit: existing subject is "Affine etale restriction comparison preserving the adjunction unit"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-comparison-direct-image-canonical-mate: existing subject is "Canonical derived direct-image comparison is the invertible counit mate"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-conjugate-iso-unit-equation: existing subject is "An isomorphism of right adjoints determines a unique isomorphism of left adjoints compatible with the units"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-constant-module-transition-coefficients: existing subject is "Forgetting scalars commutes with the constant-sheaf adjoint transition"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-constant-pullback-composition-coherence: existing subject is "ConstantPullbackCompositionCoherence"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-constant-pullback-identity-coherence: existing subject is "ConstantPullbackIdentityCoherence"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-etale-coefficient-product-composition-component: existing subject is "Composition calculation at one outgoing-arrow factor"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-etale-coefficient-product-embedding-compatibility: existing subject is "Compatibility of explicit product embeddings with the coefficient transitions"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-etale-coefficient-product-identity-component: existing subject is "Identity calculation at one outgoing-arrow factor"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-etale-coefficient-product-transition-laws: existing subject is "Identity and composition laws for explicitly constructed outgoing-arrow product transitions"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-etale-set-constant-pullback-composition: existing subject is "Composition of constant pullback comparisons"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-etale-set-constant-pullback-unit-generators: existing subject is "Unit transport on constant generators"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-etale-set-constant-transport-generators: existing subject is "Compositional transport on constant generators"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-etale-set-constant-transport-identity: existing subject is "Identity transport of arbitrary constant-sheaf maps"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-formal-system-exchange-mate-compatibility: existing subject is "Transport of an objectwise mate identity to diagrams"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-inverse-image-composition: existing subject is "Inverse images along a composite: the canonical isomorphism compatible with the units"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-open-scalar-conjugate-normalization vs lem-weil-pbc-ordinary-flat-exchange-prescribed-adjunction: existing subject is "Ordinary flat exchange for a prescribed vertical adjunction"; this extraction specifies the explicit restriction equation for the already published derived open scalar conjugate.

lem-sfb-scalar-inverse-image-tower-diagram vs adic-unit-exists-data: existing subject is "Existence of the identity scalar-extension unit map"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-coef-semilinear-geometry-base: existing subject is "Geometry base fields for coefficient linear operations"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-coef-semilinear-geometry-derived: existing subject is "Derived geometric system operations and normalization"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-coef-semilinear-geometry-ops: existing subject is "Canonical geometric mate and projection words"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-kun-prime-coefficient-complexes: existing subject is "Degree zero complexes and localization"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-kun-prime-coefficient-complexes-input-output: existing subject is "Ordinary source and target tensor complexes"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-kun-prime-coefficient-constructions: existing subject is "Canonical quotient coefficient tensor arrow"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-kun-prime-coefficient-functors: existing subject is "Punctual tensor source and target functors"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-kun-prime-coefficient-iso: existing subject is "Derived coefficient tensor isomorphism type"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-kun-prime-coefficient-localization-compatibility: existing subject is "Localized termwise coefficient compatibility"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-kun-prime-coefficient-normalization: existing subject is "Derived normalization by the quotient tensor map"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-kun-prime-coefficient-pullbacks: existing subject is "Canonical coefficient pullback maps"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-kun-prime-coefficient-term-map: existing subject is "Degree zero coefficient term map"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-kun-prime-coefficient-termwise-normalization: existing subject is "Termwise normalization of the quotient tensor arrow"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-pd-proetale-section-module-functors: existing subject is "Normalized tensor structures on existing pro-etale section-module functors"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-pd-section-module-operations-data: existing subject is "Existing section-module operations and pure-tensor data"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-pur-cochain-coefficient-arrows: existing subject is "Canonical scalar-association and transition arrows on cochain sheaves"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-pur-cochain-coefficient-universe-transport: existing subject is "Canonical common-universe transport of ring and module sheaves"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-pur-cochain-tensor-coherence-data: existing subject is "Canonical cochain ringed-pullback and coherence data"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-pur-finite-tate-site-comparison: existing subject is "Finite Tate tensor generators and root-normalized site comparison predicates"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-pur-inverse-image-tensor-hom-sections: existing subject is "Tensor, scalar and unit-section conventions for module inverse image"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-pur-kummer-module-coefficients: existing subject is "Kummer sheaves with module coefficients and their scalar actions"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-pur-operation-scalar-transport: existing subject is "Pure-tensor and derived-counit normalized operation scalar transport"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-pur-presheaf-tensor-product: existing subject is "Presheaf tensor product of modules"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-pur-sheaf-tensor-product: existing subject is "Tensor product of sheaves of modules on a site"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-pur-twist-coefficient-rings: existing subject is "The canonical discrete and completed scalar square of the Tate twist"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-sf-evaluation-hom-site-comparison: existing subject is "Evaluation-induced derived Hom comparison for the etale-proetale morphism"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-sf-open-normalization-data: existing subject is "Geometric and operation data for open tensor normalization"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-sfb-condensed-pullback-tensor-comparison: existing subject is "Normalized condensed-module pullback tensor comparison"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-sfb-internal-section-total-comparison: existing subject is "Canonical internal-to-sectionwise total-complex comparison"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-sfb-module-object-projection-map: existing subject is "Canonical derived projection map for condensed module objects"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-sfb-proetale-trace-coefficient-interfaces: existing subject is "Canonical internal-module trace coefficient interfaces"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-sfb-ringed-slice-comparison-model: existing subject is "Normalized ringed slice comparison data"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-sp-constant-scalar-pullback-comparison: existing subject is "Canonical constant-coefficient scalar extension, direct image and pullback comparison"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-sp-scalar-tensor-comparison-data: existing subject is "Normalized tensor and scalar-extension comparison data"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-sp-semilinear-constant-ring-operations: existing subject is "Constant-ring semilinear system operations and normalized evaluation mates"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-trf-singleton-site-operations: existing subject is "Punctual ringed-site operations and normalized comparison predicates"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-weil-pbc-canonical-ringed-tensor-comparison: existing subject is "Normalized ordinary tensor comparison data"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-weil-pbc-ringed-tensor-section-calculus: existing subject is "Section calculus for the actual sheaf tensor and scalar extension"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-weil-pbc-ringed-tensor-square-presentation: existing subject is "Representative presentation of a commutative ringed tensor square"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs def-zl-pbc-finite-raw-scalar-comparison: existing subject is "Canonical comparison of normalized and embedding finite-field scalar extension"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-coef-signed-single-dual-restriction: existing subject is "Normalized slice comparison for a single coefficient dual"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-kun-derived-pullback-composition-monoidal: existing subject is "Canonical derived etale inverse-image composition is monoidal"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pc-sheaf-modules-tensor-closed: existing subject is "Sheaves of modules on a site form a symmetric monoidal closed category"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pc-sites-sheaf-tensor-bilinear-universal: existing subject is "Universal property of sheaf tensor product"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pe-internal-section-tensor-comparison: existing subject is "Relative tensor and K-flatness under the internal-to-sectionwise module equivalence"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-per-galois-descent-monodromy-tensor: existing subject is "Monodromy and tensor of modules descended along a finite Galois cover"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-per-local-system-tensor-monodromy: existing subject is "Tensor comparison for arbitrary torsion local systems"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pod-etale-stalk-tensor-scalar: existing subject is "Geometric stalks commute with tensor products and scalar extension on the etale site"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pod-lisse-tensor-and-scalar-extension: existing subject is "Tensor products, scalar extension and stalks of lisse sheaves of modules"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-change-of-rings-tensor-cancellation: existing subject is "Natural cancellation of scalar extension in sheaf tensors"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-change-of-rings-tensor-cancellation-independent: existing subject is "Natural tensor cancellation in independent coefficient universes"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-change-of-rings-tensor-comparison: existing subject is "Natural comparison of restricted scalar extension and sheaf tensor"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-cochain-comparison-monoidal-equations: existing subject is "Monoidal equations for the canonical cochain pullback comparison"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-cochain-pullback-tensor-coherence: existing subject is "Signed tensor comparison and composition on cochain sheaf pullbacks"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-coefficient-scalar-units: existing subject is "Multiplication units for derived scalar extension"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-constant-finite-free-power-iso: existing subject is "Finite-basis coordinates for constant scalar extension"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-constant-finite-free-products: existing subject is "Countable products and finite-free constant scalar extension"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-constant-finite-free-section-basis: existing subject is "Compatible sectionwise bases of constant coefficient extensions"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-etale-constant-module-flat: existing subject is "Flatness under constant-scalar realization"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-etale-constant-module-tensor: existing subject is "Constant-coefficient realization commutes naturally with right tensor"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-independent-inverse-image-tensor-comparison: existing subject is "Normalized tensor comparison for an algebraic inverse image at independent site sizes"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-independent-normalized-scalar-composition: existing subject is "Normalized composition of module scalar extensions"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-independent-ringed-tensorator-existence: existing subject is "Existence of the tensorator for fixed scalar insertion at independent site sizes"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-inverse-image-scalar-comparison: existing subject is "Inverse image commutes with extension of scalars, with its unit formula"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-inverse-image-tensor-comparison: existing subject is "The unit-normalized tensor comparison for an isomorphic base change"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-isomorphism-inverse-image-tensor-hom: existing subject is "Inverse image along an isomorphism of schemes commutes with tensor products and sheaf Hom"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-kummer-finite-biproducts: existing subject is "Integral finite-basis cohomology and Kummer exactness"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-kummer-finite-free-comparison: existing subject is "Normalized finite free Kummer cohomology comparison"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-kummer-integral-root-comparison: existing subject is "Integral basis reduction for the Kummer root sheaf"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-module-tensor-coefficient-equations: existing subject is "Ordinary module tensor equations for coefficient change"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-module-tensor-composition-equation: existing subject is "Ordinary tensor square for composite module pullback"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-module-tensor-extension-equation: existing subject is "Ordinary scalar-extension tensor equation"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-module-tensor-generator-calculus: existing subject is "Pure tensors and normalized insertion naturality for sheaf modules"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-module-tensor-monoidal-equations: existing subject is "Associativity and symmetry of the canonical ordinary module tensor comparison"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-proetale-inverse-image-tensor-comparison: existing subject is "Pure-tensor description and coherence of the pro-etale inverse-image tensor comparison"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-ringed-site-pullback-dual-free-chart: existing subject is "Invertibility of a pulled evaluation comparison on a finite-free chart"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-ringed-site-pullback-pairing-transfer: existing subject is "Extension of module pairings along a ringed site morphism"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-scalar-tensor-unit: existing subject is "Scalar action unitor for a normalized signed tensor comparison"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-system-cochain-tensor-reduction: existing subject is "Cochain scalar-adjoint tensor formula for strict systems"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-system-ordinary-tensor-reduction: existing subject is "Ordinary scalar-adjoint tensor formula for strict systems"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-tate-inverse-limit-base-change: existing subject is "Base change of an ell-adic inverse-limit tower and of its finite reduction tensor"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-tensor-pushout-action: existing subject is "A sectionwise scalar pushout acts uniquely on a balanced tensor sheaf"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-twist-coefficient-comparison: existing subject is "The canonical coefficient pushout comparison is invertible"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-twist-coefficient-tensor: existing subject is "Finite integral coefficient extension commutes with sheafwise completion"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-twist-integral-local-models: existing subject is "Scalar-extension local models of the integral root line"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pur-varying-ring-tensor-comparison: existing subject is "Normalized tensor comparison for one varying-ring inverse image"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sc-hom-tensor-comparison-natural: existing subject is "Naturality of the sheaf tensor comparison isomorphism"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sc-hom-tensor-reverse-pair: existing subject is "Reverse currying for one pair of module sheaves"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sc-hom-tensor-section-natural: existing subject is "Naturality of the canonical presheaf-to-sheaf tensor map"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sc-hom-tensor-summand-localized-ext: existing subject is "Localized pure-tensor extensionality for a sheaf tensor"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sc-hom-tensor-summand-restriction-ext: existing subject is "Internal Hom maps determined by total tensor summand restrictions"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sc-internal-hom-coproduct-fan: existing subject is "Internal Hom of a coproduct is a product"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sc-internal-hom-product-fan: existing subject is "Internal Hom preserves integer-indexed product fans"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sf-completed-tensor-finite-shift: existing subject is "Signed right shifts of the strict finite tensor tower"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sf-finite-field-local-tensor-model: existing subject is "Localized inverse-image constant models under field scalar extension"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sf-open-operation-models: existing subject is "Open operation comparisons with fixed tensor models and right square"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sf-reduction-pull-finite-evaluation: existing subject is "Finite evaluation respects the specified reduction/pullback comparison"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sfb-condensed-support-projection-formula: existing subject is "Natural support tensor projection formulas on unbounded condensed modules"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sfb-localized-site-tensor-restriction: existing subject is "Restriction to a localized site commutes with the sheaf tensor product"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sfb-proetale-intrinsic-tensor-comparison: existing subject is "Right-tensor comparison for intrinsic constant-ring realization"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sfb-ringed-derived-tensor-diagrams: existing subject is "Coherence equations for explicit canonical derived comparison maps"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sfb-ringed-derived-tensor-lift: existing subject is "Symmetric monoidal coherence of a canonical derived tensor lift"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sfb-ringed-derived-two-iso-comparison: existing subject is "Specified geometric 2-isomorphism comparison on derived modules"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sfb-scalar-ordinary-tensor-comparison: existing subject is "Normalized ordinary scalar tensor comparison in independent site universes"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sfb-site-inverse-image-bilinear-adjunction: existing subject is "Bilinear adjunction for the inverse image of a morphism of sites"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sfb-site-inverse-image-multimap-universal: existing subject is "Universality of inverse-image units for natural maps with finitely many inputs"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sp-finite-free-scalar-models: existing subject is "Existence of normalized actual-restriction scalar models"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sp-scalar-extension-binary-coherence: existing subject is "Normalized binary scalar-extension comparisons"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sp-scalar-extension-dual-evaluation: existing subject is "Explicit scalar-extension evaluation on internal duals"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sp-scalar-extension-dual-local-iso: existing subject is "Local rank-one scalar extension and dual invertibility"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sp-scalar-extension-dual-tower-core: existing subject is "Dual comparisons and binary scalar-extension tower squares"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-w2-inverse-image-change-of-rings-unit-smul: existing subject is "Scalar compatibility of the inverse-image change-of-rings unit"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-etale-native-tensor-pullback: existing subject is "Native unbounded derived tensor commutes with etale inverse image"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-algebraic-inverse-image-pairing-isIso: existing subject is "Universality of the transported inverse-image pairing"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-algebraic-inverse-image-pure-pairing: existing subject is "The canonical bilinear pairing of the specified inverse image"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-algebraic-inverse-image-tensor-comparison: existing subject is "The normalized tensor comparison for the specified algebraic inverse image"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-canonical-ringed-tensor-comparison-construction: existing subject is "Construction of the normalized ordinary tensor comparison"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-continuous-module-encoding-lattices: existing subject is "Local freeness and lattice compatibility of the explicit continuous encodings"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-continuous-module-encoding-restriction: existing subject is "Continuous module encoding commutes with restriction along an etale morphism"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-continuous-module-encoding-scalar-extension: existing subject is "Scalar extension under the continuous integral and rational module encodings"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-extension-tensor-comparison: existing subject is "Restricted scalar extension as a sheaf tensor product"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-left-exact-site-inverse-image-tensor: existing subject is "Inverse image induced by a continuous left-exact site functor and its tensor structure"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-localization-inverse-image-coherence: existing subject is "Coherent localization comparison for exact inverse image"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-ringed-slice-normalized-comparisons: existing subject is "Existence of normalized slice tensor, Hom and Koszul comparisons"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-ringed-topoi-module-pullback-tensor: existing subject is "Underived tensor comparison for pullback of modules on ringed topoi"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-ringed-topoi-module-pullback-tensor-tail: existing subject is "Tensor comparison tail for scalar-extended inverse-image modules"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-scalar-extension-tensor-comparison: existing subject is "Scalar extension preserves the normalized sheaf tensor"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-scalar-localization-complex-colimit: existing subject is "Ordinary scalar-sequence colimit of complexes"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-scalar-localization-module-colimit: existing subject is "Scalar localization as an ordinary module-sheaf colimit"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-scalar-tensor-comparison-universes: existing subject is "Scalar-extension tensor associativity on underlying abelian sheaves in independent universes"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-pbc-tensor-local-bijection-universes: existing subject is "Tensoring a local module bijection commutes with sheafification in independent universes"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-point-sections-tensor-shift: existing subject is "Sections-tensor comparison commutes with shifts"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-weil-sheaf-scalar-extension-ring-iso: existing subject is "Scalar extension along an isomorphism of ring sheaves"; this extraction specifies the ordinary balanced scalar-tower/inverse-image equality with final coefficient action retained.

lem-sfb-internal-section-scalar-adjunction vs lem-sfb-internal-module-operations-transport: the existing theorem compares geometric pullback/pushforward/open extension for one coefficient ring; the new node compares extension and restriction along a change of ring.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pur-proetale-inverse-image-tensor-comparison: the existing statement is ordinary inverse-image tensor functoriality; the new one fixes the derived scalar mate and its K-flat representative.

lem-sfb-exact-open-closed-unbounded-calculus vs lem-sfb-condensed-support-derived-localization: the existing result fixes internal modules for a condensed ring on pro-etale schemes; the new abstract result takes any exact abelian localization datum and states its specified localized adjunctions.

lem-sfb-normalized-immersion-comparison-coherence vs lem-sfb-locally-closed-extension-coherence: the existing result gives extension and gamma with their Hom bijections; the new conditional result concerns comparison functors F and maps d that are absent from the existing statement.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-sfb-successive-derived-quotient-normalization: the existing result constructs scalar reassociation but has no geometric inverse image; the new statement is its ordinary compatibility diagram with inverse image.

lem-sfb-internal-section-scalar-adjunction vs lem-pd-ringed-direct-image-pairing-lax: the newly landed existing node supplies an ordinary direct-image lax tensor pairing; the extraction compares internal and sectionwise change-of-ring adjunctions and their derived normalizations.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pd-ringed-tensor-adjunction-mate: the newly landed existing node normalizes an ordinary oplax tensorator for a module pullback; the extraction identifies a derived scalar-change mate across exact inverse image with its flat-term K-flat coequalizer model, and gives geometric composition.

lem-sfb-scalar-inverse-image-tower-diagram vs lem-pd-ringed-direct-image-pairing-lax: the newly landed existing node gives a direct-image lax pairing with two tensor arguments; the extraction gives the three-ring scalar-reassociation square for inverse image, with different functors and endpoints.

The first push attempt stopped before pushing because these two nodes landed after the successful dry run. I opened both complete statements and added the three distinct-subject comparisons above. No mathematical change or duplicate extraction was needed.

lem-sfb-kflat-scalar-comparison-normalization vs lem-pd-section-ordinary-oplax-normalization: the existing statement identifies the ordinary module-pullback oplax tensor arrow for two modules over a single pulled-back condensed coefficient ring, including its associators and unitors; the extraction identifies the scalar-change adjunction mate across an exact inverse image for an arbitrary ring-sheaf map with the inverse of its flat-term K-flat balanced representative, and proves geometric composition. The existing statement has no derived scalar-change functor, K-flat representative, or scalar-adjunction mate normalization, so it does not imply the extraction in one line.

The next push stopped because this additional Tag 03EL node landed after the dry run. Its complete statement was opened and compared as above; the seven extracted statements and the item proof are unchanged.
