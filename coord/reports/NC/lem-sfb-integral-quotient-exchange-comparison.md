## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-quotient-exchange-comparison.json`: unchanged statement and four-step assembly (2316 proof-text characters).
- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-quotient-pullback-face-model.json`: new statement, status unsplit; no Mathlib match. Coefficient projections and simultaneous six-face K-flat normalization, without a pushforward exchange assertion.
- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-quotient-section-mate-realization.json`: new statement, status unsplit; no Mathlib match. Simultaneous internal/section geometric and scalar adjunction normalization, including the specified balancing comparison and direct-image mate, without the exchange/reduction equation.
- `citations.json`: nine literal quotations, one for every assembly step/node citation. `searches.jsonl` retains every actual search run here. `retained-proof.json` and this report retain the entire returned argument. Sandbox-local JSON/report writers are not delivery files.

Two new nodes, zero Mathlib leaves. Both new nodes have empty proof and proof_deps, null proof_origin, explicit sources and complete hypotheses, and are independent of each other and of the item's conclusion. Their statements have comparable sizes (about 3100 and 3250 characters); neither restates the item's exchange equality.

## Attachments

None. The exact blueprint tag and integral/quotient exchange searches under `lean/WeilConjectures/` returned no declaration. I read `lean/Sheaf/Paper/IntegralQuotientExchangeComparison.lean`, including its actual scalar realization definitions and theorem at line 267. Its theorem ends in `sorry`; it is not a finished attachment. The existing finite rectangle and pullback-square nodes remain reusable material rather than attachment claims.

## WANTED

None. The blueprint and Stacks sources used are present.

## Corrections and scope

This is the repair of the human's 2026-10-21 re-split decision, applied on 2026-10-22. The sandbox initially held only brief markers, not a node/report/search log. I copied the current repository's returned seven-step split, read its full statement and the preceding Q28 report, and retained every old item field outside the stage-1-owned proof/report fields. The item statement is byte-for-byte unchanged. Its original creation metadata, Lean record, blueprint origin and previous Mathlib searches are preserved. The current-repository comparison is the available returned head; no git command was run in the read-only repository.

The return's numbered work requirement is fulfilled by extracting two independent arguments for parallel future workers, not merely abbreviating the proof. Returned Steps 2-3 become the pullback face-model statement. Returned Step 1 and the realization identifications in Step 6 become the section mate-realization statement; the defining adjunct calculation in Step 4 is stated there as well. The parent retains the short generator equality, mate-cube application and inverse cancellations from Steps 4-5, the finite-rectangle assembly from Step 6, and the natural-isomorphism conclusion of Step 7. The complete old proof is reproduced below, so the future workers have its actual arguments, not a summary. Both new nodes are statement-only as requested.

No mathematical statement dispute was found. No properness, derived completeness, étale-origin witness, finite-type assumption or coefficient-flatness assumption is added. In particular no theorem about completed pullbacks is silently used for the ordinary unbounded derived category. No scalar-restriction functor is assumed faithful on derived morphisms. No SGA source is used. No Lean, compiler, Lake, build, repository or launcher modification was made.

## Unfinished work

No stage-1 work is intentionally left on the parent. The two new statements are deliberately unsplit, as required by the return, and join the queue for different workers. No proof or proof sketch is inserted in either new node's statement; the retained arguments appear in the report below.

## Review by NC

I read the chapter record `sec-six-functors-basics`, unit `sk-thm-sfb-proper-base-change`, and the current main-20261015 integral detail proof in full. Paragraph (3)'s claim that reduction of each canonical map is the corresponding torsion map is the precise source sentence realized. The repair stays below this unit and keeps its route. Stacks `sites-cohomology.tex` Lemma 0D6D (`lemma-derived-pullback-composition`, lines 3658 ff.) computes both composite pullbacks on one K-flat complex with flat terms. Lemma 07A4 (`lemma-pullback-tensor-product`, lines 3684 ff.) gives the tensor/pullback representative formula. Those are the sources of the first new node; its simultaneous face normalization and integral projection compatibility are the extracted argument, not a claim that Stacks states this specialized result verbatim. I also read the full statements of the profinite inverse-image and integral-limit nodes: they give the actual finite projections, not a general preservation-of-limits assertion.

For the second new node I read Stacks Lemma 07A6 (`lemma-adjoint`, lines 3989 ff.), Remark 07A7 (`remark-base-change`, lines 4033 ff.), and `derived.tex` Lemmas 09T5 (`lemma-derived-adjoint-functors`, lines 9596 ff.) and 08BJ (`lemma-adjoint-preserve-K-injectives`, lines 9857 ff.). I checked the actual section-operation data and all three reused comparison statements: `lem-pd-section-derived-pushpull-normalization` includes independently derived adjunctions, units, counits and geometric compositors for arbitrary schemes; `lem-sfb-internal-section-scalar-adjunction` includes the actual scalar map, balanced generators and K-flat localization without coefficient flatness; `lem-pe-internal-section-tensor-comparison` preserves flat and K-flat complexes. The second new node combines these normalizations for the specified integral-to-quotient map and identifies its geometric mate, rather than asserting some isomorphisms of unnamed functors. The full proof instructions for this combination are the retained Steps 1, 4 and 6 below. Its section projection is explicitly defined by the counit adjunct, so the statement does not appeal to a properness-restricted definition for its meaning.

Assembly Step 1 cites the new face-model lemma for its simultaneous representative and all six actual faces, and the new section-realization lemma for chi=lambda and the geometric compositors. The statement of the first lemma expressly supplies coefficient-projection compatibility and the actual ordinary face formulas; the statement of the second supplies the normalized derived identifications. Thus the only calculation left in the step is equality on balanced generators and localization. Testing flatness is done on the current coefficient ring after each operation: extension preserves K-flatness because (P tensor_R S) tensor_S N = P tensor_R Res(N), with restriction exact; it never requires S flat over R. The ordinary representative square has source p^S_f' p^S_g t_Y(P) and target t_X' p^R_h p^R_f(P). Hence its derived equation has exactly the displayed direction and object types.

Assembly Step 2 uses the direct-image comparison's defining adjunct, the mate definition's transpose formula, and the ambient exchange definition's actual geometric-square mate. Each was read in full. The existing exchange-mate cube's statement gives the right-adjoint cube from equality of the inverse-image cube with four invertible comparison squares. I checked its Lean orientation against lambda inverses, with connecting functors D_Y, D_X, D_Y', D_X'. It does not require either exchange to be invertible. The intermediate equation has source D_Y' L_g,R F_f,R(K) and target F_f',S L_h,S D_X(K); precomposing lambda_g and postcomposing F_f',S(lambda_h) yields exactly the parent's source and target. Cancellation is only of lambda inverse pairs.

Assembly Step 3 uses the second new lemma's explicit identifications of lambda, rho and both exchanges, and the intrinsic finite rectangle's statement for the independently prescribed order of its arrows. I opened that statement: its projection maps are the specified adjuncts, its exchange is the ambient mate, and it imposes no properness or finiteness assumption on K. I read the explicit formulas in `def-weil-pbc-four-arrows` and `sectionProjection` in the existing Lean file as a check, but did not use the properness-dependent hypotheses or invertibility applications in that definition as an unrestricted theorem. This repair instead defines chi and pr in the new lemma on arbitrary edges using the same balanced and counit formulas. Consequently Step 3 compares exactly the normalized rectangle, including its last inverse chi_h, and does not merely identify corners.

Assembly Step 4 cites the direct-image comparison statement's natural isomorphism assertion. Lambda is already specified as a natural isomorphism there. All equations are of natural transformations, so naturality does not require a functorial choice of K-flat replacements. Each citation has a verbatim quotation in citations.json; I checked that its statement, not its proof, gives the fact used.

Small cases checked for both new statements and the assembly: n=1 is the first positive quotient, with no n-1 denominator or index; K=0 and an empty scheme give the unique zero maps at every vertex; identity scheme edges use the actual unit compositors and the scalar adjunct; arbitrary unbounded complexes are handled by the flat-term K-flat models, with ordinary direct-sum total tensor, not bounded resolutions. A nonflat quotient such as Z_l to Z/l is allowed: the tensor test restricts an acyclic S-complex, and never asserts that arbitrary R-acyclic complexes remain acyclic after ordinary scalar extension. Neither new lemma asserts the exchange itself invertible. Both realization and face statements remain valid without properness or completeness.

I checked delivery-errors B-E against the open node statements and sources: self-contained new objects and definition dependencies; no proofs in the new nodes; actual recorded searches with second phrasings and no unavailable service called a negative; blueprint origins and via chains; exact C4 statement citations; no appeal to proofs of cited nodes; no new helper that restates the exchange equation; no circular dependency. The parent has four proof steps, all below 2000 characters, with total 2316 below the requested 3000. Each substantive old argument is allocated above and retained below. Generic off-unit mate-cube and intrinsic-rectangle uses are declared in split_report, with existing top-level tool_uses preserved rather than edited.

## Mathlib and blueprint searches

The new nodes each have real LeanFinder, LeanSearch, Loogle and grep records, including two different natural-language phrasings. All results were read. For the face-model node, the first semantic phrasing returned ordinary commutative-algebra/cotangent facts; the second returned `SheafOfModules.pullbackComp`, `sheafificationCompPullback` and exact-derived functor comparison infrastructure. I read `PullbackContinuous.lean` around lines 60, 79, 167 and 177. Those declarations are ordinary pullback composition and its adjunction conjugate; they do not give the six derived faces with an inverse-limit integral coefficient and its actual quotient. The K-flat grep returned no hits. For the section-realization node, the semantic queries returned ordinary sheaf pullback adjunctions and unit/free formulas, while Loogle returned `mateEquiv_conjugateEquiv_vcomp` and `conjugateEquiv_mateEquiv_vcomp`. I read `Adjunction/Mates.lean` around lines 486 and 505. They give abstract mates calculus, not the actual internal-to-section realization. No result is an exact match or one-line specialization of either new statement. A candidate-location rg command was inadvertently used once; the same candidate search was rerun through msearch.py and logged, with its actual hits. Every recorded query was actually executed; none was fabricated.

The whole-DAG tag searches covered 0D6D, 07A4, 07A6, 07A7, 09T5, 08BJ, 0E47 and 0E48. Concept searches covered balanced cubes, quotient/section comparisons, coefficient projection squares and integral scalar comparisons. Whole-blueprint searches included `quotient pullback`, `finite reduction`, `scalar`, `exchange`, `section-module`, `pullback cube`, `section scalar`, and `internal.*section`; no blueprint statement supplies either new assertion. The blueprint ancestor command returns det-thm-sfb-proper-base-change-integral. Each new node's via list is [lem-sfb-integral-quotient-exchange-comparison], with its precise paragraph-(3) place and empty same_as. The closest existing statements and all source-tag candidates reported by the duplicate gate are distinguished below.

## Not duplicates

lem-sfb-integral-quotient-pullback-face-model vs lem-pe-constructible-comparison-tensor-test-reflection: that statement reflects vanishing of one etale/proetale tensor-test homology group; this one normalizes the six derived coefficient/geometric faces on a single integral K-flat model.

lem-sfb-integral-quotient-pullback-face-model vs def-sf-point-fibre-tensor-common-stage: that defines common-field-stage point fibre tensor data; this asserts simultaneous K-flat face formulas for arbitrary scheme edges and an integral quotient.

lem-sfb-integral-quotient-pullback-face-model vs lem-weil-pbc-ringed-slice-normalized-comparisons: that constructs tensor, Hom and Koszul comparisons for restriction to a slice; this concerns integral quotient scalar extension and a four-corner geometric square.

lem-sfb-integral-quotient-pullback-face-model vs def-sf-finite-open-tensor-operations: that defines fixed finite-coefficient tensor/open operations; this proves representative normalization across a nonfinite integral coefficient and its quotient.

lem-sfb-integral-quotient-pullback-face-model vs lem-derived-right-exact-tensor-comparison: that constructs a binary derived monoidal tensorator from one functor; this normalizes six scalar/geometric composition faces and the actual integral projections.

lem-sfb-integral-quotient-pullback-face-model vs def-coef-semilinear-derived-calculus: that defines a strict-system derived calculus interface; this is an assertion about the actual one-level integral quotient pullback models.

lem-sfb-integral-quotient-pullback-face-model vs lem-sf-point-integral-completed-tensor-comparisons: that constructs completed point tensor/scalar witnesses for finite field extensions; this uses uncompleted scalar extension modulo pi^n on arbitrary scheme squares.

lem-sfb-integral-quotient-pullback-face-model vs lem-sf-completed-tensor-rational-naturality: that proves categorical rationalization naturality from an assumed completion unit; this proves actual K-flat representative formulas before any completion or rationalization.

lem-sfb-integral-quotient-pullback-face-model vs def-coef-semilinear-geometry-derived: that records normalization conditions for a strict-system geometric interface; this asserts the actual one-level coefficient/projection and six-face normalization.

lem-sfb-integral-quotient-pullback-face-model vs lem-sf-ringed-finite-free-tensor-complex: that proves scalar tensor comparison and K-flat preservation for one ring map; this additionally normalizes the geometric square, its six faces and the finite projections of the integral limit.

lem-sfb-integral-quotient-pullback-face-model vs def-sf-point-fibre-tensor-rational-compatibility: that defines rational point tensor and finite-field-extension compatibility; this proves integral quotient geometric face formulas without rational coefficients.

lem-sfb-integral-quotient-pullback-face-model vs def-sf-point-evaluation-tensor-coherence: that defines signed associativity, symmetry and unit equations for point tensors; this concerns quotient scalar pullback and geometric composition representative maps.

lem-sfb-integral-quotient-section-mate-realization vs lem-sbc-derived-restriction-zero-transport: that treats H^0 restriction/coefficient coherence for abelian etale sheaves, expressly excluding the derived unit; this identifies unbounded internal/section module adjunctions and their scalar/geometric mates.

lem-sfb-integral-quotient-section-mate-realization vs lem-sbc-restricted-derived-section-zero-comparison: that identifies an H^0 derived section pullback with ordinary sections; this retains the entire quotient-module derived category and its specified scalar and exchange mates.

lem-sfb-integral-quotient-section-mate-realization vs lem-sbc-derived-section-pullback-zero: that identifies degree-zero section pullback on a single sheaf; this concerns all unbounded internal modules and coefficient/geometric adjunctions.

lem-sfb-integral-quotient-section-mate-realization vs lem-sbc-derived-section-single-unit: that intertwines two single-object derived section units; this normalizes scalar extension and geometric mates through the internal/section equivalence.

lem-sfb-integral-quotient-section-mate-realization vs lem-sbc-restricted-derived-section-shift-comparison: that identifies a shifted single-object H^0 map with restricted cohomology pullback; this asserts full unbounded module scalar and exchange realization.

lem-sfb-integral-quotient-section-mate-realization vs lem-sbc-restricted-derived-sections-single: that gives the single-complex comparison for restricted derived sections of abelian etale sheaves; this identifies specified internal/section module operations and scalar mates for integral quotients.

lem-sfb-integral-quotient-section-mate-realization vs lem-sbc-restricted-derived-evaluation-pullback: that proves a bounded-below H^p evaluation/pullback equation for etale abelian sheaves; this proves coefficient/geometric adjunction realization for unbounded integral and quotient module objects.

lem-sfb-integral-quotient-section-mate-realization vs lem-sbc-restricted-derived-sections-shift-transport: that transports a derived section transformation through shift/H^p comparisons; this identifies actual internal/section scalar and geometric mates without cohomology truncation.

lem-sfb-integral-quotient-section-mate-realization vs lem-coef-enriched-sequence-projection-formula: that computes the finite projections of a sequence-site enriched Hom adjunction; this concerns one quotient scalar change and geometric pushpull realization, with no strict sequence object or internal Hom claim.

lem-sfb-integral-quotient-section-mate-realization vs lem-coef-scalar-hom-zero-compatibility: that normalizes H^0 derived sections of an internal-Hom scalar comparison; this identifies full derived scalar and geometric adjunctions and their mates.

lem-sfb-integral-quotient-section-mate-realization vs def-coef-compact-support-tensor-comparison: that defines universal coefficient presentations and a compact-support comparison for finite rings; this proves actual ordinary-direct-image mate realization for integral and finite quotient rings.

lem-sfb-integral-quotient-section-mate-realization vs def-sf-ringed-derived-adjoint-lift-data: that records witness data and normalization equations for one ringed morphism; this asserts simultaneous realization under the internal/section equivalences, including the actual quotient projection and ambient exchanges.

lem-sfb-integral-quotient-pullback-face-model vs lem-weil-pbc-finite-reduction-pullback-square: the existing result states the derived square equality in section modules. The new result supplies the simultaneous six-face representative normalization and projection formulas needed to relate the actual internal comparisons to that equality; it does not introduce another square-equality node.

lem-sfb-integral-quotient-pullback-face-model vs lem-sfb-kflat-scalar-comparison-normalization: the existing statement identifies a single balancing comparison with its restriction mate and proves its two-edge composition law; the new statement supplies one simultaneous resolving model and all geometric-square faces for the actual integral-limit coefficient and its finite projections.

lem-sfb-integral-quotient-pullback-face-model vs lem-sfb-etale-proetale-cube-flat-model: the existing cube compares etale and proetale sites with discrete constant coefficient rings; the new cube stays proetale and uses the actual nonconstant inverse-limit integral coefficient and quotient on arbitrary geometric scheme squares.

lem-sfb-integral-quotient-pullback-face-model vs lem-sfb-coefficient-projection-square: the existing statement concerns projection formula maps under exact scalar extension in the standing finite-type setting; the new one is a pullback-face representative theorem and does not assume quotient scalar extension exact.

lem-sfb-integral-quotient-pullback-face-model vs lem-pod-canonical-coefficient-pullback-reduction: the existing statement concerns completed pullback of the coefficient unit along a scheme isomorphism; the new one concerns ordinary unbounded derived pullback of arbitrary complexes along arbitrary edges.

lem-sfb-integral-quotient-pullback-face-model vs lem-fd-whole-tower-integral-pullback-comparison: the existing theorem is a whole completed-tower framework/PBC comparison on allowed schemes and isomorphisms; the new statement is an uncompleted one-level integral/quotient six-face normalization on arbitrary schemes.

lem-sfb-integral-quotient-section-mate-realization vs lem-pd-section-derived-pushpull-normalization: the existing theorem identifies geometric pushpull and their adjunctions for one condensed ring. The new one adds simultaneous scalar-extension realization for the integral quotient and identifies its specified lambda/rho and the exchanges in those same coordinates.

lem-sfb-integral-quotient-section-mate-realization vs lem-sfb-internal-section-scalar-adjunction: the existing theorem identifies scalar extension/restriction adjunctions on one site; the new one includes geometric pullback/direct image, geometric compositors and their specified scalar and ambient-exchange mates.

lem-sfb-integral-quotient-section-mate-realization vs lem-pe-internal-section-tensor-comparison: the existing theorem identifies the relative binary tensor and preserves flat/K-flat complexes; the new one identifies independently specified geometric/scalar adjunctions and their mates across sites.

lem-sfb-integral-quotient-section-mate-realization vs lem-sfb-integral-quotient-direct-image-comparison: the existing theorem gives the internal rho, its isomorphism and projection-formula refinement under scalar restriction. The new one asserts the independently normalized section realization of lambda, rho and both geometric exchanges, before any scalar restriction.

lem-sfb-integral-quotient-section-mate-realization vs lem-weil-pbc-intrinsic-finite-exchange-rectangle: the existing theorem states an equation of section-module exchanges and coefficient projections; the new one identifies the actual internal operations with those section arrows, and asserts no rectangle equality.

lem-sfb-integral-quotient-section-mate-realization vs lem-sfb-integral-quotient-exchange-comparison: the parent asserts compatibility of reduction with the exchange, namely a commuting equation. The new lemma only identifies the two realizations of each scalar/geometric operation and its mate; the parent still must prove the cube and take mates.

lem-sfb-integral-quotient-pullback-face-model vs lem-sfb-integral-quotient-exchange-comparison: the parent asserts the direct-image exchange equation and its realization. The new lemma concerns no direct image or exchange and only normalizes representative faces of the left-adjoint cube.

lem-sfb-integral-quotient-section-mate-realization vs lem-weil-pbc-strict-tower-exchange-mate-normalization: the existing statement assumes properness, derived completeness and bounded-below etale-origin witnesses and compares strict tower exchange. The new one identifies single-level uncompleted internal and section operations without those assumptions.

lem-sfb-integral-quotient-pullback-face-model vs def-pd-section-derived-realization: that defines section derived tensor and operation comparisons while leaving adjunction compatibility to a theorem; this asserts simultaneous six-face K-flat models for the actual integral quotient across a geometric square.

lem-sfb-integral-quotient-pullback-face-model vs def-pd-section-derived-tensor-data: that defines the conjugated binary tensor and localized section equivalence; this asserts coefficient projection compatibility and actual scalar/geometric face representative formulas.

lem-sfb-integral-quotient-pullback-face-model vs lem-pd-module-ringed-topos-derived-comparison: that theorem assumes separated finite-type schemes over a positive-characteristic field and compares tensor and pushpull for a single condensed ring; this theorem concerns arbitrary schemes and simultaneous integral/quotient representative faces.

lem-sfb-integral-quotient-pullback-face-model vs lem-pd-section-derived-tensor-normalization: that identifies the binary internal tensor pullback oplax arrow with the ringed tensor arrow; this concerns quotient scalar change and all faces of a geometric composition square, with the actual finite projections of the integral limit.

lem-sfb-integral-quotient-pullback-face-model vs def-weil-pbc-normalized-origin-scalar-comparisons: that defines identity and successive extension comparisons on a single site; this asserts existence and simultaneous K-flat computation of geometric-square scalar faces.

lem-sfb-integral-quotient-pullback-face-model vs def-weil-pbc-ringed-projection-restriction-data: that defines tensor, exact-operation and slice restriction data; this is a theorem normalizing one actual integral quotient coefficient/geometric square.

lem-sfb-integral-quotient-pullback-face-model vs def-weil-pbc-ringed-tensor-square-presentation: that defines a square presentation and deliberately includes no derived-square tensor coherence; this asserts the actual six representative face normalizations for an integral scalar/geometric cube.

lem-sfb-integral-quotient-pullback-face-model vs lem-weil-pbc-augmented-cech-tensor-pullback: that identifies pullback of an augmented local Cech tensor action for a locally finite-type ideal; this concerns finite quotient scalar extension and geometric composition, with no Cech augmentation or ideal generators.

lem-sfb-integral-quotient-pullback-face-model vs lem-weil-pbc-augmented-diagram-projection-mate: that proves a strict-tower projection mate equation with its reduction units; this concerns no direct image or strict tower map and instead computes single-level scalar/pullback faces on one K-flat representative.

lem-sfb-integral-quotient-pullback-face-model vs lem-weil-pbc-cochain-pullback-tensor-shift: that proves signed shift compatibility of one binary tensor comparison; this normalizes scalar-extension and geometric-square faces and their finite coefficient projections.

lem-sfb-integral-quotient-pullback-face-model vs lem-weil-pbc-constant-derived-normalization-universal: that proves universality of a constant-sheaf scalar-normalization arrow for fixed rings; this uses a nonconstant integral ring sheaf and normalizes all six scalar/geometric faces.

lem-sfb-integral-quotient-section-mate-realization vs def-pd-section-derived-realization: that defines independent section operations and explicitly leaves adjunction compatibility to a comparison theorem; this asserts simultaneous geometric and quotient-scalar adjunction realization and identifies the specified lambda/rho and exchange mates.

lem-sfb-integral-quotient-section-mate-realization vs def-pd-section-derived-tensor-data: that defines localized equivalences and a conjugated tensor; this asserts equality of the independently specified scalar/geometric adjunctions and their comparison mates.

lem-sfb-integral-quotient-section-mate-realization vs lem-pd-module-ringed-topos-derived-comparison: that theorem assumes separated finite-type schemes over a positive-characteristic field and treats one condensed ring; this theorem is unrestricted in schemes and adds the simultaneous integral-to-quotient scalar and geometric mate identifications.

lem-sfb-integral-quotient-section-mate-realization vs def-pbc-successive-derived-scalar-normalization-data: that defines normalization data types on one site, with no existence theorem; this asserts actual internal/section realization across geometric sites for the specified integral quotient map.

lem-sfb-integral-quotient-section-mate-realization vs def-weil-pbc-derived-direct-image-composition: that defines conjugate composition of bounded-below etale abelian direct images; this asserts internal/section scalar and geometric realization on the entire unbounded module categories.

lem-sfb-integral-quotient-section-mate-realization vs def-weil-pbc-derived-normalization-arrows: that defines constant-sheaf coefficient normalization and an underived restriction/pullback comparison; this proves the actual internal/section unbounded scalar and geometric adjunction identifications.

lem-sfb-integral-quotient-section-mate-realization vs def-weil-pbc-ringed-slice-derived-data: that packages a slice-localization interface and its unit/counit conditions; this asserts actual quotient scalar-extension realization and the geometric mates for arbitrary scheme edges, without slicing.

lem-sfb-integral-quotient-section-mate-realization vs def-weil-pbc-successive-derived-quotient-data: that defines presentations and successive scalar-extension normalization data on one site; this asserts realization under internal/section equivalences and identifies geometric exchange mates.

lem-sfb-integral-quotient-section-mate-realization vs lem-pbc-normalized-derived-adjunction-transport: that constructs transported universal scalar-derived data for adjunctions whose right adjoints are exact; this identifies independently specified section geometric direct images, which need not be exact, and their scalar and ambient-exchange mates.

lem-sfb-integral-quotient-section-mate-realization vs lem-weil-pbc-cohomology-pullback-derived-unit: that identifies bounded-below etale abelian cohomology pullback using the derived unit and Leray; this asserts whole unbounded internal/section module scalar and geometric realization without global sections.

lem-sfb-integral-quotient-section-mate-realization vs lem-weil-pbc-derived-adjunction-shift: that proves integer-shift compatibility for a ringed adjunction; this identifies independently specified internal and section scalar/geometric adjunctions and their specified comparison mates.

## Retained returned proof and allocation

The following is the complete proof text read from the returned current-repository node before repair. It is supporting material for future workers, not proof steps in either statement-only new node.

### Returned Step 1 — section mate realization

Write $D_T=D_{n,T}$. On each corner let $E_T^R,E_T^S$ denote the termwise derived section-action equivalences. The derived pushpull normalization identifies the internal and section-module $L_{u,*},F_{u,*}$, their independently specified adjunctions, units, counits and geometric pullback compositors. The scalar-adjunction comparison identifies $D_T$ with the actual section-module derived extension along $R_T\to S_T$, using the same balanced generators on K-flat representatives. Thus we may perform the calculation in section-module categories and return through these equivalences; this preserves the specified transformations, rather than choosing new adjunctions on their endpoints. In particular the internal ambient exchanges become exactly the section-module unit--square--counit exchanges. The tensor comparison preserves flat-term K-flat representatives.

Cited statements retained for the future worker: `lem-pd-section-derived-pushpull-normalization`, `lem-sfb-internal-section-scalar-adjunction`, `lem-pe-internal-section-tensor-comparison`, `def-weil-pbc-ambient-ringed-exchange`.

Source: literature/stacks-project/derived.tex; Tags 09T5 (lemma-derived-adjoint-functors), 08BJ (lemma-adjoint-preserve-K-injectives); sites-cohomology.tex Tag 07A6 (lemma-adjoint); internal/section normalization supplied by the cited comparison nodes.

### Returned Step 2 — pullback face model

The coefficient limits and their finite projections are the ones in the statement. Apply the profinite-coefficient inverse-image theorem to the tower $A/\pi^m$. It gives $c_{u,R}:u^{-1}R_V\cong R_U$ and $c_{u,S}:u^{-1}S_V\cong S_U$, satisfying $a_Uc_{u,R}=c_{u,S}u^{-1}a_V$, where $a_T:R_T\to S_T$ is the actual projection. These comparisons commute with composition. The canonical integral-limit identification identifies this tower with the pulled-back condensed integral coefficient. Indeed, after every finite projection both coefficient comparisons send a locally constant residue to its pullback; equality follows from the uniqueness of a map into the displayed limit. Hence these are the cartesian coefficient identifications used in $\lambda_u$, and the two paths around the scheme square respect the coefficient projections.

Cited statements retained for the future worker: `lem-weil-pbc-profinite-coefficient-inverse-image`, `det-prop-sfb-qlbar-colimit-x-integral-limit`, `lem-sfb-integral-quotient-direct-image-comparison`.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-integral.proof.md; Paragraph (3), coefficient projections in the assertion that reduction of the canonical exchange is canonical; compare the cited profinite-coefficient theorem.

### Returned Step 3 — pullback face model

Let $\theta^R:L_{f',R}L_{g,R}\cong L_{h,R}L_{f,R}$ and $\theta^S$ denote the specified geometric squares. For every $M\in D_R(Y)$ the balancing maps satisfy
$$D_{X'}(\theta^R_M)\circ\lambda_{f',L_{g,R}M}\circ L_{f',S}(\lambda_{g,M})
=\lambda_{h,L_{f,R}M}\circ L_{h,S}(\lambda_{f,M})\circ\theta^S_{D_YM}.$$
To check this equality, take a flat-term K-flat representative $P$ of $M$. Geometric pullback preserves this class. Extension $P\otimes_RS$ is K-flat over $S$: tensoring it with an acyclic $S$-complex is $P$ tensored over $R$ with that complex restricted to $R$, which is acyclic. Its terms are flat by the same exact-tensor test. Thus all functors in the displayed equation are computed by the ordinary balanced tensors and pullbacks of $P$. The specified compositors are the termwise geometric ones. Both paths send a local tensor in $(f')^{-1}g^{-1}(P\otimes_RS_Y)$ to the pullback of $x\in P$ along $fh=gf'$ tensored with the pullback of $s\in S_Y$. The coefficient compatibility of Step 2 makes these the same $S_{X'}$-linear map. Balanced pure tensors generate the sheafified tensor, so equality holds degreewise, and localization gives the displayed equation for every $M$.

Cited statements retained for the future worker: `lem-pc-kflat-resolution`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `lem-pur-derived-change-of-rings`, `lem-weil-pbc-proetale-derived-pullback-composition`, `lem-sfb-integral-quotient-direct-image-comparison`.

Source: literature/stacks-project/sites-cohomology.tex; Tags 0D6D (lemma-derived-pullback-composition), 07A4 (lemma-pullback-tensor-product); elementary balanced-tensor verification of the coefficient/geometric cube.

### Returned Step 4 — section mate realization and assembly Step 2

For each vertical edge $u=f,f'$, the comparison $\rho_{u,n}$ in the statement is exactly the mate of $\lambda_u:L_{u,S}D_V\to D_UL_{u,R}$. This follows by substituting its defining adjunct into the mate formula: its transpose is $D_U(\varepsilon^R_{u,K})\circ\lambda_{u,F_{u,R}K}$. Equivalently,
$$\varepsilon^S_{u,D_UK}\circ L_{u,S}(\rho_{u,n,K})=D_U(\varepsilon^R_{u,K})\circ\lambda_{u,F_{u,R}K}.$$
Likewise $\operatorname{Ex}^R$ and $\operatorname{Ex}^S$ are exactly the mates of $\theta^R$ and $\theta^S$ by the ambient exchange definition. These equalities fix the orientation of every mate; no inverse of an exchange is taken.

Cited statements retained for the future worker: `lem-sfb-integral-quotient-direct-image-comparison`, `def-weil-pbc-adjunction-mate`, `def-weil-pbc-ambient-ringed-exchange`.

Source: literature/stacks-project/sites-cohomology.tex; Tag 07A7 (remark-base-change), the counit-adjunct definition.

### Returned Step 5 — assembly Step 2 (existing mate cube)

Apply the exchange-mate cube to the four integral categories $D_R(Y),D_R(X),D_R(Y'),D_R(X')$, the corresponding four quotient categories, the four connecting functors $D_Y,D_X,D_{Y'},D_{X'}$, and the adjunctions on $f,f'$ at the two coefficient levels. Its invertible pullback comparisons are $p_u=\lambda_u^{-1}$. The inverse-image cube hypothesis is exactly Step 3. By Step 4 the vertical comparison mates are the specified $\rho_{f,n},\rho_{f',n}$ and the two remaining mates are the actual exchanges. The cube gives, at $K$,
$$D_{Y'}(\operatorname{Ex}^R_K)\text{ followed by }\rho_{f',n,L_{h,R}K}\text{ followed by }F_{f',S}(\lambda_{h,K}^{-1})
=\lambda_{g,F_{f,R}K}^{-1}\text{ followed by }L_{g,S}(\rho_{f,n,K})\text{ followed by }\operatorname{Ex}^S_{D_XK}.$$
Precompose with $\lambda_{g,F_{f,R}K}$ and postcompose with $F_{f',S}(\lambda_{h,K})$. The inverse pairs cancel by functoriality. The resulting equation is precisely the one asserted, in $D_S(Y')$.

Cited statements retained for the future worker: `lem-weil-pbc-exchange-mate-cube`.

Source: literature/stacks-project/sites-cohomology.tex; Tag 0E47 (remark-compose-base-change-horizontal), with the cited explicit exchange-mate cube supplying the omitted mate verification.

### Returned Step 6 — section mate realization and assembly Step 3

To identify the independently specified finite rectangle, denote its pullback/reduction comparison by $\chi_u$ and its finite projection by $\operatorname{pr}_{u,n}$. In section-module coordinates, $\chi_u=\lambda_u$: both are the localization of $u^{-1}(x\otimes s)\mapsto u^{-1}x\otimes u^{-1}s$. The normalized finite projection is the adjunct of reduction of the integral counit after $\chi_u$, so Step 4 and uniqueness of adjuncts give $\operatorname{pr}_{u,n}=\rho_{u,n}$. Step 1 identifies both ambient exchanges with the ringed exchanges. The finite rectangle is therefore
$$\operatorname{Ex}^S_{D_XK}\circ L_{g,S}(\rho_{f,n,K})=F_{f',S}(\lambda_{h,K}^{-1})\circ\rho_{f',n,L_{h,R}K}\circ D_{Y'}(\operatorname{Ex}^R_K)\circ\lambda_{g,F_{f,R}K}.$$
Postcomposing with $F_{f',S}(\lambda_{h,K})$ yields Step 5. This is equality with that normalized rectangle, including its specified projection mates, not merely an isomorphism between its four objects. The formula has just been proved from the unrestricted cube; no properness or completeness condition from the four-corner applications is used.

Cited statements retained for the future worker: `lem-weil-pbc-intrinsic-finite-exchange-rectangle`, `def-weil-pbc-four-arrows`, `lem-sfb-integral-quotient-direct-image-comparison`, `def-weil-pbc-adjunction-mate`.

Source: literature/stacks-project/sites-cohomology.tex; Tags 07A7 (remark-base-change), 0E48 (remark-compatible-with-diagram); compare lean/Sheaf/Paper/FiniteReductionExchangeRectangle.lean, theorem finiteReductionExchange_rectangle.

### Returned Step 7 — assembly Step 4 (existing direct-image comparison)

The $\lambda_u$ and $\rho_{u,n}$ are natural isomorphisms by the direct-image comparison statement. Thus $L_{g,S}(\rho_{f,n})$ identifies the two sources, and $\rho_{f',n}$ and $F_{f',S}(\lambda_h)$ identify the targets. Rearranging Step 5 along those isomorphisms identifies the reduction of the actual integral exchange with the actual quotient exchange. All equalities above are equations of natural transformations (the balancing checks are natural in the representative and the mate cube is natural), so evaluation gives an equality natural in $K$. There was no use of invertibility of either exchange or of properness, completeness, boundedness or constructibility.

Cited statements retained for the future worker: `lem-sfb-integral-quotient-direct-image-comparison`.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-integral.proof.md; Paragraph (3), exchange part of reduction of the canonical maps.

## Retained prior report (Q28, read-only source)

This archived report describes the preceding seven-step delivery. Its assertions of zero new nodes and its previous validation refer only to that preceding delivery. The repair and its checks are described above. Its sources, search descriptions, proof detail and citations are retained verbatim below.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-quotient-exchange-comparison.json`: statement unchanged; seven-step split; Mathlib verdict no match for the entire normalized internal-module assertion.
- `citations.json`: one literal statement quotation for each of the 21 step/node citations.
- `report.md`: this report. `searches.jsonl` contains the real search-command records; `write_split.py` is the sandbox-local reproducible JSON writer, not a delivery node.

There are **0 new nodes and 0 new Mathlib leaves**. The sandbox initially contained no node, proof, report or search log. The current repository node was retained with its original statement, source, created/blueprint metadata and original searches, and the searches run here were appended.

## Attachments

None. Searched the actual `lean/WeilConjectures` library for the item tag and integral/quotient reduction/exchange notions, and inspected the generic exchange API. No project declaration gives the full internal-module assertion and independently normalized ringed realization. The existing ringed theorem `AlgebraicGeometry.Scheme.finiteReductionExchange_rectangle` in `lean/Sheaf/Paper/FiniteReductionExchangeRectangle.lean` was read, but it is not a declaration under `WeilConjectures/` and does not supply the internal/section identification asserted here. Its existing DAG node is reused, without claiming a finished attachment.

## WANTED

None. All sources used are present in the read repository.

## Corrections and scope

The seed had no proof. Its statement is correct and unchanged. The missing work was not an existence statement about some comparison: it was coherence of the specified balancing maps and preservation of the independently chosen derived adjunctions.

The old Poincare comparison `lem-pd-module-ringed-topos-derived-comparison` assumes separated schemes of finite type over a positive-characteristic field. I did not apply it to the arbitrary schemes here. Instead I use the existing unrestricted `lem-pd-section-derived-pushpull-normalization`, whose statement explicitly includes the independently derived units, counits and geometric composition maps. Scalar normalization is the separate unrestricted `lem-sfb-internal-section-scalar-adjunction`, and flat/K-flat preservation is `lem-pe-internal-section-tensor-comparison`.

The intrinsic rectangle statement points to `def-weil-pbc-four-corners` for its projection adjuncts, but the explicit formula is actually in `def-weil-pbc-four-arrows`. Step 6 cites that definition directly for the normalization formula. The four-arrow applications also assume properness, completeness and finite-origin witnesses. Those assumptions are not imported: Step 6 compares its displayed definitions, while Steps 3-5 independently prove the equality for arbitrary K and arbitrary scheme morphisms using the unrestricted mate cube. No four-arrow invertibility assertion or finite-origin theorem is applied. In particular this proof does not infer equality of quotient-linear maps by forgetting their quotient action; scalar restriction is not generally faithful on derived morphisms.

The proof follows the proper-image unit's paragraph (3), canonical reduction of exchange, and supplies its omitted coefficient/mate calculation. It does not change the unit route or target statements. Generic off-unit tools are declared in `split_report.tool_uses` for the maintainer to judge; no top-level `tool_uses` was added.

## Unfinished work

None for this stage-1 item. The cited nodes retain their own stage states. No Lean was written, no compiler or build was run, and no repository or launcher file was modified.

## Not duplicates

No new nodes. Whole-DAG tag and concept searches and whole-blueprint searches (`exchange`, `scalar.*pullback`, `coefficient.*square`, `internal`, `finite-exchange`, `reduction`) led to reuse of the existing mate cube, scalar adjunction comparison, derived section normalization and finite rectangle. No imported blueprint statement has the full assertion with these internal-module and normalization clauses, so `blueprint.same_as` remains empty. The existing generic ringed rectangle is a dependency, not a new relabelling of the item.

## Mathlib searches

Ran the required launcher search command with LeanFinder, LeanSearch, Loogle and grep, with two distinct natural-language phrasings. Read the hits. LeanFinder found underived `SheafOfModules.pullbackPushforwardAdjunction` and related formulas. LeanSearch found `SheafOfModules.pullbackComp`, its conjugate identity, and the ordinary `ModuleCat` scalar pseudofunctor. Loogle found `CategoryTheory.mateEquiv_vcomp`, `mateEquiv_hcomp` and conjugate variants; their source in `Mathlib/CategoryTheory/Adjunction/Mates.lean` was read. The sheaf pullback source in `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean` was also read. These are ingredients, not one-line specializations proving the actual unbounded quotient-module realization. The recorded CategoryTheory grep found no coefficient-exchange assertion. No service failure was recorded as a negative result. The initial asynchronous LeanFinder call's completed log was reused; its query was repeated once to recover and read the full printed signatures.

## Review by Q28

I read the current chapter and proper-image unit, all of the integral detail proof in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-integral.proof.md`, and Stacks `sites-cohomology.tex` Remark 07A7, Remark 0E47 (`remark-compose-base-change-horizontal`) and Remark 0E48 (`remark-compatible-with-diagram`). Stacks says the compatibility verification is omitted; the split supplies it through the existing explicit mate-cube theorem. I also read the section-module realization and scalar comparison nodes and the concrete finite rectangle Lean source to verify orientation. There are no new-node sources to review.

For Step 1 I checked the statements, not merely the proofs, of `lem-pd-section-derived-pushpull-normalization`, `lem-sfb-internal-section-scalar-adjunction`, `lem-pe-internal-section-tensor-comparison`, and the ambient exchange definition. They respectively give the actual derived adjunction and composition normalization, the actual derived scalar comparison on balanced generators, K-flat preservation, and the exact unit--square--counit formula. Their arbitrary-scheme and unbounded hypotheses match the item. This replaces the tempting but invalid use of the restricted Poincare statement.

For Step 2 the profinite inverse-image statement explicitly includes compatibility with the finite projections and compositions; the integral-limit node identifies the actual coefficient sheaf with that tower. The uniqueness check against every projection ensures that it is the coefficient identification in the prescribed lambda comparison. No claim that arbitrary inverse image preserves arbitrary limits is used.

For Step 3 I checked each domain and target of the displayed inverse-image cube. The K-flat resolution node supplies flat-term representatives, the ringed tensor/pullback node preserves them along geometric edges, the change-of-rings node computes quotient scalar extension, and the derived compositor node specifies its value on these representatives. The short exact-tensor test written in the step proves that scalar extension also preserves this class; it does not assume S is flat over R. On these models both paths send the same local balanced tensor to the same pullback tensor, with its S-action. This is an elementary comparison of the cited canonical formulas, not a new auxiliary lemma hidden behind the word 'coherent'.

For Step 4 I compared the exact defining adjunct of rho in the direct-image comparison statement with the mate definition. They agree in the displayed orientation, giving the counit identity. The ambient exchange definition gives the other two mates. In Step 5 I checked the generic mate cube's four adjunctions and all four connecting functors against Step 3. With its comparisons p_u=lambda_u^{-1}, its comparison mates are rho, not their inverses. The displayed intermediate equality has source D_{Y'}L_{g,R}F_{f,R}K and target F_{f',S}L_{h,S}D_XK. Precomposition by lambda_g and postcomposition by F_{f',S}(lambda_h) gives the exact source and target stated in the item.

For Step 6 I read the statement of the intrinsic finite rectangle and the explicit chi and finite-projection definitions in `def-weil-pbc-four-arrows`. The balanced representative formulas give chi=lambda; their counit-adjunct formulas give projection=rho. The ringed exchanges are the independently specified ones by Step 1. Consequently the rectangle with F(lambda_h^{-1}) on its right is precisely the same equation before the cancellation of Step 5. This is an identification of specified arrows. I have used only the definition formulas of the four-arrow presentation here, not its properness-dependent finite-exchange isomorphism.

For Step 7 the direct-image comparison statement asserts the requisite lambda and rho natural isomorphisms for all unbounded inputs. Functors preserve those inverses. Equality is already an equality of natural transformations, so naturality in K is preserved without making functorial choices of representative complexes.

I tested the argument at K=0, at n=1, for identity squares, for a zero/empty corner, and for unbounded K with no completeness condition. In an identity square all mate formulas reduce to the same identity under canonical comparators; for K=0 and an empty corner both paths are the unique zero morphism. The K-flat argument handles unbounded complexes with direct-sum total tensor, never an unjustified bounded resolution. No exchange inverse is used. The comparison retains the finite coefficient action at every step. All seven steps are under 2000 characters; none hides a separate non-elementary subclaim without a cited node.

I checked delivery-errors B1-B10 (no new nodes, genuine searches, preserved blueprint fields and no attachment overclaim), C1-C8 (all non-elementary ingredients cited with verbatim statement quotations, no restricted hypothesis substituted, generic tools declared), D1-D5 (the steps carry the balancing and mate argument, no new restatement lemma), and E1-E7 (typed objects and all hypotheses as above). The server-only preliminary `check_dag` and `review_split` passed. The required final dry run and direct push follow this review.

## Repair validation notes

The first required dry run exited after the duplicate gate listed additional source-tag candidates from the server tree. I opened all 22 listed statement entries (19 distinct nodes), ruled out exact matches and one-line specializations, and added the individual distinctions above. This changes the report only; it does not evade the duplicate check by removing the cited Stacks tags. The next required dry run follows this repair.
