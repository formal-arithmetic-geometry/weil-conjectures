# Stage-1 G1/D repair: lem-weil-frobenius-point-transport-natural

Files written:
- dag/nodes/sec-six-functors/lem-weil-frobenius-point-transport-natural.json: unchanged statement, stmt_deps, Lean record and inherited approvals; replaced only the split/proof records with a 1809-character assembly.
- lem-weil-point-automorphism-restriction-natural: retained unchanged, statement-only, unsplit; no Mathlib match. Original steps 1-2.
- lem-weil-isomorphism-comparison-natural: added, statement-only, unsplit; no Mathlib match. Original steps 3-5.
- lem-weil-point-automorphism-transport-scalar-extension: retained unchanged, statement-only, unsplit; no Mathlib match. Original steps 7-8.
- lem-weil-point-transformation-coefficient-descent: added, statement-only, unsplit; no Mathlib match. Original steps 6 and 9.
- citations.json: rebuilt for all 13 step/node uses with literal relevant statement excerpts.

Attachments: none. Read-only searches of lean/WeilConjectures by the blueprint tag and Frobenius-point names found no attachment. The recorded Sheaf/SixFunctors/FrobeniusPointTransportNatural.lean theorem WeilConjectures.frobeniusPointTransport_natural still has sorry at line 367; the three object-identification helper theorems also have sorry. Existing rationalization natural-transformation machinery in WeilConjectures/CategoryTheory/DerivedCategory/RationalizationRecollement.lean does not state the normalized point/common-stage assertion.

WANTED: none.

What was wrong: the previous delivery extracted only original steps 1-2 and 7-8. Despite its shorter proof, it left the specified-kappa naturality and coefficient-descent work inline; thus it did not fulfill the human's requirement to spread every argument of the original 8574-character proof across separately schedulable nodes. This repair adds both missing tasks rather than merely rebasing or compressing that text. No statement dispute or target/Lean modification is needed.

Unfinished: proofs of the four new nodes are deliberately not supplied; all four are independent stage-1 queue items, except the scalar task's existing dependence on the restriction task. No further argument is hidden in the item.

## Return points repaired

G1/D, missing original steps 3-5: lem-weil-isomorphism-comparison-natural states naturality of the SPECIFIED kappa on all ambient derived morphisms, for any scheme isomorphism and both finite and completed integral coefficients. Its finite components are the actual sheafified tensor-unit maps; its integral components are the actual theta-inverse G(u), including incomplete objects and resolution identifications. Its last assertion composes kappa with any supplied natural rho. Hence original step 5 is assigned there too, and the item only instantiates this assertion with rho = sigma and restricts the categories using the existing preservation lemma.

G1/D, missing original steps 6 and 9: lem-weil-point-transformation-coefficient-descent takes ANY supplied integral natural transformation eta, with the exact integral phi/alpha square as a hypothesis. It asserts naturality on all raw rationalized Hom tensors and on all common-stage representatives, spelling out the two functor formulas with the actual composite b = phi after F(alpha) inverse. The item supplies this hypothesis from the accepted scalar task and invokes the lemma. No rational-sum calculation or common-stage proof remains inline.

Minor missing alpha citation: assembly step 3 now explicitly cites lem-pur-integral-operations-scalar-extension, as well as lem-weil-point-sections-scalar-extension. The descent node also names this exact alpha and cites it in stmt_deps; its b is defined from that alpha, rather than an unspecified comparison.

The accepted two nodes are retained verbatim. The four statements have lengths 2318, 2382, 2743 and 3387 characters (the recorded files give the exact counts), so none carries the entire original proof. The old proof, source notes, search records and report are retained below and in returned-proof.json; the point of this delivery is the four explicit queue tasks, not the shortening alone.

## Original argument preservation map

| Original step | New statement-only task | Work that remains to be proved there |
| --- | --- | --- |
| 1 | lem-weil-point-automorphism-restriction-natural | Identify the distinguished comma coprojection using the initial index/terminal opposite; show coefficient restriction fixes constants, coordinatewise integrally. |
| 2 | lem-weil-point-automorphism-restriction-natural | Chain-map linearity and naturality; extend through all inverted quasi-isomorphisms using exact Gamma and G. |
| 3 | lem-weil-isomorphism-comparison-natural | The x maps to x tensor 1 square and sheafification; extend to all derived arrows. |
| 4 | lem-weil-isomorphism-comparison-natural | Use the actual entire-cone theta and actual completion unit u to prove the specified integral kappa square, including incomplete objects. |
| 5 | lem-weil-isomorphism-comparison-natural | Compose S(kappa) with a natural rho; the item specializes to point sections and sigma and uses the cited preservation theorem. |
| 6 | lem-weil-point-transformation-coefficient-descent | Identify scalar-extended components and prove the naturality equality on every sum of integral morphism tensors. |
| 7 | lem-weil-point-automorphism-transport-scalar-extension | Replace completed tensor by chi; check restriction on pure tensors; move sigma past chi; cancel the actual beta/phi comparisons. |
| 8 | lem-weil-point-automorphism-transport-scalar-extension | Substitute alpha T(kappa) = kappa beta; move through phi; obtain integral and rational scalar compatibility, with units and towers. |
| 9 | lem-weil-point-transformation-coefficient-descent | Identify both actual common-stage functors via phi and b; compare the same L-square; prove extension and representative independence. |

The full text and cited dependencies of EVERY original step are reproduced without shortening in the retained report below. A future worker can read that argument alongside its own self-contained statement; no proof has been put into a new node's proof field or disguised as a proof sketch in its statement.

## Sources and searches

For the item and each of the four tasks I read Deligne, Weil II, (1.1.3), p. 150 (PDF page 15), and (1.1.7), pp. 150-151 (PDF pages 15-16). The former explicitly describes rational Hom extension and the inductive limit over finite coefficient fields. The latter describes Galois action on the point fiber by transport of structure. These motivate the construction but do not assert pro-etale strict-cone normalizations: source/proof_origin explicitly mark those arguments as agent-written. No SGA source is used.

I compared the retained sandbox with the current live item: its statement, statement dependencies, blueprint, import flags, Lean record and inherited tool_uses agree exactly. The live proof is the original nine-step proof preserved in returned-proof.json; the returned sandbox proof was the insufficient four-step compression. I ran the mandatory initial dry run before editing: it exited OK (not pushed) at 5fa133494f3. That established mechanical validity of the returned head, not repair of the human return. I read the chapter, inherited f! unit, GOAL and the three-level rule. No chapter/unit route or realization record was changed.

Before adding the two ids I searched the entire DAG for kappa and all statements mentioning def-weil-inverse-image-pullback-comparison, and for natural-transformation/naturality combined with rationalization, scalar-localization and common-stage words. I opened every closest statement listed in Not duplicates. Blueprint searches used ancestor, search 'naturality', 'scalar localization', 'inverse-image comparison', 'point transport', 'natural transformation', and 'common-stage', across all chapters. The ancestor remains def-weil-global-geometric-frobenius, first cohomology-transport arrow, through the two retained via nodes. No blueprint node states the new normalized point transformations. The new blueprint.from.place names the specific old argument served and same_as is [].

For EACH added node I ran the prescribed msearch.py leanfinder, loogle, grep and leansearch commands under Q97 and this item. Every exact query and its actual response is in searches.jsonl; the alternate semantic phrasing is the distinct LeanSearch question. The kappa search found ordinary etale scheme modules and SheafOfModules.pullbackObjFreeIso_hom_naturality. I read Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean, in particular line 132: the lemma concerns freeMap for maps of generator sets, not all ambient complexes and not the specified completed strict-cone kappa. The grep for inverse-image comparison/completed pullback gave zero hits. The descent search found ThinSkeleton/ShortComplex.mapNatTrans and Localization.Construction.natTransExtension. I read Mathlib/CategoryTheory/Localization/Construction.lean:247-279: that construction extends a supplied transformation over the functors of a localization; it does not identify point sections, completed pullback alpha/phi, or common-stage point morphisms. The main CategoryTheory grep for rationalization/commonStage transformations gave zero hits. None is an exact or one-line specialization of either new statement. All services responded; no outage is recorded as absence. The previous genuine logs/search records for the accepted tasks are reused unchanged.

## Not duplicates

lem-weil-isomorphism-comparison-natural vs def-weil-inverse-image-pullback-comparison: the definition fixes kappa but explicitly postpones its naturality and resolution independence; the new node asserts those properties at finite and integral coefficients.
lem-weil-isomorphism-comparison-natural vs lem-weil-isomorphism-derived-pullback-comparison-normalization: the existing lemma identifies the integral kappa with an entire-cone unit via natural theta; it does not state the finite/integral kappa natural transformation and its composite with an arbitrary rho. It is the main tool for the integral part, retained by the human's requested cut.
lem-weil-isomorphism-comparison-natural vs lem-weil-isomorphism-derived-pullback: the existing lambda is an unspecified natural isomorphism on constructible categories; it does not identify the actual specified kappa and does not cover incomplete ambient objects.
lem-weil-isomorphism-comparison-natural vs lem-weil-isomorphism-comparison-scalar-extension: this is a change-of-coefficient square at fixed K, not naturality in arbitrary derived K-morphisms or the finite tensor-unit component.
lem-weil-isomorphism-comparison-natural vs lem-trf-integral-inverse-image-comparison-composition: this compares successive scheme maps, not the specified natural transformation in the complex variable at both coefficient levels.
lem-weil-isomorphism-comparison-natural vs lem-trf-integral-point-transport-tower-realization: the existing theorem realizes point transport in a strict integral tower; it does not state the ambient finite/integral kappa naturality for arbitrary scheme isomorphisms.
lem-weil-isomorphism-comparison-natural vs lem-weil-frobenius-point-transport-natural: the new task concerns all ambient inverse-image/pullback maps for general X,Y, not Frobenius point transport or rational/common-stage coefficient passage. It strictly separates original steps 3-5.
lem-weil-point-transformation-coefficient-descent vs prop-weil-pbc-rational-transport: the existing lemma extends functors and transformations between raw scalar-localized integral constructible categories; it does not identify the specified functor valued in D(E) via termwise tensor on point sections, nor its common-stage point target and composite b.
lem-weil-point-transformation-coefficient-descent vs lem-pur-semilinear-scalar-localization: this handles abstract raw-localization transformations and their equations, but not the point-fiber realization or normalized phi/alpha composite on common-stage representatives. It can be used by a later worker for the rational subargument, not as the entire new result.
lem-weil-point-transformation-coefficient-descent vs prop-weil-pbc-descent-functors: the existing theorem descends supplied compatible functors on its PBC pair categories; it does not identify the two concrete point functors, the composite b, or the passage from integral components to the actual rational point target. Both realization and compatibility with rationalization must be proved before applying it.
lem-weil-point-transformation-coefficient-descent vs lem-sbc-coherent-pair-functor-descent: the existing abstract pair-category descent takes compatible finite-stage transformations as input; the new task starts with integral maps, derives rational naturality on all Hom tensors, and identifies the specific composite point/pullback comparison and its actual target category. It does not re-prove abstract descent alone.
lem-weil-point-transformation-coefficient-descent vs lem-sbc-common-stage-inverse-through-karoubi: that theorem starts with already descended natural transformations and proves invertibility on idempotent summands; this task imposes no invertibility and uses raw categories, without either Karoubi completion.
lem-weil-point-transformation-coefficient-descent vs lem-weil-point-sections-scalar-extension: phi and its coherences are supplied there, but no transformation eta to pullback or its integral/rational/common-stage naturality is stated.
lem-weil-point-transformation-coefficient-descent vs lem-pur-integral-operations-scalar-extension: alpha is supplied there, but neither the point-fiber composite b nor descent of a supplied transformation into that target is asserted.
lem-weil-point-transformation-coefficient-descent vs lem-weil-frobenius-point-transport-natural: the new task assumes an arbitrary integral eta and its scalar square; it does not construct sigma, kappa, their naturality, or any Frobenius restriction comparison. It isolates only the rational/common-stage realization argument.
lem-weil-point-transformation-coefficient-descent vs lem-weil-point-automorphism-transport-scalar-extension: the scalar task proves compatibility for a particular kappa-sigma composite and asserts no naturality in K; the descent task assumes compatibility and integral naturality for arbitrary components, then proves the normalized rational/common-stage result.

No Stacks tag is newly cited. The prior retained Not duplicates section below also supplies all comparisons for the two accepted tasks.

## Review by Q97

I reviewed this G1/D repair against the full old proof, all four new statements, and every statement actually cited by each assembly step, with delivery-errors B-E open. The accepted restriction and scalar tasks are unchanged. I checked that sigma has target Gamma(GN), not Gamma(PN), and that integral P remains completed pullback over the completed coefficient sheaf. The item statement and its Lean record are untouched.

Step 1 uses the restriction task's exact unbounded naturality assertion and the point-transport definition's exact distinguished coprojection, not its postponed theorem pointer. Specializing g to g_s meets its hypothesis because Frobenius is a field automorphism; no k-linearity is required. Constant coefficients have the c-inverse target action of clause (1). Its conclusion covers finite n >= 1 and every ambient integral complex without completeness. I opened the restriction statement and verified it says all of these clauses.

Step 2 uses the NEW kappa task, including its generic composite S(kappa)rho assertion. This is the missing original 3-5 task: it asserts naturality for every derived morphism at BOTH finite and completed integral coefficients, not merely for chain maps or finite reductions. The existing preservation lemma states preservation of constructibility and completeness for both coefficient kinds. The point-fiber definition says its functors are sections there; the point-transport definition gives the actual composite Gamma(kappa)sigma. Thus the item merely instantiates the composite assertion and restricts full subcategories. I checked ell invertible on s since ell != p. The node's source argument uses the actual theta-inverse G(u), whose entire-cone normalization statement I read in full; no equality of reductions is substituted for equality into a derived limit. Its finite argument is x maps to x tensor 1 followed by sheafification; equality for inverted quasi-isomorphisms is supplied as part of the new naturality conclusion. These arguments are assigned to the new task, not left in the item.

Step 3 uses the accepted scalar task's exact t equation and rational version, the point-transport definition to identify t with iota, and the new descent task's exact compatibility hypothesis. I checked that the scalar task uses phi on P_E K and Gamma(alpha) inverse in exactly that order, so both sides have source Gamma(TK) and target Gamma(P_E K) tensor O_L. The scalar comparison statements explicitly give alpha and phi with identity and tower coherence; they are cited at this step, correcting the return's missing alpha cite. I opened the finite-free chi/beta normalization statements too: their actual completion maps, not arbitrary isomorphisms, are the ones the accepted scalar task specifies.

Step 4 uses the descent task with the supplied family from steps 2-3. I checked its rational conclusion ranges over arbitrary sums of integral morphism tensors, including derived arrows not represented by a single integral map. Its common-stage conclusion names the actual functor formulas, with b = phi after F(alpha) inverse, and states the equation at the same L as the representative. Source and target of b are H_L(K tensor_E L) and H_E(K) tensor_E L, so the composite b' H_L(u) b inverse is typed in the target common-stage Hom. The point-transport definition constructs exactly these tensor-extended and stage-represented components. No point-fiber equivalence or fullness is assumed. The source defines equality after a further common field, which is exactly the representative-independence conclusion now assigned to this task. This restores original step 9 in a new node instead of compressing it inline.

For the kappa task I tested g = id, X or Y empty, zero maps and objects, shifts, finite n = 1, arbitrary derived arrows, and an incomplete integral ambient N. At g = id the completed kappa is the actual completion unit and need not be invertible; the statement asserts naturality without adding such an invertibility claim. For the descent task I tested eta = 0, identity eta when g = id, shifted objects, L = E, a ramified E subset L, different fields of definition, successive E subset L subset M, and nonzero rational morphisms with the zero component family. These cases use no injectivity or full faithfulness of transition functors: equality is transported to a common later stage, never reflected back. Its hypothesis is precisely the integral compatibility supplied by the accepted scalar task; no new boundedness, finite Tor or field-linearity condition has been smuggled into the item.

For B1-B10, each task is a self-contained statement with proof [], proof_deps [] and proof_origin null, real source/place, full blueprint ancestry and genuine searches. For C1-C8, the item's only non-elementary assertions are conclusions of its cited tasks or existing preservation/comparison statements. All 13 uses have literal, relevant statement quotes in citations.json. The generic off-unit tools are declared only in split_report.tool_uses; inherited approved tool_uses are preserved. For D1-D5, neither added task restates the whole item: one is general ambient kappa naturality, the other is normalized descent of arbitrary supplied eta. The four tasks divide the original argument rather than passing the whole item to a child. For E1-E7, I checked all hypotheses and map types above, completed versus discrete coefficients, finite n, ramification and the common-stage equivalence relation. No source error was found.

The 1809-character item proof has no step over 2000 characters and no hidden comparison or localization argument. Every original argument is assigned in the preservation table, with its full text retained below. The batch-5 dependency closure is unchanged: the original item already used the normalization tool, and the new kappa task uses that same coefficient identification, not any trace-formula proof. All file writes are confined to the named sandbox; no compiler, Lake, repository git command, local preflight/check_dag/review_split, repository edit, launcher edit, or subagent was used.

## Delivery status: server storage failure

The repaired delivery was dry-run twice, sequentially, with each process polled to exit. Both invocations exited 1 without pushing, with the sole preflight reason: tools/check_dag.py could not verify its DAG baseline because the server returned [Errno 28] No space left on device. The first temporary baseline path was /tmp/sheaf-dag-base-6ke8z0r6/dag/nodes/sec-smooth-purity/lem-weil-pbc-descend-model-localization.json; the retry path was /tmp/sheaf-dag-base-w7e5xcbk/dag/nodes/sec-smooth-purity/lem-sc-field-higher-direct-image-stalk.json. The standalone server review_split check passed. The full dry run has not passed, and no push was attempted. All four task nodes, the revised item, citations, original proof and logged searches remain in this sandbox for the next authorized retry after server space is restored. No server/launcher file was edited or deleted to bypass this failure.

## Retained report and original proof from the returned delivery

Everything below is retained historical provenance. Its earlier claim that the remaining inline arguments were sufficient is superseded by the G1/D repair above.

# Stage-1 repair: lem-weil-frobenius-point-transport-natural

1. Files written:
   - dag/nodes/sec-six-functors/lem-weil-frobenius-point-transport-natural.json: unchanged statement; four assembly steps, 2565 characters total.
   - dag/nodes/sec-six-functors/lem-weil-point-automorphism-restriction-natural.json: statement-only, status unsplit, no Mathlib match. The independent task is to identify the specified comma-index coprojection, normalize its finite/completed coefficient action, and descend its chain naturality to the entire derived category.
   - dag/nodes/sec-six-functors/lem-weil-point-automorphism-transport-scalar-extension.json: statement-only, status unsplit, no Mathlib match. The independent task is the pure-tensor restriction square through the specified completion comparisons, and its composition with the specified pullback comparison.
   - citations.json: literal statement excerpts for every step/node use.
   - searches.jsonl: eight actual searches, retained exactly as msearch wrote them. The inherited item's searches are also retained in its JSON.
   - returned-proof.json and this report preserve all nine returned steps verbatim. repair.py and write_report.py are sandbox-only preparation scripts, not library changes.
2. Attachments: none. The item tag and Frobenius point-transport searches in lean/WeilConjectures find no declaration stating the whole result. The recorded Sheaf.SixFunctors.FrobeniusPointTransportNatural has frobeniusPointTransport_natural ending in sorry and three sorry helper object equalities. It is statement material, not an attachment. The generic coefficient-change theorem in WeilConjectures/SixFunctors/Etale/Derived/CoefficientChange.lean concerns discrete finite coefficients on the etale site and restriction of scalars; it does not identify our pro-etale completed sigma/kappa. Neither new statement is attached.
3. WANTED: none. The relevant Deligne paper and existing DAG interfaces are available.
4. Problem repaired: the human returned the 8574-character proof as too much work for one task. This delivery actually creates two self-contained statement-only tasks, not a rebase or unchanged re-push. The current repository has the returned nine-step proof; the sandbox initially had only dispatcher markers, no nodes, report or search log. I copied the current node and recovered the previous N6 and NI reports from coord/reports, retaining the former below. No item statement, target, Lean, chapter, unit, or maintainer-owned field is changed. The inherited f! unit binding remains historically unrelated to this point-transport factor, as the previous review already reported; the blueprint ancestor's first transport arrow is followed.
5. Unfinished: the two new proofs are intentionally not written in the nodes. They are parallel stage-1 tasks. This worker only supplies their statements, source locations and real Mathlib searches, with empty proof and proof_deps and null proof_origin. Their proof obligations and the complete previous argument are preserved here for subsequent workers.

## Repair map and comparable work

The first task takes old steps 1-2 (2657 characters): a site-equivalence/comma-category calculation, module coefficient normalization at every finite projection, chain naturality, and localization. The second takes old steps 7-8 (2530 characters): completed coefficient extension via chi and the pure-tensor square, followed by the alpha/kappa/beta substitution, rationalization and successive-extension coherence. Thus the two tasks have comparable original argument sizes and different mathematical interfaces. Neither asserts the whole item: the first never mentions iota or completed derived pullback, and the second asserts coefficient compatibility, not naturality on any derived category. Both work for any automorphism of Spec k rather than merely Frobenius.

All remaining parts of the original argument are kept explicitly as short assembly. Old step 3 is the finite x-to-x-tensor-1 naturality calculation and inverse-arrow cancellation in new assembly step 2. Old step 4 is the actual-unit/theta equation, with its derived naturality calculation, in that same step. Old step 5 is the composition with sigma and restriction to the full constructible categories there. Old step 6 is the sum of tensors calculation in new step 3. Old step 9 is the common-stage representative/conjugation argument in new step 4. No implication is replaced by the words 'transport' or 'standard'. In particular equality of reductions is never used as equality of maps into a derived limit. The entire returned text is reproduced below, so none of its arguments is lost to the shortening of the assembly.

## Sources read

For the item and both new nodes I read Deligne, La conjecture de Weil II, (1.1.3), printed p.150 (PDF page 15), and (1.1.7), printed pp.150-151 (PDF pages 15-16), using pdftotext. The first gives the rational Hom tensor formula and finite coefficient-field passage; the second gives transport of structure on the geometric fiber and its functorial use. Neither purports to supply the pro-etale comma-object or strict completion calculation. Those are explicitly agent-formulated extractions from the returned proof; the source fields say this. I read the current blueprint ancestor def-weil-global-geometric-frobenius in main-20261015 and its two first cohomology arrows. The new nodes' blueprint.from/via track that ancestor through this item, the point-transport definition and cohomology-transport definition. No forbidden route source is used.

For the restriction task I opened the full statements of def-weil-proetale-inverse-image, lem-weil-proetale-isomorphism-inverse-image, def-weil-inverse-image-pullback-comparison, lem-weil-point-proetale-sections-exact and def-weil-abstract-derived-category. The first really defines the small comma category and the opposite-indexed colimit; the second really gives evaluation at (s,g) naturally; the third really specifies the completed coefficient map by all projections and says the transported module functor is exact; the fourth explicitly handles arbitrary sheaves of rings, not just finite coefficients; the last explicitly localizes complexes at quasi-isomorphisms.

For the scalar task I opened the full statements of lem-weil-isomorphism-comparison-scalar-extension, lem-weil-finite-free-completed-scalar-comparison, lem-weil-point-sections-scalar-extension, lem-weil-isomorphism-derived-pullback and lem-pur-integral-operations-scalar-extension. These fix, respectively, beta and its kappa equation; the actual zero-shifted-coordinate chi and finite freeness; phi as the inverse of Gamma(chi) after sections-tensor; completeness/constructibility of the needed objects; and the canonical alpha and its identity/successive-extension coherences. These are the precise normalizations used in the new statement, not arbitrary choices of isomorphisms.

## Searches and duplicate check

Before writing the new files I searched the whole DAG by sigma, point, inverse-image, comparison, restriction and coefficient-extension words, and used tools/blueprint_refs.py search for natural transformation, point transport, comparison morphism, scalar extension, inverse image, restriction transport, coefficient comparison, completed scalar, transport of structure, isomorphism inverse image and restriction. The ancestor command returns def-weil-global-geometric-frobenius. I examined the closest statements listed below and the existing source declarations. No distinct blueprint node states either normalized point-section map. same_as is therefore [] for both new nodes and unchanged for the item.

For each new node I ran leanfinder, loogle, grep and leansearch through the prescribed msearch.py command. Both semantic services returned eight hits and both Loogle and grep commands succeeded. The alternate semantic wording was LeanSearch's distinct question. The restriction queries returned Scheme.restrictFunctorGamma, ordinary etale algebra facts, Point.sheafFiberComapIso, Sheaf.natTransGammaRes and PresheafOfModules.restriction_app. I read Mathlib/CategoryTheory/Sites/Point/Comap.lean:69 and its hypotheses, CategoryTheory/Sites/GlobalSections.lean:167-181, and Algebra/Category/ModuleCat/Presheaf.lean:288-301: these supply pieces on ordinary sites/presheaves but do not normalize the designated pro-etale coprojection and completed ring action or give the whole derived statement in one line. The scalar queries returned ordinary etale algebra facts and LinearEquiv.extendScalarsOfIsLocalizationEquiv; I read RingTheory/Localization/Module.lean:240-254, which compares linear equivalences over a ring and its localization and has no sheaf completion map or sections comparison. Loogle '"sheafTensor"' and the completed scalar grep in AlgebraicGeometry returned zero hits. Thus both new nodes remain unsplit, not Mathlib leaves. All query strings and actual top results are copied from the genuine log into the nodes. No unavailable service has been represented as a negative result.

## Not duplicates

lem-weil-point-automorphism-restriction-natural vs lem-weil-frobenius-point-transport-natural: the new node identifies the actual restriction/coprojection at any point automorphism with its coefficient-normalized evaluation map, before kappa; it supplies a lower map used in the assembly and asserts no iota naturality or scalar passage.
lem-weil-point-automorphism-restriction-natural vs lem-weil-proetale-isomorphism-inverse-image: the existing statement gives evaluation naturally but does not identify the distinguished comma-index coprojection with the identity or prove the constant-section sigma formula and unbounded derived restriction transformation.
lem-weil-point-automorphism-restriction-natural vs lem-weil-point-proetale-sections-exact: exactness of sections does not supply any automorphism restriction map or its coefficient normalization.
lem-weil-point-automorphism-restriction-natural vs lem-weil-isomorphism-derived-pullback-comparison-normalization: normalization concerns kappa into completed pullback; the new node concerns sigma before kappa, on all ambient complexes, including incomplete ones.
lem-weil-point-automorphism-transport-scalar-extension vs lem-weil-frobenius-point-transport-natural: the new statement contains the specified sigma/chi/beta square for arbitrary automorphisms and its kappa composite; it asserts no naturality in K at finite, integral, rational or common-stage coefficients. It does not restate the whole item.
lem-weil-point-automorphism-transport-scalar-extension vs lem-weil-isomorphism-comparison-scalar-extension: the existing equation compares kappa only; it never mentions restriction on point sections, sigma or phi. The new argument establishes the additional restriction square and composes it with that equation.
lem-weil-point-automorphism-transport-scalar-extension vs lem-weil-point-sections-scalar-extension: the existing lemma defines phi and its coherences but gives no square with point-automorphism restriction or t.
lem-weil-point-automorphism-transport-scalar-extension vs lem-weil-finite-free-completed-scalar-comparison: finite freeness and chi do not compare any restriction map or its pullback composite.
lem-weil-point-automorphism-transport-scalar-extension vs lem-pur-integral-operations-scalar-extension: alpha and its coherence do not specify a square with sigma and iota.
lem-weil-point-automorphism-transport-scalar-extension vs lem-trf-point-complex-scalar-extension: the latter treats ordinary finite-ring tensor on finite-Tor complexes, not completed valuation-ring coefficients and chi/beta.
lem-weil-point-automorphism-transport-scalar-extension vs lem-sp-proetale-scalar-tensor-normalization: that lemma normalizes a finite-ring pullback/tensor comparison on sheaves, not restriction of point sections through the specified completion map.
lem-weil-point-automorphism-transport-scalar-extension vs lem-trf-integral-inverse-image-comparison-composition: that equation compares two successive scheme isomorphisms at one coefficient field, not extension of the coefficient field on point sections.
lem-weil-point-automorphism-transport-scalar-extension vs lem-trf-integral-pullback-comparison-realization: that statement fixes entire-diagram pullback comparisons, but has no restriction/coprojection or sections square.
lem-weil-point-automorphism-transport-scalar-extension vs lem-pur-composition-comparison-scalar-compatibility: that statement is about composition of exceptional smooth operations and purity, not ordinary point restriction.
lem-weil-point-automorphism-transport-scalar-extension vs lem-trf-frobenius-transports-scalar-extension: the latter compares compact-support transports of a general variety and depends on the present item; it cannot be a dependency of this split. The new lemma never uses compact supports.

No Stacks tag is introduced in either new node, so there are no additional same-tag pairs to explain.

## Review by Q97

I checked the current item, both new statements, all nine old proof steps and the literal statements of every node cited by the new four-step assembly. I retained the finite/integral versus rational/common-stage distinction made by the earlier maintainer: sigma targets Gamma(g^{-1}N), not Gamma(Lg^*N). I checked source and target of every beta, alpha, phi and kappa composition. The item statement is byte-for-byte unchanged.

Assembly step 1 uses the new restriction lemma for the coefficient-normalized sigma on all ambient complexes, and the point-transport definition for the exact same distinguished coprojection. The new lemma introduces U, V, the colimit coprojection, g, the coefficient sheaves and all actions, so the identification is a specialization, not an appeal to its unwritten proof. Frobenius is a scheme automorphism; it need not fix k pointwise.

Assembly step 2 uses the finite comparison definition for x to x tensor 1, the derived-category definition for inversion of quasi-isomorphisms, and the whole normalization statement for the natural theta with theta kappa = G(u). The displayed cancellation proves naturality of the specified integral morphism, not a choice of some invertible morphism. I checked g_s is an isomorphism and ell is invertible because ell differs from the residue characteristic p. Isomorphism-derived-pullback states both finite and completed integral preservation. The point-fiber definition says it is sections at those stages, and the point-transport definition specifies Gamma(kappa) sigma. Composing those two naturality squares proves precisely the required finite/integral iota square.

Assembly step 3 uses raw rationalization's Hom tensor E formula, the point functor's linear formula on pure tensor morphisms, and the derived operation's scalar-localized formula. I checked it handles finite sums, not just morphisms represented by one integral chain map. The new scalar lemma's t is exactly iota after g = g_s. It states the full integral equation and its rationalized form under the specified alpha and phi, including successive extensions. Thus scalar compatibility here does not rely on unspecified completion identifications. In the scalar statement, GK and PK are complete and constructible by the cited isomorphism lemma; the assertion is not made for incomplete K.

Assembly step 4 uses the algebraically-closed category's actual morphism colimit and equality after a larger field. The point-fiber definition gives conjugation by phi; the operations definition gives conjugation by alpha. Its transformed square is the finite-stage L square proved in step 3. Further extension preserves it by the scalar lemma. I checked objects initially defined over different coefficient fields and that both functors use the same common-stage representative. No trace theorem, duality assertion or assumption leaf is used to prove this coefficient descent.

For the two new tasks I tested g = id, zero complexes, zero and identity morphisms, arbitrary shifts, n = 1, L = E and E subset L subset M. At g = id the restriction/coprojection is the identity under the specified evaluation, and the comparison into completed pullback is the actual completion unit. The scalar equation has source Gamma(TK) and target Gamma(P_E K) tensor O_L. A ramified extension uses the finite-free/strict-completion comparison with cofinal uniformizer indices, not equality of same-index quotients. No new finite Tor hypothesis is introduced. The unbounded restriction assertion remains valid on incomplete objects because only the exact inverse-image functor, not completed pullback, is involved.

I checked delivery-errors B-E against the files: two self-contained statement-only unsplit nodes, no proof sketches in their statements, no new definitions, genuine logged searches in all required kinds, no nonexistent attachment, no new node hiding the whole item, and every cited assertion supplied by a statement rather than a proof. The site-normalization and scalar-square tasks are nontrivial and comparable, not elementary one-line copies of an existing fact. The remaining localization, sum and conjugation computations are explicit assembly. Every assembly step is under 2000 characters and the total is under 3000. citations.json quotes only literal substrings of cited statements. All writes are confined to this sandbox. No compiler, Lake, live git command, direct local check_dag/review_split/preflight, repository edit or launcher edit is used.

## Preserved returned proof, without shortening

### Original step 1

Write $g=g_s$, $U=(s\xrightarrow{\mathrm{id}}s)$ and $V=(s\xrightarrow g s)$. The evaluation isomorphism $(g^{-1}M)(U)\simeq M(V)$ in [lem-weil-proetale-isomorphism-inverse-image](1) identifies the specified coprojection/sheafification in [def-weil-frobenius-point-transport] with evaluation at $V$: at the distinguished index the map $U\to u_g(V)$ is the indicated diagonal, and reindexing along the inverse site equivalence sends it to $\mathrm{id}_V$. More explicitly, $(V,\mathrm{diagonal})$ is initial in the indexing category $\mathcal I_U$: a map $U\to u_g(W)$ is uniquely a map $V\to W$ under this equivalence. It is therefore terminal in $\mathcal I_U^{\mathrm{op}}$, so the colimit is $M(V)$ with that coprojection the identity. These identifications are natural in $U$, hence already a sheaf, and sheafification preserves them. Thus $\sigma_M$ is restriction along $g:V\to U$ under this identification. Restriction respects addition and the module action. For a finite coefficient $a$, the structure map of [def-weil-proetale-inverse-image] sends the pulled-back constant section $a$ to the constant section $a$; hence $\sigma_{\Lambda_s}(a)=c_\Lambda^{-1}(a)$. For integral $a\in\mathcal O_E$ the same equality follows after every projection to $A_{E,m}$, using the defining formula for $c_{\mathcal O_E}$ in [def-weil-inverse-image-pullback-comparison]; equality in the ordinary sheaf inverse limit is equality of all coordinates. Consequently $\sigma_M(ax)=c_\Lambda^{-1}(a)\sigma_M(x)$, which is precisely linearity for the action in clause (1), also for the completed coefficient sheaf.

Uses: def-weil-frobenius-point-transport, lem-weil-proetale-isomorphism-inverse-image, def-weil-proetale-inverse-image, def-weil-inverse-image-pullback-comparison.

### Original step 2

For a chain map $u:N\to N'$, sheaf-map naturality says $u(V)\operatorname{res}_g=\operatorname{res}_g u(U)$; the functorial colimit coprojection and sheafification in [def-weil-proetale-inverse-image] say $(g^{-1}u)(U)\operatorname{ins}_N=\operatorname{ins}_{N'}u(V)$. Composition gives $\Gamma(s,g^{-1}u)\sigma_N=\sigma_{N'}\Gamma(s,u)$. Apply this also to each differential; the maps are linear maps of complexes. Sections preserve quasi-isomorphisms by [lem-weil-point-proetale-sections-exact], and the module inverse-image functor does so by [def-weil-inverse-image-pullback-comparison]. The localization defining $D$ in [def-weil-abstract-derived-category] is generated by chain maps and formal inverses of quasi-isomorphisms. For an inverted map $v$, its naturality equation gives the equation for $v^{-1}$ by multiplying by the two inverses. It therefore gives the equation for every finite composite of generators. This descends $\sigma$ and its naturality to the asserted derived functors, without a boundedness or completeness hypothesis on $N$.

Uses: def-weil-proetale-inverse-image, lem-weil-point-proetale-sections-exact, def-weil-inverse-image-pullback-comparison, def-weil-abstract-derived-category.

### Original step 3

At finite level the comparison in [def-weil-inverse-image-pullback-comparison](a) is $x\mapsto x\otimes1$. For a chain map $u$, both paths in its naturality square send $x$ to $g^{-1}u(x)\otimes1$, and sheafification preserves this equality. The same formal-inverse calculation of Step 2 gives $Lg_s^*(u)\kappa_N=\kappa_{N'}g_s^{-1}(u)$ for every derived morphism. This proves naturality of the specified finite comparison, rather than choosing some isomorphism between the functors.

Uses: def-weil-inverse-image-pullback-comparison.

### Original step 4

At integral level use [lem-weil-isomorphism-derived-pullback-comparison-normalization], applicable because $g_s$ is an isomorphism and $\ell$ is invertible on $s$. It identifies the SPECIFIED $\kappa_N$ with $\theta_{g,N}^{-1}G(u_N)$, where $G=g_s^{-1}$, $u$ is the actual natural completion unit, and $\theta$ is natural for derived morphisms. Thus for $v:N\to N'$,
$$Lg_s^*(v)\kappa_N=\theta_{g,N'}^{-1}G(\widehat v)G(u_N)=\theta_{g,N'}^{-1}G(u_{N'})G(v)=\kappa_{N'}G(v).$$
This uses the whole strict-cone normalization in the cited statement; equality of maps to individual reductions would not suffice.

Uses: lem-weil-isomorphism-derived-pullback-comparison-normalization.

### Original step 5

For $\Lambda=A_{E,n},\mathcal O_E$, [lem-weil-isomorphism-derived-pullback] ensures that $Lg_s^*$ preserves the indicated constructible category. The point functor is sections there by [def-weil-finite-coefficient-point], and [def-weil-frobenius-point-transport] defines $\iota_N=\Gamma(s,\kappa_N)\sigma_N$. Composing the squares in Steps 2-4 yields
$$\operatorname{Fib}_s(Lg_s^*v)\iota_N=\Gamma(s,\kappa_{N'})\Gamma(s,g_s^{-1}v)\sigma_N=\iota_{N'}\operatorname{Fib}_s(v).$$
These are maps in the full bounded point categories, so the same equality proves the required natural transformation there.

Uses: lem-weil-isomorphism-derived-pullback, def-weil-finite-coefficient-point, def-weil-frobenius-point-transport.

### Original step 6

For $\Lambda=E$, [def-weil-rationalization-karoubi] gives the same integral objects and morphisms that are finite sums $\sum_j v_j\otimes a_j$. By [def-weil-finite-coefficient-point], the fiber sends this to $\sum_j a_j(\Gamma(s,v_j)\otimes E)$, and [def-weil-frobenius-point-transport] gives $\iota^E_N=\iota^{\mathcal O_E}_N\otimes E$. The rational pullback is the scalar-localized integral operation [def-weil-derived-pullback-tensor-hom]. Tensor the integral naturality equality with $E$, multiply by $a_j$, and add over $j$. This gives naturality for every rational morphism; it includes morphisms not represented by a single integral chain map.

Uses: def-weil-rationalization-karoubi, def-weil-finite-coefficient-point, def-weil-frobenius-point-transport, def-weil-derived-pullback-tensor-hom.

### Original step 7

Fix a finite extension $E\subset L$ and put $T=-\widehat\otimes_{\mathcal O_E}\mathcal O_L$. Let $\beta_K:T(g_s^{-1}K)\simeq g_s^{-1}(TK)$ be the explicitly defined isomorphism in [lem-weil-isomorphism-comparison-scalar-extension]. The sections comparison $\varphi_H:\Gamma(s,TH)\simeq\Gamma(s,H)\otimes_{\mathcal O_E}\mathcal O_L$ is the inverse of sections-tensor followed by $\Gamma(s,\chi_H)$ by [lem-weil-point-sections-scalar-extension]. Define $\psi_K=(\varphi_{g_s^{-1}K})\circ\Gamma(s,\beta_K)^{-1}$. Then
$$\psi_K\sigma_{TK}=(\sigma_K\otimes1)\varphi_K.$$
To check this, use the specified $\chi$ to replace $T$ by ordinary finite free tensor [lem-weil-finite-free-completed-scalar-comparison]. On a local pure tensor $x\otimes b$, restriction and the distinguished inverse-image coprojection send it to $\operatorname{ins}(x|_V)\otimes b$ in either order: restriction fixes the constant coefficient $b$, and the tensor comparison sends the inverse image of a pure tensor to the tensor of the inverse images. This is exactly the local formula for $b_K$ and hence for $\beta_K$. Additivity and the tensor relations give equality of the sheaf maps. Step 2 applied to the derived map $\chi_K$ moves $\sigma$ through $\chi_K$. The two $\chi$ factors then cancel by the displayed definition of $\beta$; the defining formula for $\varphi$ then gives the written equation on derived sections. The objects to which $\varphi$ is applied are constructible by [lem-weil-isomorphism-derived-pullback].

Uses: lem-weil-isomorphism-comparison-scalar-extension, lem-weil-point-sections-scalar-extension, lem-weil-finite-free-completed-scalar-comparison, lem-weil-isomorphism-derived-pullback.

### Original step 8

Let $\alpha_K:T(Lg_{s,E}^*K)\simeq Lg_{s,L}^*(TK)$ be the canonical comparison of [lem-pur-integral-operations-scalar-extension]. By [lem-weil-isomorphism-comparison-scalar-extension], $\alpha_K T(\kappa^{E}_K)=\kappa^{L}_{TK}\beta_K$. Naturality of $\varphi$ in [lem-weil-point-sections-scalar-extension] and Step 7 therefore give
$$\varphi_{Lg_{s,E}^*K}\Gamma(s,\alpha_K)^{-1}\iota^{\mathcal O_L}_{TK}=(\iota^{\mathcal O_E}_K\otimes1)\varphi_K.$$
Indeed substitute $\iota=\Gamma(\kappa)\sigma$, replace $\Gamma(\alpha)^{-1}\Gamma(\kappa^L)$ by $\Gamma(T\kappa^E)\Gamma(\beta)^{-1}$, move $\Gamma(T\kappa^E)$ through $\varphi$ using its naturality, and apply Step 7. Tensor with $L$ to get precisely compatibility of $\iota^E$ with rational coefficient extension, under the displayed sections/scalar-extension and pullback/scalar-extension comparisons. Their identity and successive-extension coherences are those in the two cited scalar-extension lemmas. Thus this equality persists after any further finite coefficient extension.

Uses: lem-pur-integral-operations-scalar-extension, lem-weil-isomorphism-comparison-scalar-extension, lem-weil-point-sections-scalar-extension.

### Original step 9

Finally a morphism between $(E,K)$ and $(E',K')$ in [def-weil-algebraically-closed-coefficients] is represented over some common finite field $L$ by $v:K\otimes_EL\to K'\otimes_{E'}L$. The fiber functor acts on it by conjugating $\operatorname{Fib}_s(v)$ with the scalar comparisons [def-weil-finite-coefficient-point]. The pullback acts on it by conjugating $Lg_{s,L}^*(v)$ with the rationalized pullback/scalar-extension comparisons $\alpha$ of [lem-pur-integral-operations-scalar-extension], as specified at the algebraically closed level of [def-weil-derived-pullback-tensor-hom]. By Step 8 the scalar extension of each point-transport component equals the component at that common stage. Hence the desired naturality square is, after those conjugations, exactly the $L$-naturality square proved in Step 6. It commutes. A further extension preserves this equality by Step 8, and equality in the morphism colimit is equality at a further common stage. Consequently the result is independent of the representative and proves clause (2) for $\Qlb$.

Uses: def-weil-algebraically-closed-coefficients, def-weil-finite-coefficient-point, def-weil-derived-pullback-tensor-hom, lem-pur-integral-operations-scalar-extension.

## Previous stage-1 report retained for provenance

# Stage-1 delivery: lem-weil-frobenius-point-transport-natural

1. Files written:
   - dag/nodes/sec-six-functors/lem-weil-frobenius-point-transport-natural.json: statement, split into nine proof steps, unchanged statement, no Mathlib match.
   - dag/nodes/sec-six-functors/lem-weil-isomorphism-comparison-scalar-extension.json: one new statement-only auxiliary lemma, unsplit, no Mathlib match. It concerns the specified integral comparison on arbitrary scheme isomorphisms, not point transport.
   - citations.json: one literal statement excerpt for each of the 26 step/node citations.
   - searches.jsonl: actual msearch output records; retained unmodified.
2. Attachments: none. Searched the exact blueprint tag and point-transport terminology in WeilConjectures of the read-only slopmaster2 checkout. No declaration stating all clauses was found. Broader Frobenius results concern trace operators rather than this comparison of fibers; no exact attachment is claimed. No master sorry declaration was used as proof evidence.
3. WANTED: none.
4. Problems found: the original node has no proof and only two inherited grep searches. Its definition already warns that naturality of the integral comparison is a separate assertion. The existing comparison-normalization theorem supplies this for derived morphisms; the scalar-extension theorem by itself gives an isomorphism of operations, not its compatibility with the SPECIFIED kappa. That last compatibility is isolated in the new lemma. No statement change or dispute is required. The inherited unit metadata points to sk-prop-sf-rf-shriek-preservation, now an f! preservation unit in sec-six-functors-basics; it does not describe the Frobenius factor and appears historically misbound. I preserved this maintainer-owned metadata, followed the recorded blueprint ancestor's actual transport arrow, and declared generic off-unit tools. Maintenance can review the binding independently; no unit route is replaced.
5. Unfinished: the new comparison lemma is intentionally statement-only, as required for a one-level split. No additional item work is left before delivery, subject to server preflight.

## Sources and search results

Read Deligne, Weil II, (1.1.3), printed p. 150, for raw rationalization and finite-field-of-coefficients passage, and (1.1.7), printed pp. 150-151, for transport on the geometric fiber. The exact pro-etale complex formulas are an agent expansion, not a theorem attributed verbatim to Deligne. Read Bhatt-Scholze Section 6.5, especially Example 6.5.2 and Lemma 6.5.9(4), printed pp. 49-51: completed pullback is pullback followed by completion. The new lemma's formula is explicitly marked agent-formulated; Bhatt-Scholze is contextual source, not claimed to state that formula. Also read Stacks Tag 03D6, sites-modules-definition-pushforward, including its pullback tensor formula, and Tag 08TC, derived-definition-derived-limit: its warning about nonunique derived limits is exactly why we do not compare only individual reductions. Read the archived blueprint ancestor def-weil-global-geometric-frobenius and its two first transport arrows. No SGA source is used.

Searches were made through msearch.py only. The item's first wording returned Witt-vector isocrystal Frobenius maps and underived module/pushforward transformations; a second wording returned Zariski-module restriction identifications. The successful Loogle retry gives Point.sheafFiberComapIso; reading Comap.lean shows only an abstract underived sheaf-fiber isomorphism, not this module/completed/derived transport. The first Loogle query reports an unknown identifier, recorded literally, and was not used as evidence of absence. The grep found the pro-etale topology and ell-adic sheaf definitions. For the new lemma, two semantic phrasings returned scheme fiber-product identities and maps on free sheaves; LeanSearch returned SheafOfModules.pullbackObjFreeIso_hom_naturality and unrelated adic/uniform-space completion results. Read Sheaf/PullbackFree.lean: these are ordinary sheaves and free-module maps, with no strict quotient-cone comparison. Loogle returned presheaf pullback identities. The recorded grep found only unrelated lattice/topological/manifold completions. Thus neither the item nor the new auxiliary comparison is a one-line Mathlib specialization. All query strings are copied from searches.jsonl; no unavailable service is reported as no match.

Before naming the new lemma, searched the whole DAG for the specified comparison definition, kappa/naturality and scalar-extension terminology, and the whole blueprint with blueprint_refs.py (point transport, comparison morphism, completion unit, scalar extension, inverse image, completion comparison). Opened all existing statements referring to def-weil-inverse-image-pullback-comparison. None gives its coefficient-extension square. The new node and item have same_as = []; their ancestor and via list retain the existing historical chain.

## Not duplicates

lem-weil-isomorphism-comparison-scalar-extension vs lem-weil-isomorphism-derived-pullback-comparison-normalization: normalization identifies kappa with inverse image of the actual completion unit and gives derived naturality at one coefficient field; the new lemma compares the SPECIFIED maps between two different coefficient fields.
lem-weil-isomorphism-comparison-scalar-extension vs lem-pur-integral-operations-scalar-extension: that statement gives the natural comparison alpha of pullback operations and coefficient extension; it contains no equation involving the specified inverse-image comparison kappa.
lem-weil-isomorphism-comparison-scalar-extension vs lem-weil-finite-free-completed-scalar-comparison: that statement specifies chi and its invertibility for a finite coefficient extension; it has no scheme isomorphism or comparison to completed pullback.
lem-weil-isomorphism-comparison-scalar-extension vs lem-weil-point-sections-scalar-extension: that statement compares section functors and coefficient extension, whereas the new lemma is module-valued on arbitrary X and Y and never takes sections.
lem-weil-isomorphism-comparison-scalar-extension vs lem-trf-integral-point-transport-tower-realization: realization identifies integral point transport with its single-field reduction tower; it does not compare finite coefficient extensions.
lem-weil-isomorphism-comparison-scalar-extension vs prop-weil-pbc-scalar-extension: this supplies coherent operation/base-change comparisons in another coefficient presentation; it does not identify the explicit inverse-image-to-pullback morphism of the present definition.
lem-weil-isomorphism-comparison-scalar-extension vs lem-weil-frobenius-point-transport-natural: the new lemma asserts only compatibility of kappa for arbitrary scheme isomorphisms. It has no Frobenius, point, sections, sigma, rational morphism or common-stage coefficient category. The item's proof establishes linearity and chain/derived naturality directly and then combines two separate squares; it does not apply a renamed clause of itself.

## Why the new lemma is needed and plausible

Its statement fixes both alpha (the canonical tensor/completion comparison) and beta (conjugated by the specified chi), so the displayed equation has a definite meaning. A proof can choose one flat-term K-flat representative, use the ordinary inverse-image/tensor formula, and compare the entire zero-shifted-coordinate maps into the quotient-tower cones. For ramification index e, the relation varpi_E = unit times varpi_L^e permits restriction to indices en. The existing lem-pur-compact-support-roos-cofinality statement explicitly preserves strict augmentations, commutes with finite free coefficient tensor, and respects composition. This and comparison-normalization are the relevant tools; equality after separate projections is not substituted for equality of cone maps. This is an auxiliary comparison argument with its own inputs and explicit prescribed maps, rather than a short algebraic rearrangement. Its proof is not smuggled into its statement or split further here.

## Review by N6

I read the node and definition statements with the sources above open. For step 1, the isomorphism-inverse-image statement gives the evaluation formula naturally in the sheaf and site object; the inverse-image definition specifies the constant coefficient adjoint; the comparison definition specifies the completed structure map by all finite projections. These statements justify respectively identification of the actual coprojection, preservation of constant coefficients, and the integral coordinate argument. The module action then gives the displayed linearity. This uses the scheme isomorphism g_s, not a generic morphism for the completed structure map.

For step 2, the inverse-image definition gives the colimit action on maps; the sections-exact theorem explicitly preserves quasi-isomorphisms on complexes; the comparison definition explicitly asserts exactness of the module inverse image including completed coefficients; the abstract-derived-category statement defines localization of complexes. I wrote out naturality for a chain map and the cancellation for a formally inverted quasi-isomorphism. This handles all unbounded complexes in clause (1), rather than only constructible objects.

For step 3 I checked that the finite comparison definition actually specifies x to x tensor 1 and its sheafification. The naturality equality on tensors is written out, and Step 2 supplies the inverse-arrow calculation. For step 4 I read the WHOLE statement of comparison-normalization: it gives the specified kappa, its exact equality with the actual unit via a natural theta, and naturality for derived morphisms. The written equality follows by substitution; it does not assume functorial K-flat choices or uniqueness of a map into a derived limit. The required scheme isomorphism and invertibility of ell hold because g_s is induced by a field automorphism in characteristic p with ell distinct from p.

For step 5 I checked that isomorphism-derived-pullback really preserves the full constructible subcategory for BOTH finite and completed integral coefficients. The point-fiber definition really is sections at these stages, and the point-transport definition really composes Gamma(kappa) with sigma. Their combination gives the written naturality equation by composition. For step 6 I read the raw rationalization morphism formula, the fiber formula on morphisms and the rational operations formula; none takes a Karoubi envelope. Finite sums of pure tensors span the localized morphism group, so tensoring, scaling and adding the integral equality proves it for every rational morphism. No denominator-clearing assertion without an argument is used.

For step 7 I checked the sections-scalar-extension statement specifies phi as the inverse of Gamma(chi) after sections-tensor. The finite-free-completed comparison states finite freeness and specifies chi, and the existing isomorphism-pullback statement ensures that G K remains constructible/complete. The new lemma defines beta from those exact chi maps and the pure-tensor inverse-image isomorphism. Restriction fixes b and both tensor paths send x tensor b to ins(x restricted to V) tensor b; linearity and tensor relations give equality, then derived naturality from step 2 moves sigma through chi. I corrected the draft here to make this last use explicit, rather than saying that completion commutes without explanation.

For step 8 I checked the operations-scalar-extension statement really supplies alpha naturally and coherently, and that the new lemma states EXACTLY alpha T(kappa) = kappa beta, with the same domains and coefficient actions. Naturality of phi is in its cited statement. The text writes the substitution and order of composition that give the integral equation; tensoring with L gives the rational comparison in the item's original statement. For step 9 I read the common-stage morphism-colimit definition and the point functor's conjugation formula; they permit representing any morphism over a common finite field, applying step 6 there, and using step 8 to identify the components. This also proves representative independence after a further extension.

For the new lemma I checked all objects are introduced, completed coefficients are not replaced by discrete constant integral coefficients, and g is an isomorphism. I tested g = identity (kappa is the actual completion unit), L = E (chi is that same unit under multiplication), K = 0, complexes concentrated in degree zero, and a ramified extension (requires en, not the same uniformizer index). All have the predicted canonical identities; no assertion is made for arbitrary non-complete K. For the item I also checked zero maps/complexes, shifted complexes, finite n = 1, arbitrary derived inverses, sums of rational morphisms, and objects initially defined over different finite coefficient fields. These do not require any extra hypothesis.

I checked B-E: one self-contained statement-only new node; no hollow definition or new Lean; all actual searches retained; no source theorem overstated; no node cites a proof in place of a statement; no clause moved intact to a child; all local calculations and scalar/common-stage transitions are written. citations.json has a literal relevant statement excerpt for every use. A read-only dependency traversal found no path from the external comparison tools back to the item. Every proof step is below 2000 characters, so no long step hides a separate comparison lemma. The one substantive new comparison is the explicit unsplit node. No compiler, Lake, local preflight/check_dag/review_split, live git command, or write outside this sandbox was used.

## Dry-run repairs

The first server dry run rejected the phrase “the item's statement” in step 8 as context-dependent (B2). Replaced it with the named sections/scalar-extension and pullback/scalar-extension comparisons already displayed in the node. I also expanded step 1 to identify the terminal colimit index explicitly, so the evaluation comparison is normalized by the specified coprojection rather than an arbitrary natural isomorphism. No statement or dependency changed.

## Previous stage-2 report retained for provenance (no stage-2 work in this delivery)

## Worker report

This repair updates `Sheaf.SixFunctors.FrobeniusPointTransportNatural`.  The main
statement remains the node statement, with its finite and integral models made
explicit.  Three helper theorem declarations record the canonical object equalities
needed to write the rational and common-stage qbar squares:
`frobeniusPointRationalPullbackEq`, `frobeniusPointQbarPullbackEq`, and
`frobeniusPointQbarFibreObjEq`.  They are obtained from the object clauses of
`rationalDerivedPullback_existsUnique`, `commonStageDerivedPullback_existsUnique`,
and `pointQbarFibre_existsUnique`; their proofs are postponed at stage 2.

The theorem binds `D`, `l`, the prime instance, `hl`, `E`, its field, algebra,
and finite-dimensional instances, and then states the following clauses.

* The finite sigma component is linear on every complex degree and every
  coefficient element.  The next conjunct gives chain-map naturality for every
  finite complex morphism.  A further conjunct applies `DerivedCategory.Q.map`
  to the same equation, making the derived-level sigma naturality explicit.
* The completed-integral sigma component is linear and natural on chain maps;
  the following `DerivedCategory.Q.map` conjunct is its derived-level form.
* Finite constructible naturality is the square with
  `frobeniusPointFinitePullback`; integral constructible naturality is the
  analogous square with `frobeniusPointIntegralPullback`.
* Rational naturality uses the canonical functor
  `rationalDerivedPullback l E (frobeniusPointIso D).hom`.  Its map is
  transported to the point-transport pullback objects on both sides by
  `eqToHom (frobeniusPointRationalPullbackEq ...)`; there is no existentially
  chosen map.
* Qbar naturality quantifies `u : A ⟶ B` in
  `generalAlgebraicallyClosedConstructibleCategory`, and uses
  `pointQbarFibre.map u` and
  `commonStageDerivedPullback ... .map u`.  The two fibre-functor object
  equalities and the common-stage/pullback object equalities are inserted by
  canonical `eqToHom` maps, so all four sides of the square have the displayed
  source and target.
* The derived sigma definitions are used in additional naturality conjuncts for every derived morphism.
* The final clause quantifies a finite coefficient extension
  `ι : E' →ₐ[ℚ_[l]] L` and states the scalar-extended transport equation after
  conjugation by `pointRationalFibreScalarIso`, the normalized
  `rationalPullbackScalarComparison`, and the rational pullback object equalities.
  The fibre comparison is the canonical normalization built from
  `pointRationalSectionsScalarExtensionIso`.

The imported dependency declarations are from
`Sheaf.SixFunctors.FrobeniusPointTransport` (the finite/integral sigma maps,
transport maps, pullback objects, and qbar objects),
`Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`,
`Sheaf.Paper.SfIntegralConstructible`, `Sheaf.Paper.SfRationalizationKaroubi`,
and `Sheaf.Paper.DerivedPullbackTensorHom` (the rational and common-stage
pullback functors).  The point-fibre declarations are
`pointFiniteFibre`, `pointIntegralFibre`, `pointRationalFibre`,
`pointQbarFibre`, and `pointQbarFibreObj` from
`Sheaf.Paper.FiniteCoefficientPoint`.

Edge cases checked were `n = 0` (the finite coefficient level is `n + 1`), zero
complexes and zero maps, identity maps, empty constructible objects, repeated
or identity coefficient inclusions, and a further scalar extension.  The
hypothesis `hl : l ≠ D.p` is retained and supplies the residue-field
`Invertible` instance used by both pullback constructions.

Searches made:

* `msearch.py ... leanfinder` for pro-etale Frobenius point-transport
  naturality: no matching declaration.
* `msearch.py ... loogle` for natural transformations, localization, and
  `sheafFiberComapIso`: only generic natural-transformation/site declarations.
* `msearch.py ... grep` and `rg` over `WeilConjectures/` and `lean/Sheaf/` for
  the item id and Frobenius transport: only the recorded transport module and
  its component definitions were found.
* `rg` for `rationalDerivedPullback`, `commonStageDerivedPullback`, and
  qbar scalar-extension declarations located the canonical interfaces in
  `Sheaf.Paper.DerivedPullbackTensorHom` and `FiniteCoefficientPoint`.

No `STATEMENT-DISPUTED` marker or node fault applies.  The theorem proof and the three helper equalities remain `sorry`, as required
for stage 2; the two derived sigma definitions have real data, by reusing the
recorded transport constructions.

## Second reading by NI

I reread the node, its source proof, every recorded dependency, and the repaired
module.  The returned issues are addressed as follows: the rational conjunct
now uses `rationalDerivedPullback` with canonical `eqToHom` object transports;
the qbar conjunct quantifies morphisms of the general algebraically closed
constructible category and uses `pointQbarFibre.map` together with
`commonStageDerivedPullback.map`; the finite and integral sigma equations are
also stated after `DerivedCategory.Q.map`; and the theorem docstring contains
nine numbered proof steps.  The previous second-reading sentence claiming
that these squares were already stated was removed and replaced by this
explicit account of the repaired equations.  The finite/integral conjuncts,
hypotheses, universes, and the `n = 0` case remain unchanged.  The file passes
`scompile.py` with no compiler errors or warnings.


## Repair details

The former heterogeneous scalar-extension equality was replaced by the typed conjugated square: source and target are transported by `pointRationalFibreScalarIso`, the pullback side by `rationalPullbackScalarComparison`, and the rational pullback object equalities. The derived finite and integral sigma components are explicit definitions (`frobeniusPointFiniteSigmaDerived` and `frobeniusPointIntegralSigmaDerived`) and the theorem states naturality for every derived morphism. The theorem proof docstring is a proper module docstring with the source, blueprint identifier, and nine postponed proof steps. The three helper equalities are theorem declarations with `sorry`, rather than proved proposition definitions.

## Maintainer review fix (cc second reader, 2026-10-18)

The two delivered "derived sigma" definitions were literal aliases of the recorded
transports `frobeniusPointTransportFinite` / `frobeniusPointTransportIntegral`. Their
target was `Γ(s, Lg_s^* N)`, i.e. `ι_N = Γ(κ_N) σ_N`, not `σ_N`. So the conjuncts using
them stated naturality of `ι` on the whole derived category. That is not the node's
clause (1) natural transformation `Γ(s,-) → Γ(s, g_s⁻¹(-))` of functors
`D(s_proet, Λ) → D(Λ)`, and it duplicated a recorded notion under a misleading name.

The fix replaces both definitions with the genuine derived `σ`. They keep the same
names, have no `hl` argument, and carry source/blueprint `/--` docstrings. Each one
conjugates the chain-level `frobeniusPointFiniteSigma` / `frobeniusPointIntegralSigma`
of `DerivedCategory.Q.objPreimage N` by the recorded `mapDerivedCategoryFactors`
isomorphisms and `Q.objObjPreimageIso N`. The target is the recorded exact module
inverse image `inverseImageFiniteDerived` / `inverseImageIntegralDerived` of
def-weil-inverse-image-pullback-comparison. The fix states the two derived conjuncts
with `(inverseImageFiniteDerived …).map f` / `(inverseImageIntegralDerived …).map f`,
for every derived morphism `f`. It also moves the nine numbered proof steps from a
detached `/-!` block into the theorem's `/--` docstring. Every other conjunct is
unchanged. The file compiles per file through nt_compile.py with no diagnostics.


## Retained repair retry, 2026-10-21

A fresh worker resumed the retained four-node repair and ran the required initial `deliver.py Q97 lem-weil-frobenius-point-transport-natural --no-push` before changing any input. The invocation was polled through exit; no second delivery invocation was started and nothing was pushed. It failed in server preflight: `Could not verify the DAG baseline: [Errno 28] No space left on device: /tmp/sheaf-dag-base-q0c3any6/dag/nodes/sec-proper-base-change/lemma-weil-pbc-etale-pullback-forget-modules.json`. This repeats the server resource failure reported by the preceding worker; it is outside the writable sandbox.

I compared the current shared item with the sandbox: only proof, proof_deps, proof_origin and split_report differ; the statement, stmt_deps and Lean record still agree. The shared DAG still contains neither added id. I reread all four new statements and the full nine-step returned-proof.json, the current definitions and all assembly citations, and checked all 13 citations.json quotes as literal substrings of the current cited statements. The preservation map still assigns every original argument to a new statement-only task, including original steps 3–5 and 6/9. The assembly remains 1809 characters, with no step above 2000 characters. The restored alpha citation remains in step 3. I reread Deligne Weil II PDF pages 15–16, the actual strict-cone normalization, the specified beta/alpha comparison, and the two closest Mathlib candidates (free-sheaf pullback naturality and localization natTransExtension). I read the genuine retained search results and reused those queries without rerunning them. No content repair or new searches were warranted. All five node files and citations.json are retained unchanged for the next retry.


## Successful retained-repair retry, 2026-10-21

The required initial dry run of the retained four-node repair completed successfully at 90c9ff4653a (`OK (not pushed)`); the earlier server disk-space failure did not recur. I compared the sandbox to the current shared item again: only proof, proof_deps, proof_origin and split_report differ. The repaired four-node content has not previously been pushed, so this is the substantive G1/D repair described above, not an unchanged re-push of the returned two-node head.

I reread all nine original arguments and all four task statements. The specified finite tensor-unit and ambient integral completion-unit naturality, including incomplete objects, are assigned to the kappa task; arbitrary rational sums and both actual common-stage conjugations are assigned to the descent task. In assembly step 2 the general composition conclusion applies with S = H = sections and rho = sigma, and the preservation statement supplies precisely the finite/integral constructible restrictions. In step 3 the accepted scalar task supplies the exact phi Gamma(alpha)-inverse square required by the descent hypothesis; both scalar comparisons are explicitly cited. In step 4 the descent conclusion covers all rational arrows and independence of equivalent common-stage representatives. Thus none of the missing return arguments remains inline. Identity g, zero transformations, shifts, n = 1, incomplete ambient N, L = E and ramified extensions introduce no extra hypothesis or invertibility claim.

I reread Deligne (1.1.3) and (1.1.7), the live strict-cone normalization, the specified beta/alpha identity and the actual phi definition. I also read the retained genuine search-log results for all four tasks; every recorded tool/query pair occurs there. All 13 assembly uses have relevant verbatim quotes in citations.json against the current statements. The assembly is still 1809 characters and its longest step is 545 characters. The item statement, statement dependencies, Lean record, blueprint and inherited approvals remain unchanged. No Lean was written or compiled.
