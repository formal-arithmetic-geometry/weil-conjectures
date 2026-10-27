# Repair of lem-trf-bounded-stage-roof-comparison — Q75, 2026-10-22

## Files written

- dag/nodes/sec-trace-formula/lem-trf-bounded-stage-roof-comparison.json: unchanged statement; four-step assembly.
- dag/nodes/sec-trace-formula/lem-trf-resolving-class-derived-descent.json: statement, unsplit; no Mathlib match. Derived descent through a bounded above resolving class.
- dag/nodes/sec-trace-formula/lem-trf-good-truncation-stage-naturality.json: statement, unsplit; no Mathlib match. Canonical good-truncation comparisons commute with stage transitions.
- dag/nodes/sec-trace-formula/lem-trf-resolving-roof-ambient-compatibility.json: statement, unsplit; no Mathlib match. Resolving roofs detect augmentation compatibility with unbounded targets.
- citations.json: every citation of each parent proof step, with verbatim statement excerpts.
- report.md: this signed repair and full retained argument.

## Attachments

None. Searched the live WeilConjectures source by blueprint id and resolving/truncation/roof concepts; no exact completed declaration. Read Sheaf/Algebra/Homology/BoundedStageRoofComparison.lean: bounded_stage_roof_comparison and bounded_stage_roof_comparison_homology both end in sorry. The former states the stronger derived form; the latter states this node on cohomology. Their existing Lean records are retained; no attachment claim is made.

## WANTED

None. All mathematical sources used are present locally.

## Returned defect and repair

The sandbox initially contained only dispatcher brief markers, no node copy, report or search log. The read-only current repository contains the returned eight-step split and its review/Lean records. Copied that current node as the baseline, preserving its statement, citations in the original argument, existing Mathlib-search records, metadata and Lean records. There was no retained sandbox work or returned-head file to overwrite or rebase. No git command was run in the repository.

The return requires at least two comparable statement-only nodes, at most 3000 characters in the parent proof, and no lost argument. This delivery introduces THREE nodes: localization/descent (old steps 1--3), coherent truncations (old steps 4--5), and resolving augmentation roofs (old steps 7--8). Old step 6 is the elementary assembly using the naturality supplied by the first node. These are different arguments: the first has no towers, the second has no F or P, and the third treats a single arbitrary augmented derived isomorphism with no towers or truncations. None states the parent assertion. All are unsplit with empty proof and proof_deps and null proof_origin. Their statements give the derived forms; the parent obtains the requested cohomology comparisons by applying H^i. The item statement and hypotheses are unchanged.

## What remains unfinished

Stage 1 only. The three new statements intentionally await independent proof splits. No Lean was written; no compiler, Lake, build or local check_dag/review_split/preflight was run. Required validation is through deliver.py on the server.

## Review by Q75

For the latest landing-return repair, see the signed current-DAG and step-by-step recheck in “Landing return L” below; the original review and argument are retained.

I read Stacks derived.tex Tag 0794, proposition-left-derived-exists, from its hypotheses and first paragraph through the entire common-roof claim and the sentence about compatibility as n varies. The claim occurs before the colimit argument: its bounded-stage part needs only additive F and preservation of quasi-isomorphisms between the supplied resolving complexes. It does not need the proposition's stronger right-exactness and sequential-colimit hypotheses, and this repair adds neither. The source's displayed arrow is inconsistent with its preceding alpha notation; the already-corrected item follows the actual augmented square, and remains unchanged.

For derived-descent I also read Tag 05RT (lemma-acyclic), Tag 05T7 (lemma-subcategory-left-resolution), and Tag 0GSL (lemma-localization-subcategory), plus Categories 04VI/04VJ (right roofs and equality). I read the existing DAG statements for multiplicative-system, fraction representation, common refinement, subcategory-left-resolution, dense-subcategory, truncation-cohomology, localization-universal-property and homotopic-maps-equal-cohomology. They supply exactly the inputs in retained steps 1--3 below: Ore/refinement sources have bounded cohomology; the truncation can be resolved using zero and epimorphic generation; the dense localization is equivalent; F descends with its natural comparison. I stated all these conclusions together as one independently assignable infrastructure argument, in derived form. The cohomological bounds are not termwise bounds until resolution; both notions are distinguished explicitly.

For stage-naturality I reread the truncated-alpha diagram and “The exact same argument” sentence in 0794, the definition of good truncation, and the existing truncation-cohomology and truncation-descends node statements. Old steps 4--5 below give the full computation. The new statement assumes only the bounds and cohomology isomorphisms actually used. In particular c_n of E_n and G_n is invertible after Q, whereas c_n of X or Y need not be. The transition identity cancels the former, never the latter. All identities are in the derived category; there is no per-degree-only substitute for a derived isomorphism.

For ambient-compatibility I read the common L/resolving R passage and the square in 0794, Categories 04VI/04VJ and 05T7. I checked the existing fraction-representation and common-refinement statements: equality for two roofs with denominator 1_V yields an actual quasi-isomorphism to V in the homotopy category. Its source still has bounded above cohomology, so it can be resolved. The new node asserts both the refined P-roof and its compatibility after ANY descended functor with the stated rho-naturality. It applies F's preservation only to the composites from the final bounded above P-complex, not to maps through arbitrary intermediate complexes. The final homotopy can have an unbounded target. Old steps 7--8 below preserve the construction and cancellation in full.

Parent step 1 cites derived-descent for its functor and natural rho, and the derived-category definition for cohomology factorization; both cited statements say exactly this. Step 2 cites stage-naturality for a_n and BOTH displayed identities, checking each bound, augmentation equation and quasi-isomorphism hypothesis against the unchanged parent. Step 3 is only conjugation and functoriality using the natural rho from derived-descent, already chosen in step 1. Step 4 cites ambient-compatibility with b=alpha e_n and c=g_n; step 2 gives its required equality and step 1 gives S,rho. Applying the derived cohomology functor then gives precisely the item's augmentation identity. citations.json quotes these conclusions verbatim rather than appealing to any cited proof.

Small-case checks: zero complexes and P={0} in the zero category; alpha=id and identical stages; negative i and i>n (F may create cohomology there, so no vanishing after F is asserted); stages with nonzero acyclic tails above n; and a genuinely unbounded target. The localization statement only needs cohomological boundedness before resolving. The truncation statement does not infer a chain isomorphism from a quasi-isomorphism. In the ambient node c and b need not be quasi-isomorphisms, so it also applies to zero augmentations. F need not be exact: tensoring with Z/2 on bounded above projective abelian-group complexes illustrates why preservation is restricted to P-models. No counterexample or statement correction was found.

I checked delivery-errors B--E against the actual JSON and sources: introduced objects and universes, definition dependencies, TeX escaping, sources by tag and label, blueprint provenance, genuine searches, no new proof sketches in statements, no duplicate or cyclic parent dependency, exact citation statements rather than their proofs, complete bounds and homotopy hypotheses, and no hidden “transport” or denominator cancellation. New nodes have no proof steps; all parent steps are below 2000 characters and the assembly is below 3000. The old longer arguments are assigned below in full for the future workers; their proofs are not claimed finished here.

## Search evidence

For EACH new node ran leanfinder, loogle, grep through the prescribed msearch.py, and a second phrasing through leansearch. All services answered successfully. Read the returned names and Mathlib source: Algebra/Homology/Localization.lean 340--409 assumes PreservesHomology; DerivedCategory/ExactFunctor.lean 30--48 assumes exactness; DerivedCategory/Fractions.lean 73--88 gives one strictly bounded roof; Embedding/CochainComplex.lean 50--88 supplies truncation and naturality. The ambient search also finds general RightFraction.map_eq_iff and injective-resolution homotopy comparisons, neither a P-resolution refinement with arbitrary target. These are supporting inputs, not one-line specializations proving the new statements. The exact query texts, returned digest records and distinct verdicts are in each node and searches.jsonl. Existing item search records are retained as inherited evidence, not represented as newly run searches.

Searched the whole DAG for 0794, bounded-above cohomology, resolving/localization/roof and truncation-stage concepts; read the candidate statements. blueprint_refs ancestor gives lem-trf-local-term-locality, and searches for 0794, resolving, bounded stage, good truncation and roof found no blueprint node stating any new claim. Inherited chapter and unit are retained; no unit/chapter files changed. New provenance names the exact 0794 supporting paragraph and old step allocation beneath the same ancestor.

## Not duplicates

- lem-trf-resolving-class-derived-descent vs def-coef-infinity-relative-cone: the existing statement is “Relative coherent limit and colimit diagrams”, on different objects and with a different conclusion; its occurrence of 0794 does not state this abelian-complex supporting argument.
- lem-trf-resolving-class-derived-descent vs lem-coef-space-presheaf-right-kan-mapping-formula: the existing statement is “Right Kan extensions of space-valued presheaves by mapping spaces”, on different objects and with a different conclusion; its occurrence of 0794 does not state this abelian-complex supporting argument.
- lem-trf-resolving-class-derived-descent vs lem-trf-continuous-cocontinuous-derived-shriek: the existing statement constructs unbounded site lower shriek and its adjunction, not this general bounded-cohomology localization/truncation/roof assertion.
- lem-trf-resolving-class-derived-descent vs lem-trf-finite-filtered-flat-resolution: the existing statement concerns filtered flat module resolutions and tensor acyclicity on a ringed site; this node is an unfiltered general abelian-category comparison input.
- lem-trf-resolving-class-derived-descent vs lem-trf-bounded-stage-roof-comparison: the parent compares all cohomology degrees of two F-image towers; this is only the separately specified supporting argument, without that tower conclusion.
- lem-trf-resolving-class-derived-descent vs lem-trf-unbounded-left-derived-criterion: the existing statement is unbounded left derivability under right exactness and exact sequential colimits, whereas this node isolates a bounded-stage proof input and assumes no colimits.
- lem-trf-resolving-class-derived-descent vs lem-per-noetherian-supported-product-calculus: the existing statement is “Supported products and Cartier interchange on ordinary etale sites”, on different objects and with a different conclusion; its occurrence of 0794 does not state this abelian-complex supporting argument.
- lem-trf-resolving-class-derived-descent vs lem-weil-pbc-finite-module-localization-zero-annihilator: the existing statement is “A finite module killed elementwise by a multiplicative set is killed by one element of it”, on different objects and with a different conclusion; its occurrence of 0794 does not state this abelian-complex supporting argument.
- lem-trf-good-truncation-stage-naturality vs def-coef-infinity-relative-cone: the existing statement is “Relative coherent limit and colimit diagrams”, on different objects and with a different conclusion; its occurrence of 0794 does not state this abelian-complex supporting argument.
- lem-trf-good-truncation-stage-naturality vs lem-coef-space-presheaf-right-kan-mapping-formula: the existing statement is “Right Kan extensions of space-valued presheaves by mapping spaces”, on different objects and with a different conclusion; its occurrence of 0794 does not state this abelian-complex supporting argument.
- lem-trf-good-truncation-stage-naturality vs lem-trf-continuous-cocontinuous-derived-shriek: the existing statement constructs unbounded site lower shriek and its adjunction, not this general bounded-cohomology localization/truncation/roof assertion.
- lem-trf-good-truncation-stage-naturality vs lem-trf-finite-filtered-flat-resolution: the existing statement concerns filtered flat module resolutions and tensor acyclicity on a ringed site; this node is an unfiltered general abelian-category comparison input.
- lem-trf-good-truncation-stage-naturality vs lem-trf-bounded-stage-roof-comparison: the parent compares all cohomology degrees of two F-image towers; this is only the separately specified supporting argument, without that tower conclusion.
- lem-trf-good-truncation-stage-naturality vs lem-trf-unbounded-left-derived-criterion: the existing statement is unbounded left derivability under right exactness and exact sequential colimits, whereas this node isolates a bounded-stage proof input and assumes no colimits.
- lem-trf-good-truncation-stage-naturality vs lem-per-noetherian-supported-product-calculus: the existing statement is “Supported products and Cartier interchange on ordinary etale sites”, on different objects and with a different conclusion; its occurrence of 0794 does not state this abelian-complex supporting argument.
- lem-trf-good-truncation-stage-naturality vs lem-weil-pbc-finite-module-localization-zero-annihilator: the existing statement is “A finite module killed elementwise by a multiplicative set is killed by one element of it”, on different objects and with a different conclusion; its occurrence of 0794 does not state this abelian-complex supporting argument.
- lem-trf-resolving-roof-ambient-compatibility vs def-coef-infinity-relative-cone: the existing statement is “Relative coherent limit and colimit diagrams”, on different objects and with a different conclusion; its occurrence of 0794 does not state this abelian-complex supporting argument.
- lem-trf-resolving-roof-ambient-compatibility vs lem-coef-space-presheaf-right-kan-mapping-formula: the existing statement is “Right Kan extensions of space-valued presheaves by mapping spaces”, on different objects and with a different conclusion; its occurrence of 0794 does not state this abelian-complex supporting argument.
- lem-trf-resolving-roof-ambient-compatibility vs lem-trf-continuous-cocontinuous-derived-shriek: the existing statement constructs unbounded site lower shriek and its adjunction, not this general bounded-cohomology localization/truncation/roof assertion.
- lem-trf-resolving-roof-ambient-compatibility vs lem-trf-finite-filtered-flat-resolution: the existing statement concerns filtered flat module resolutions and tensor acyclicity on a ringed site; this node is an unfiltered general abelian-category comparison input.
- lem-trf-resolving-roof-ambient-compatibility vs lem-trf-bounded-stage-roof-comparison: the parent compares all cohomology degrees of two F-image towers; this is only the separately specified supporting argument, without that tower conclusion.
- lem-trf-resolving-roof-ambient-compatibility vs lem-trf-unbounded-left-derived-criterion: the existing statement is unbounded left derivability under right exactness and exact sequential colimits, whereas this node isolates a bounded-stage proof input and assumes no colimits.
- lem-trf-resolving-roof-ambient-compatibility vs lem-per-noetherian-supported-product-calculus: the existing statement is “Supported products and Cartier interchange on ordinary etale sites”, on different objects and with a different conclusion; its occurrence of 0794 does not state this abelian-complex supporting argument.
- lem-trf-resolving-roof-ambient-compatibility vs lem-weil-pbc-finite-module-localization-zero-annihilator: the existing statement is “A finite module killed elementwise by a multiplicative set is killed by one element of it”, on different objects and with a different conclusion; its occurrence of 0794 does not state this abelian-complex supporting argument.

Additional concept candidates: lem-trf-right-fraction-dense-subcategory is the general dense-subcategory input, not the new bounded-cohomology restriction plus F descent; lem-kun-bounded-derived-roofs assumes bounded module representatives, not a general epimorphically generating P class or an unbounded augmentation target; lem-weil-pbc-truncation-descends provides functors and inclusion naturality, not the simultaneous t_n and a_n comparison equations; lem-sfb-ringed-equivalence-resolving-tensor-descent assumes an exact monoidal equivalence and concerns K-flat tensor descent, not an arbitrary additive F with the restricted quasi-isomorphism hypothesis. These inputs/candidates were reused or distinguished, not cloned. The three new nodes have no dependency on each other or the parent; they can be assigned in parallel.

Shared-supporting-tag candidates from the first dry run were opened and their complete statements read. The differences are:

- lem-trf-resolving-class-derived-descent vs lem-pc-right-fraction-representation: the existing node supplies a generic right roof; the new node additionally resolves roof sources in an arbitrary epimorphically generating class, controls bounded cohomology, and supplies the specified derived descent or ambient augmentation conclusion.
- lem-trf-resolving-class-derived-descent vs lem-weil-pbc-resolving-representative-whiskering: the existing node proves full faithfulness of restriction on functors of two variables, assuming a dense representative setup; the new node constructs the bounded-cohomology resolving setup or refines a particular ambient augmentation equality, and is not a two-variable whiskering theorem.
- lem-trf-resolving-class-derived-descent vs lem-weil-pbc-tensor-comparison-descent-representatives: the existing node descends a specified tensor comparison with representative tensor data; the new node assumes no tensors or tensor comparisons and instead treats bounded-cohomology descent or an ambient augmented roof.
- lem-trf-resolving-class-derived-descent vs lem-pur-descent-split-tensor-action: the existing node descends ring actions, balanced maps and retractions assuming fully faithful precomposition; the new node has no ring action or split tensor data and instead constructs resolving models and derived compatibility.
- lem-trf-resolving-class-derived-descent vs lem-pc-right-fraction-common-refinement: the existing node characterizes equality by a generic common refinement, but neither replaces its source by a bounded above P-complex nor proves the F-image compatibility or bounded-cohomology descent.
- lem-trf-resolving-class-derived-descent vs lem-weil-pbc-localization-universal-property: the existing node descends an already defined W-inverting functor; the new node constructs the bounded-cohomology resolving localization equivalence from the epimorphic generation assumptions before applying that property.
- lem-trf-resolving-class-derived-descent vs def-kun-filtered-page-localization-data: the existing node defines filtered spectral-page localization records over a commutative ring; the new node is an existence/compatibility theorem for unfiltered complexes in arbitrary abelian categories.
- lem-trf-resolving-class-derived-descent vs lem-kun-filtered-page-descent: the existing node descends normalized spectral pages of finite filtered module complexes; the new node has no filtration, spectral sequence or module-ring hypothesis and uses an arbitrary epimorphically generating object class.
- lem-trf-resolving-class-derived-descent vs lem-kun-filtered-page-stationary: the existing node supplies stationary comparisons for localized filtered spectral pages; the new node constructs resolving-class descent and has neither page indices nor a stationarity hypothesis.
- lem-trf-resolving-class-derived-descent vs lem-kun-finite-filtered-graded-comparison: the existing node shows a graded quasi-isomorphism of finite filtered module complexes is an underlying quasi-isomorphism; the new node has no filtration and constructs a resolving localization and a descended F.
- lem-trf-resolving-class-derived-descent vs lem-kun-stationary-localization-naturality: the existing node extends eventual naturality of stationary spectral-page comparisons to localized arrows; the new node has neither spectral pages nor eventual naturality, and constructs a bounded-cohomology resolving equivalence with derived F.
- lem-trf-resolving-roof-ambient-compatibility vs lem-pc-right-fraction-representation: the existing node supplies a generic right roof; the new node additionally resolves roof sources in an arbitrary epimorphically generating class, controls bounded cohomology, and supplies the specified derived descent or ambient augmentation conclusion.
- lem-trf-resolving-roof-ambient-compatibility vs lem-weil-pbc-resolving-representative-whiskering: the existing node proves full faithfulness of restriction on functors of two variables, assuming a dense representative setup; the new node constructs the bounded-cohomology resolving setup or refines a particular ambient augmentation equality, and is not a two-variable whiskering theorem.
- lem-trf-resolving-roof-ambient-compatibility vs lem-weil-pbc-tensor-comparison-descent-representatives: the existing node descends a specified tensor comparison with representative tensor data; the new node assumes no tensors or tensor comparisons and instead treats bounded-cohomology descent or an ambient augmented roof.
- lem-trf-resolving-roof-ambient-compatibility vs lem-pur-descent-split-tensor-action: the existing node descends ring actions, balanced maps and retractions assuming fully faithful precomposition; the new node has no ring action or split tensor data and instead constructs resolving models and derived compatibility.
- lem-trf-resolving-roof-ambient-compatibility vs lem-pc-right-fraction-common-refinement: the existing node characterizes equality by a generic common refinement, but neither replaces its source by a bounded above P-complex nor proves the F-image compatibility or bounded-cohomology descent.
- lem-trf-resolving-roof-ambient-compatibility vs def-pc-cycle-pullback-tower-data-stage3: the existing node defines a particular recursive pullback tower using a supplied functor T and natural transformation pi; the new node asserts existence of a resolving common roof for arbitrary given complexes, with no functorial cover T supplied.
- lem-trf-resolving-roof-ambient-compatibility vs def-tower-canonical-comparison-g3: the existing node defines a termwise comparison for that specific recursive pullback tower; the new node compares a derived isomorphism and arbitrary augmentations using a P-valued common roof.
- lem-trf-resolving-roof-ambient-compatibility vs lem-pc-cycle-pullback-tower-comparison-stage3: the existing node identifies one term of a specific recursive resolution with a pointwise pullback; the new node refines an arbitrary augmented derived isomorphism by two quasi-isomorphisms and asserts a derived F-image square.
- lem-trf-resolving-roof-ambient-compatibility vs lem-pc-cycle-pullback-tower-laws-stage3: the existing node proves differential and augmentation identities for one explicit tower; the new node proves the existence and compatibility of a common resolving roof, not the laws of that construction.
- lem-trf-resolving-roof-ambient-compatibility vs lem-pc-functorial-cycle-pullback-construction: the existing node assumes a functorial object cover T with epic pi and constructs functorial resolutions; the new node only assumes nonfunctorial epimorphic generation and refines a given augmented derived isomorphism.
- lem-trf-resolving-roof-ambient-compatibility vs lem-pc-functorial-cycle-pullback-core-stage3: the existing node constructs terms and augmentations of a functorial pullback resolution from a specified T, without a quasi-isomorphism assertion; the new node instead gives two quasi-isomorphic legs and a homotopy into an arbitrary unbounded target.


## Landing return L: current-DAG repair, 2026-10-22

The latest return is a landing/promotion refusal after reader approval: this side-project completion was not yet promoted into the live queue DAG. It is distinct from the earlier long-proof re-split order documented above. I continued the retained four node files, report, citations and searches; I did not reconstruct the work or discard the prior proof. The earlier dry run completed despite the provider interruption and left its durable receipt at eee1ed71c4d.

I compared the retained item with the current read-only DAG: statement, stmt_deps, source, chapter/unit, blueprint provenance, inherited search results, Lean and review metadata all agree; only proof, proof_deps and split_report differ, precisely the retained re-split. The three supporting node ids are still absent from the current repository. No mathematical change to those three statements is forced. deliver.py constructs this repair on the latest origin/sheaf-dag and overlays only worker-owned fields, preserving current maintainer metadata. Promotion into the live queue remains the maintainer's action, as return L explicitly says.

For this rebase I reopened def-sp-abelian, def-weil-abstract-derived-category, lem-weil-pbc-localization-universal-property and lem-weil-pbc-truncation-descends, and all three supporting statements in the sandbox. The current derived-category definition still explicitly factors every cohomology functor through Q. The localization statement still supplies a descended functor with a specified natural isomorphism; truncation-descends still preserves quasi-isomorphisms and gives natural inclusion transformations. Thus no dependency statement narrows a hypothesis used in the assembly. I also reopened truncation-cohomology and right-fraction-dense-subcategory to check the retained arguments' infrastructure. The inherited citation quotes still occur verbatim. I expanded the step-1 quote to include existence of the functor, all resolving-model comparison isomorphisms, and naturality, rather than only its last equation.

I rechecked the assembly against the actual statements: step 1 uses resolving-class-derived-descent with the exact zero/generation/additivity/preservation assumptions, and derived cohomology factorization. Step 2 uses good-truncation-stage-naturality with both augmentation identities, all degree bounds, and the quasi-isomorphism alpha. Step 3 conjugates the single descended functor's naturality and transition equation; it adds no exactness assumption. Step 4 uses resolving-roof-ambient-compatibility with b=alpha e_n, c=g_n and the same descended functor and rho. Its arbitrary unbounded target and restricted preservation assumptions match the parent exactly. Each used conclusion is in the cited statement, with verbatim evidence in citations.json.

I reread derived.tex Tag 0794 (proposition-left-derived-exists), including the conflicting alpha direction and the complete common-roof argument before colimits, and Tags 05RT/05T7. The existing correction to the alpha direction remains faithful; the parent statement stays unchanged. Bounds apply to cohomology before resolution and to terms after resolution; only final resolving-class composites are fed to F's preservation assumption. Zero augmentations, identical towers, unbounded targets, and acyclic tails do not invalidate the three supporting statements. All new nodes remain statement-only, and every parent step is under 2000 characters. The report still preserves all eight returned arguments verbatim below. Existing logged search results were reread and reused because neither the statements nor search questions changed.

The concrete changes for return L are this current-DAG comparison and signed citation review, the expanded citation evidence, and the item's updated split_report. No repository, launcher, Lean, chapter or unit file was edited. A fresh dry run and push are required after these changes.

## Rebase retry after dry-run 9897522c111

I compared all fields again against the current shared DAG after the retained split passed its initial server dry run. The main node still has the reviewed eight-step proof; the released stage-1 repair note explicitly reopens it under keep_plan, with at least two statement-only nodes and a parent assembly of at most 3000 characters. This delivery retains three separate supporting arguments and the unchanged parent statement. The baseline fields, including the existing Lean and review records, agree exactly; only proof, proof_deps and split_report differ. None of the three supporting ids is present in current main. The delivery script rebases these permitted fields on current server main; I have made no git command or write in the shared repository.

I reopened all current external dependencies of the retained nodes and original argument: abelian and derived categories, localization universal property, truncation descent and cohomology, quasi-isomorphism fractions and common refinements, class resolutions, dense-subcategory fractions, and additive homotopy invariance. Their current statements still provide exactly the inputs allocated in the eight retained steps. I reread Stacks 0794 through the entire roof claim before colimits, 05RT, 05T7 and 0GSL. In particular the resolving class is closed under finite biproducts, resolutions are termwise bounded only after truncation/resolution, and maps into an unbounded target are compared in the ambient derived category. No hypothesis or proof route changes on this rebase.

For the parent assembly, step 1 takes the descended functor and all natural comparison isomorphisms from the descent node; derived cohomology is explicitly in the definition node. Step 2 takes the displayed construction of a_n and both equations from stage-naturality; the parent supplies each vanishing bound, isomorphism through n, augmentation identity, and quasi-isomorphism alpha. Step 3 is functorial conjugation and cancellation, using the single descended functor for every stage. Step 4 applies ambient-compatibility with b=alpha e_n and c=g_n, then applies cohomology; its preservation assumption concerns only quasi-isomorphisms between bounded above P-complexes. I expanded citations.json in steps 2 and 4 to quote the comparison constructions themselves, together with their equations, so the evidence now covers the entire conclusion used.

Both existing project comparison declarations still have sorry and cannot be attached. The recorded searches were reread, including the general localization hits that require PreservesHomology and the truncation/right-fraction hits that cover only proper subarguments. Their questions and our three statements have not changed, so the genuine search records are retained. Zero and identical towers, negative cohomology degrees, acyclic stage tails, and unbounded targets still satisfy the relevant edge-case checks; no post-F vanishing or arbitrary-complex exactness is inferred. This is a signed rebase and citation repair, not a claim to perform the maintainer's separate live promotion.

## Allocation of the complete returned argument

The following is the returned proof, verbatim, for continuity of the mathematical work. Steps 1--3 belong to lem-trf-resolving-class-derived-descent, 4--5 to lem-trf-good-truncation-stage-naturality, and 7--8 to lem-trf-resolving-roof-ambient-compatibility. Step 6 is the short elementary assembly retained in the parent. In nodes 1 and 3 the assertions are stated before applying cohomology; applying Q_B instead of H^i in these same arguments works because an additive functor preserves homotopies and Q_B kills them. This is the derived-form convention, not a new exactness assumption.

### Returned step 1

Write $Q:K(\mathcal A)\to D(\mathcal A)$ for localization, and let $\mathcal C$ be the full subcategory of $K(\mathcal A)$ consisting of complexes $M$ with $H^j(M)=0$ for all sufficiently large $j$. Put $W=\operatorname{Qis}\cap\operatorname{Arrows}(\mathcal C)$. The right-fraction axioms on $K(\mathcal A)$ restrict to $\mathcal C$: in an Ore square its new source has a quasi-isomorphism to the original source, and the same is true for a right cancellation refinement, so it has bounded-above cohomology. Identities and composition are inherited. The induced functor $\mathcal C[W^{-1}]\to D(\mathcal A)$ is fully faithful: any derived arrow between its objects has a right roof whose denominator source has the cohomology of its source object, hence belongs to $\mathcal C$; and a common refinement witnessing equality of two roofs has a composite denominator which is a quasi-isomorphism to that same source object, so it too belongs to $\mathcal C$. These are respectively surjectivity and injectivity on Hom sets, by the cited representation and equality statements. We identify this localization with its full image in $D(\mathcal A)$ below; all localizations are formed in the common larger universe.

Uses: def-weil-abstract-derived-category, lem-pc-quasi-isomorphisms-multiplicative-system, lem-pc-right-fraction-representation, lem-pc-right-fraction-common-refinement.

Source: literature/stacks-project/derived.tex, Tag 05RT (lemma-acyclic), with Categories Tags 04VI (lemma-morphisms-right-localization) and 04VJ (lemma-equality-morphisms-right-localization); explicit restriction to bounded-above cohomology.

### Returned step 2

Let $\mathcal R\subset\mathcal C$ be the full subcategory of bounded above complexes whose terms belong to $\mathcal P$. Every $M\in\mathcal C$ has a quasi-isomorphism from an object of $\mathcal R$: choose $b$ with $H^j(M)=0$ for $j>b$. The canonical inclusion $c_b^M:\tau_{\le b}M\to M$ is a quasi-isomorphism by the truncation cohomology formula. Apply the bounded-above class-resolution statement to the complex $\tau_{\le b}M$, whose terms vanish above $b$, obtaining $V\to\tau_{\le b}M$ with $V^j\in\mathcal P$ and $V^j=0$ for $j>b$. Its composite with $c_b^M$ is the required quasi-isomorphism. The hypotheses of that statement are precisely that $0\in\mathcal P$ and every object is a quotient of one in $\mathcal P$. Thus the dense-subcategory fraction lemma gives an equivalence $J:\mathcal R[W_{\mathcal R}^{-1}]\xrightarrow{\sim}\mathcal C[W^{-1}]$, and $W_{\mathcal R}$ itself admits right fractions. No functorial resolution has been assumed.

Uses: lem-weil-pbc-truncation-cohomology, lem-sfb-subcategory-left-resolution, lem-trf-right-fraction-dense-subcategory.

Source: literature/stacks-project/derived.tex, Tag 05T7 (lemma-subcategory-left-resolution), part (1), and Tag 0GSL (lemma-localization-subcategory), right-fraction dense-subcategory form.

### Returned step 3

Fix $i\in\mathbf Z$. The assignments $T_i(M)=H^i(F(M))$ and $T_i(f)=H^i(F(f))$ define a functor $T_i:\mathcal R\to\mathcal B$: additivity of $F$ preserves chain homotopies and homotopic maps induce the same cohomology map. The preservation assumption on $F$ says exactly that $T_i$ inverts $W_{\mathcal R}$. The localization universal property extends $T_i$ to $\mathcal R[W_{\mathcal R}^{-1}]$; composing with an inverse of $J$ extends it to a functor $\widehat T_i:\mathcal C[W^{-1}]\to\mathcal B$. Retain the resulting natural isomorphisms $\rho_M:\widehat T_i(QM)\xrightarrow{\sim}H^i(F(M))$ for $M\in\mathcal R$. Their naturality states $\rho_N\widehat T_i(Qf)=H^i(F(f))\rho_M$ for every chain map $f:M\to N$ in $\mathcal R$. This fixes one comparison functor for all stages at once.

Uses: lem-weil-pbc-homotopic-maps-equal-cohomology, lem-weil-pbc-localization-universal-property.

Source: literature/stacks-project/derived.tex, Tag 0794 (proposition-left-derived-exists), first paragraph and bounded-stage roof comparison; Tags 014X and 0116 for homotopy invariance, Categories 04VK for descent.

### Returned step 4

For any complex $M$ write $c_n^M:\tau_{\le n}M\to M$ for the canonical inclusion. The hypotheses on $E_n$ make $c_n^{E_n}$ a quasi-isomorphism. The hypotheses on $e_n$ and the truncation cohomology formula make $\tau_{\le n}e_n$ a quasi-isomorphism as well. Consequently
$$t_n^E=Q(\tau_{\le n}e_n)\,Q(c_n^{E_n})^{-1}:QE_n\xrightarrow{\sim}Q(\tau_{\le n}X)$$
is an isomorphism in $\mathcal C[W^{-1}]$. Define $t_n^G$ in exactly the same way with $(G_n,g_n,Y)$. Also $A_n=Q(\tau_{\le n}\alpha)$ is an isomorphism, since truncation preserves quasi-isomorphisms. Set
$$a_n=(t_n^G)^{-1}A_nt_n^E:QE_n\xrightarrow{\sim}QG_n.$$
The chain identities $c_n^X(\tau_{\le n}e_n)=e_nc_n^{E_n}$ and $c_n^Y(\tau_{\le n}\alpha)=\alpha c_n^X$ follow degree by degree from the inclusions of kernels. They give, in the ambient derived category,
$$Q(g_n)a_n=Q(\alpha)Q(e_n).$$
Here $X,Y$ need not belong to $\mathcal C$; only this last equality is taken in the ambient category.

Uses: lem-weil-pbc-truncation-cohomology, lem-weil-pbc-truncation-descends, def-weil-abstract-derived-category.

Source: literature/stacks-project/derived.tex, Tag 0794, diagram of bounded stages and truncated alpha; Homology Tag 0118, section-truncations.

### Returned step 5

Let $k_n^M:\tau_{\le n}M\to\tau_{\le n+1}M$ be the canonical inclusion. In the following calculation all chain maps are understood under $Q$. Naturality of $c_{n+1}$ and of $k_n$, and $e_{n+1}u_n=e_n$, give
$$\begin{aligned}
t_{n+1}^E u_n c_n^{E_n}
&=t_{n+1}^E c_{n+1}^{E_{n+1}}(\tau_{\le n+1}u_n)k_n^{E_n}\\
&=(\tau_{\le n+1}e_n)k_n^{E_n}
=k_n^X(\tau_{\le n}e_n)
=k_n^Xt_n^Ec_n^{E_n}.
\end{aligned}$$
Cancel the isomorphism $Q(c_n^{E_n})$. Thus $t_{n+1}^E Q(u_n)=Q(k_n^X)t_n^E$. The identical calculation, substituting $(G,g,v,Y)$ for $(E,e,u,X)$, gives $t_{n+1}^GQ(v_n)=Q(k_n^Y)t_n^G$. Truncation naturality gives $A_{n+1}Q(k_n^X)=Q(k_n^Y)A_n$. Substitution in the definition of $a_n$, followed by cancellation of $t_{n+1}^G$, proves
$$a_{n+1}Q(u_n)=Q(v_n)a_n.$$
The computation takes place entirely among bounded-above-cohomology objects; equality there follows from Step 1's faithful embedding. No cancellation of $Q(c_n^X)$ or $Q(c_n^Y)$ is used.

Uses: lem-weil-pbc-truncation-descends.

Source: literature/stacks-project/derived.tex, Tag 0794, sentence “The exact same argument shows that these maps are also compatible as n varies”; explicit truncation-naturality calculation.

### Returned step 6

Define
$$\theta_n^i=\rho_{G_n}\,\widehat T_i(a_n)\,\rho_{E_n}^{-1}.$$
It is an isomorphism because $a_n$ and both $\rho$'s are isomorphisms. Apply the functor $\widehat T_i$ to the equality of Step 5 and use the naturality formula for $\rho$ from Step 3 on $u_n,v_n$. Cancelling the adjacent $\rho^{-1}\rho$ gives exactly
$$\theta_{n+1}^i H^i(F(u_n))=H^i(F(v_n))\theta_n^i.$$
This works simultaneously for all $n$ for the fixed $i$; repeat the construction for every integer $i$.

Uses: .

Source: literature/stacks-project/derived.tex, Tag 0794, compatibility of the bounded-stage cohomology comparisons; functorial algebra after the preceding construction.

### Returned step 7

To check the square with the actual maps into $X,Y$, use right fractions in $\mathcal R$ to represent $a_n$ by $E_n\xleftarrow{r}V\xrightarrow{s}G_n$, with $r$ a quasi-isomorphism and $V\in\mathcal R$. Under the equivalence of Step 2 and the embedding of Step 1, $a_n=Q(s)Q(r)^{-1}$. Since $a_n$ is invertible, $Q(s)$ is invertible; applying every derived cohomology functor shows that $s$ is a quasi-isomorphism. The ambient equality in Step 4 yields $Q(g_ns)=Q(\alpha e_nr)$. Apply the common-refinement statement to these two maps $V\to Y$, both viewed as roofs with denominator $1_V$. It produces a quasi-isomorphism $w:Z\to V$ such that $g_nsw=\alpha e_nrw$ in $K(\mathcal A)$. In particular $Z$ has bounded-above cohomology. Resolve $Z$ by Step 2 to obtain a quasi-isomorphism $h:L\to Z$ with $L\in\mathcal R$. Choose chain-map representatives. Then $g_n swh$ and $\alpha e_n rwh$ are chain-homotopic. Both $rwh:L\to E_n$ and $swh:L\to G_n$ are quasi-isomorphisms between bounded above $\mathcal P$-complexes, so their images under $F$ are quasi-isomorphisms. Notice that $w$ and $h$ individually may involve a complex outside $\mathcal R$; preservation by $F$ is invoked only for the composites.

Uses: lem-pc-right-fraction-representation, lem-pc-right-fraction-common-refinement, def-weil-abstract-derived-category.

Source: literature/stacks-project/derived.tex, Tag 0794, common roof L and resolving roof R; Categories Tags 04VI and 04VJ, applied in the full ambient homotopy category.

### Returned step 8

The roof formula and the naturality of $\rho$ give
$$\theta_n^i H^i(F(rwh))=H^i(F(swh)).$$
Apply the homotopy-invariance statement to the two homotopic composites of Step 7. Functoriality of $F$ and of cohomology gives
$$H^i(F(g_n))H^i(F(swh))=H^i(F(\alpha))H^i(F(e_n))H^i(F(rwh)).$$
Substitute the first equality and cancel the isomorphism $H^i(F(rwh))$. The result is
$$H^i(F(g_n))\theta_n^i=H^i(F(\alpha))H^i(F(e_n)),$$
as required. The proof used only the stated bounded-above preservation hypothesis; no exactness of $F$ on arbitrary complexes, right exactness, colimit, or preservation of colimits entered.

Uses: lem-weil-pbc-homotopic-maps-equal-cohomology.

Source: literature/stacks-project/derived.tex, Tag 0794, displayed square on cohomology before passage to colimits; Tags 0116 and 014X for applying F to a homotopy.

Parent assembly length after the 2026-10-23 repair: 2058 characters. New statement lengths: 1959, 1703, 1889.


## Current-DAG repair and signed review, 2026-10-23

I continued the retained sandbox, including all three supporting statements, original arguments, citations and searches. The return in coord/returns/Q75.md names head e659aece4cb and says the reader approved the mathematics but landing refused the side completion before live promotion. I compared the retained four node files with the current shared DAG without running git there: the parent differs only in proof, proof_deps and split_report, and none of the three new ids exists in current main. In particular the parent statement, statement dependencies, provenance, Lean attachments and maintainer review metadata agree. The released keep_plan repair note still requires the re-split. The required initial deliver.py dry run built this retained split against current server main and passed preflight at c63253ab920, confirming that the retained files are an admissible current-DAG overlay. The delivery tool performs the actual current-main rebase; live promotion is still L's action named in the return.

I reread every external statement dependency of the four files: def-sp-abelian, def-weil-abstract-derived-category, lem-weil-pbc-localization-universal-property and lem-weil-pbc-truncation-descends. I also reopened truncation-cohomology, quasi-isomorphisms-multiplicative-system, right-fraction-representation, right-fraction-common-refinement, subcategory-left-resolution, right-fraction-dense-subcategory and homotopic-maps-equal-cohomology for the full retained argument. No cited conclusion now loses an assumption needed here: the localization node supplies a natural comparison isomorphism, the derived definition supplies cohomology factorization, truncation preserves quasi-isomorphisms, and the resolution node supplies the same strict upper bound after truncation. I do not infer strict boundedness from cohomological boundedness before resolving.

With the new statements open, I checked parent step 1 against the descent node's functor and natural rho, with exactly the parent's zero, biproduct, epimorphic-generation and restricted preservation hypotheses. Step 2 uses the truncation node's actual a_n construction and both equations, checking all cohomological bounds and augmentation identities; arbitrary X,Y are allowed. Step 3 only conjugates that transition equation using rho-naturality. In this repair I wrote out its complete three-line computation and expanded the exact citation quote: this makes the changed proof more directly reviewable than an unchanged re-push. Step 4 uses the ambient node with b=alpha e_n, c=g_n and the same S,rho, whose hypotheses were supplied by steps 1 and 2; applying derived cohomology gives the asserted actual cohomology maps. No further non-elementary claim has been inserted. Each citation quote is a verbatim substring of the named statement, and each step cites precisely the conclusions it uses.

I reread derived.tex proposition-left-derived-exists (Tag 0794), from its first paragraph through the common-roof comparison and compatibility sentence, and lemma-subcategory-left-resolution (05T7), including its distinction between termwise and cohomological bounds. I checked lemma-localization-subcategory (0GSL) as background, without applying its pre-triangulated hypothesis to the arbitrary resolving class: the retained argument uses the explicit generic dense-subcategory fraction node instead. The existing correction to the source alpha direction remains necessary; no new statement correction was made.

I reread searches.jsonl rather than rerunning unchanged questions. Localization.lean's functor hits require global PreservesHomology; Fractions.lean's bounded roof does not put terms in P or compare augmentations; CochainComplex.lean's truncation naturality is an ingredient of the second node. Thus the logged searches still do not give a one-line Mathlib specialization of any supporting statement. Both existing Sheaf comparison declarations still have sorry, and the current WeilConjectures id/concept search found no exact completed attachment.

For B--E I checked again that the three new files are self-contained statement-only nodes, introduce their own complexes and functors, retain their blueprint places and authentic search records, and are distinct arguments rather than parent clauses. I tested zero complexes, identity alpha and identical towers, acyclic tails above n, negative degrees, zero augmentations and unbounded targets: none permits cancelling an unbounded target's truncation inclusion or asserting vanishing after F. The expanded step 3 is still elementary functorial algebra. The parent assembly has 2058 characters, every step is under 2000, and the complete original eight-step argument remains above. The only changes in this retry are the explicit assembly computation, its citation evidence, and the signed current-DAG repair metadata/report. A fresh dry run and push follow these changes.
