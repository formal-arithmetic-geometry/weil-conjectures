# Stage-1 repair of lem-sfb-integral-quotient-direct-image-comparison

Group NB, 2026-10-22. Direct delivery, mandatory re-split of the returned 6958-character proof. The sandbox initially held only dispatcher markers: no prior split, report or search log was present. I copied the live returned node and retained its full metadata, all inherited searches and exact statement. The live Q25 report is retained as prior-report-Q25.md. No repository, launcher or Lean file was changed and no compiler was invoked.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-quotient-direct-image-comparison.json: unchanged statement, four-step assembly (1911 characters).
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-quotient-resolution-normalization.json: statement-only, status unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-internal-scalar-pullback-normalization.json: statement-only, status unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-internal-scalar-mate-projection.json: statement-only, status unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-internal-scalar-mate-transitivity.json: statement-only, status unsplit, no Mathlib match.
- citations.json: exact statement quotations for all five parent-step citations.
- searches.jsonl and search-result-*.txt: actual searches and their full returned results. The original item searches remain unchanged.
- report.md: this report, including the unabridged old arguments and their assignment below. Sandbox preparation scripts and returned-node.json are retained for resumption.

Four new statement-only nodes, zero Mathlib leaves. New nodes have no proof steps, no proof dependencies, and null proof origin. No unit record changes: this item is not the unit's key node.

## Attachments

None. The exact blueprint tag and quotient/direct-image notions were searched under lean/WeilConjectures. No complete upstream declaration states the item. The current local Sheaf.Paper.IntegralQuotientDirectImageComparison theorem has a sorry at its end. Its docstring and signature were read, including positive exponents encoded by n+1, the actual augmentation equation, tensor and pullback normalization predicates, projection equality, and quotient-level mate equation. It is retained as a statement attachment, not claimed as a finished proof. Constituent ordinary pullback and scalar comparison definitions do not prove the new normalized unbounded comparison statements.

## WANTED

None. The current blueprint, Stacks source and all already-cited tool nodes are locally available.

## Repair of the returned point

The single returned point asks to distribute all six old arguments, add at least two comparable statement-only nodes, and leave at most 3000 characters in the parent assembly. I added four arguments, rather than moving everything into a single dependency. The resolution task covers old step 1; scalar-pullback normalization covers old step 2; the projection/mate task covers old steps 3 and 4 and the conservativity portion of old step 5; transitivity covers old step 6. The remaining invocation of the existing perfect projection formula in old step 5 is the short assembly between those tasks. Their original argument sizes are respectively 1132, 1371, 2921 and 1534 characters (the third includes the already existing projection-formula invocation recorded below). None is the parent theorem: the first has no direct image, the second concerns left adjoints, the third is a general conditional characterization and does not assert every mate invertible, and the fourth concerns arbitrary scalar chains without an invertibility assertion. They can be worked on separately. This specifically implements the human's mandatory re-split rather than the earlier policy of keeping these arguments inside this single item.

The item statement, coefficient categories and all its hypotheses are unchanged. I made no statement dispute, no source correction, and used no SGA reference. Every old argument is transcribed without shortening below, so the task statements can be read with the complete existing proof material. No unfinished proof is represented as complete.

## Mathlib and blueprint searches

Every new task has six actual msearch invocations: LeanFinder in two phrasings, Loogle, LeanSearch, and two greps of the specified Mathlib subdirectories. All services answered. Every query and full result is copied verbatim into that node's mathlib_searches; verdicts are no match, never an invented unavailability or an unrun search. The internal scalar interfaces live in the project, not Mathlib.

I read the search hits: ordinary SheafOfModules.pullbackComp and pullbackIso, ordinary restriction and extension adjunctions, AdicCompletion.flat_of_isNoetherian, profinite limit comparisons and perfectoid rings, derived adjunction counits, and ModuleCat.extendScalarsComp/extendScalars_assoc. They provide ingredients. None identifies this normalized internal scalar/geometric derived square or its actual projection mate. I read Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean (ordinary adjunction and pullbackIso), Sheaf/ChangeOfRings.lean (ordinary restrictScalars), CategoryTheory/Functor/Derived/Adjunction.lean (the abstract derived adjunction), and CategoryTheory/Adjunction/Mates.lean lines 159-194. The last gives mateEquiv_vcomp at line 170, already represented by the cited mate-pasting node. It does not prove that the particular K-flat scalar/pullback square pastes to the normalized composite square. Thus the transitivity task is not a one-line specialization of formal mate pasting: it includes that derived balancing and scalar-unit comparison. AdicCompletion.flat_of_isNoetherian is a statement about ordinary modules over a ring, not the pulled-back condensed sheaf with its actual finite projections.

Whole-blueprint searches: ancestor on the item; scalar pullback, projection mate, successive scalar, scalar.*pullback.*normaliz, scalar.*mate.*projection, scalar.*mate.*compos, uniformizer.*resolution, integral.*quotient. The sole broad successive-scalar blueprint hit det-sp-unique-adjoint-coefficients concerns transport of exceptional right adjoints on constructible finite-type domains, assuming a composition identity; it does not prove the present identity. Whole-DAG keyword and tag searches were followed by opening the nearby scalar normalization, internal/section scalar-adjunction, ordinary inverse-image tower, perfect projection and integral tower statements. New ids were checked absent before writing.

## Review by NB

I read the chapter and proper-base-change unit, SETUP's fixed chapter/unit/node levels, GOAL, the stage-1 brief and delivery-errors B through E. I followed the current main-20261015 integral proof paragraphs (1) and (3): the exact uniformizer cone route and its canonical-map reduction. The additional normalized maps are agent-extracted arguments, not a claim that Stacks states the entire internal result as one theorem.

For the resolution task I read sites-modules.tex Tags 093M (lemma-completion-flat, line 8261) and 093J (lemma-constant-exact, line 8198), and the statements of the DVR, finite quotient, integral limit, completed-constant reduction and flat-scalar cyclic-resolution nodes. These provide the Noetherian domain and regular positive power, finiteness, the actual limit, and canonical augmentation after flat extension; the cyclic lemma supplies flat-term K-flatness. The new task explicitly concerns the projection pulled from the condensed quotient, so an arbitrary isomorphism of its cokernel is insufficient. The actual augmentation and internal/section identification are retained.

For the pullback task I read sites-cohomology.tex Tags 0G7E (lemma-pullback-K-flat), 0D6D (lemma-derived-pullback-composition) and 07A6 (lemma-adjoint), and opened lem-pe-internal-section-tensor-comparison, lem-pd-section-derived-pushpull-normalization and lem-sfb-internal-section-scalar-adjunction. The first identifies total tensors, flatness and K-flatness; the latter two identify the independently specified scalar and geometric adjunctions, including their units and counits. The task requires existence of the normalized comparisons, not just two isomorphic endpoints. Universal computation counits fix the maps even on arbitrary representatives; the pure-tensor formulas express their values on flat-term K-flat representatives.

For the projection task I read Tags 07A4 (lemma-pullback-tensor-product), 0D6E (lemma-derived-pushforward-composition) and the projection definition 0B56 (equation-projection-formula-map), followed by 0944 (lemma-projection-formula). I opened the exact ring-sheaf change-adjunction statement, which says the R-adjunct of V(t) composed with b inverse is d composed with V of the S-adjunct. The task separately states the balancing equation and the resulting projection equation, with their sources and targets specified. It uses the actual internal tensor arrow and includes its section-expression equality. This is the content of old steps 3 and 4; it cannot follow merely from forgetting scalar actions. Restriction reflects isomorphisms by the cited change-adjunction node, yielding the conditional invertibility test. The task imposes no hypothesis of finite type, completeness, properness, coefficient flatness or boundedness.

For transitivity I read 0D6D, 0G7E and 07A6 and the statements of successive-derived-quotient-normalization, ringed-derived-monoidal-comparisons, mate-pasting clause (1) and sheaf-ring-derived-coefficient-adjunction. The first fixes beta and its inverse and scalar units; the second supplies canonical composition coherence; the third gives the right mate of the pasted left square; and the last fixes unit x maps to x tensor 1. The new task states both the left square equality and the quotient-linear right mate equality, without assuming the transition is flat. The common source of the latter is D12,Y D01,Y F0 K and target F2 D02,X K, hence every displayed factor is in the smaller coefficient category when specialized to finite reductions.

I checked each parent step against its cited statements. Step 1 takes the actual augmented resolution, Noetherianity, finiteness and perfectness from the first new node. Step 2 takes the normalized lambda, tensor identification and adjunction transport from the second. Step 3 takes the exact projection equation and invertibility criterion from the third, and applies the existing perfect projection formula: its full statement allows arbitrary unbounded K and arbitrary f, and requires exactly the Noetherian adic ring with all finite perfect quotients verified by step 1. Step 4 specializes the fourth node to the actual composable quotient maps; its beta, mate identity and units are precisely the item's reduction compatibility. These are all the non-elementary inputs, and citations.json quotes the actual statements for all of them. proof_deps is the union of uses. The sole remaining off-unit proof tool is the existing perfect projection formula, declared in split_report.tool_uses; new nodes inherit this unit and correct blueprint ancestry.

Small cases checked: j=1 gives the actual residue-field augmentation, ramified E uses pi rather than ell, f=id gives the identity mate, K=0 and empty schemes give the unique zero-object arrows, and n=m gives the identity scalar comparisons. For n>m the residue of pi in A/pi^n is a zero divisor, so no cyclic resolution or regularity is asserted over S_n. Neither the relative mate nor scalar restriction is asserted faithful on arbitrary morphisms; only conservativity on isomorphisms is used. The projection and transitivity displays were type-checked in words by their common source and target. All parent steps are below 2000 characters and together below 3000; all extracted tasks remain unsplit.

## Not duplicates

lem-sfb-integral-quotient-resolution-normalization vs lem-sfb-integral-quotient-direct-image-comparison: the parent combines integral invertibility, resolution and tower assertions; this task isolates actual pulled-from-condensed finite quotient projections and their internal augmented two-term resolution, together with the finite perfect adic coefficient system and does not state that whole theorem.

lem-sfb-integral-quotient-resolution-normalization vs lem-sfb-ringed-finite-free-resolution-tensor: the existing node concerns tensor computation from a specified bounded-above finite free sheaf resolution; this task requires actual pulled-from-condensed finite quotient projections and their internal augmented two-term resolution, together with the finite perfect adic coefficient system, which is absent from that statement.

lem-sfb-integral-quotient-resolution-normalization vs lem-sf-integral-line-tensor-comparison-representative: the existing node concerns k-flat line tensor models and finite balancing; this task requires actual pulled-from-condensed finite quotient projections and their internal augmented two-term resolution, together with the finite perfect adic coefficient system, which is absent from that statement.

lem-sfb-integral-quotient-resolution-normalization vs lem-trf-finite-filtered-flat-resolution: the existing node concerns flat resolutions for a fixed finite filtration; this task requires actual pulled-from-condensed finite quotient projections and their internal augmented two-term resolution, together with the finite perfect adic coefficient system, which is absent from that statement.

lem-sfb-integral-quotient-resolution-normalization vs def-trf-split-flat-filtered-sheaf-models: the existing node concerns split-flat finite filtered sheaf models and their canonical comparisons; this task requires actual pulled-from-condensed finite quotient projections and their internal augmented two-term resolution, together with the finite perfect adic coefficient system, which is absent from that statement.

lem-sfb-integral-quotient-resolution-normalization vs lem-pc-bounded-above-flat-tensor-acyclic-degree: the existing node concerns fixed-degree exactness for bounded-above flat tensor complexes; this task requires actual pulled-from-condensed finite quotient projections and their internal augmented two-term resolution, together with the finite perfect adic coefficient system, which is absent from that statement.

lem-sfb-integral-quotient-resolution-normalization vs lem-sfb-flat-scalar-tor-comparison: the existing node concerns cohomology of flat scalar tensor is scalar tor; this task requires actual pulled-from-condensed finite quotient projections and their internal augmented two-term resolution, together with the finite perfect adic coefficient system, which is absent from that statement.

lem-sfb-integral-quotient-resolution-normalization vs lem-sfb-constant-field-tor-bounds: the existing node concerns tor bounds over a constant field sheaf; this task requires actual pulled-from-condensed finite quotient projections and their internal augmented two-term resolution, together with the finite perfect adic coefficient system, which is absent from that statement.

lem-sfb-integral-quotient-resolution-normalization vs lem-sfb-ringed-site-point-kflat-resolution: the existing node concerns k-flat resolution with k-flat stalk; this task requires actual pulled-from-condensed finite quotient projections and their internal augmented two-term resolution, together with the finite perfect adic coefficient system, which is absent from that statement.

lem-sfb-integral-quotient-resolution-normalization vs lem-sfb-flat-scalar-cyclic-resolution: the existing node concerns two-term scalar quotient resolutions after flat sheaf extension; this task requires actual pulled-from-condensed finite quotient projections and their internal augmented two-term resolution, together with the finite perfect adic coefficient system, which is absent from that statement.

lem-sfb-integral-quotient-resolution-normalization vs lem-sfb-flat-scalar-tensor-units: the existing node concerns degree-zero ring sheaf is a unit for the recorded derived tensor; this task requires actual pulled-from-condensed finite quotient projections and their internal augmented two-term resolution, together with the finite perfect adic coefficient system, which is absent from that statement.

lem-sfb-integral-quotient-resolution-normalization vs lem-sfb-finite-flat-constructible-total-tensor: the existing node concerns bounded flat constructible total tensor on the etale site; this task requires actual pulled-from-condensed finite quotient projections and their internal augmented two-term resolution, together with the finite perfect adic coefficient system, which is absent from that statement.

lem-sfb-internal-scalar-pullback-normalization vs lem-sbc-derived-restriction-zero-transport: the existing node concerns restriction triangle and coefficient transport in degree zero; this task requires existence and section-compatible normalization of internal scalar/geometric derived pullback and scalar-tensor comparisons for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-pullback-normalization vs lem-sbc-restricted-derived-section-zero-comparison: the existing node concerns zeroth comparison for restricted derived section pullback; this task requires existence and section-compatible normalization of internal scalar/geometric derived pullback and scalar-tensor comparisons for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-pullback-normalization vs lem-sbc-derived-section-pullback-zero: the existing node concerns degree-zero derived section pullback before restriction coherence; this task requires existence and section-compatible normalization of internal scalar/geometric derived pullback and scalar-tensor comparisons for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-pullback-normalization vs lem-sbc-derived-section-single-unit: the existing node concerns derived section pullback intertwines the two single-object units; this task requires existence and section-compatible normalization of internal scalar/geometric derived pullback and scalar-tensor comparisons for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-pullback-normalization vs lem-sbc-restricted-derived-section-shift-comparison: the existing node concerns shifted single comparison for restricted derived section pullback; this task requires existence and section-compatible normalization of internal scalar/geometric derived pullback and scalar-tensor comparisons for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-pullback-normalization vs lem-sbc-restricted-derived-sections-single: the existing node concerns single comparison for restricted derived sections before homology; this task requires existence and section-compatible normalization of internal scalar/geometric derived pullback and scalar-tensor comparisons for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-pullback-normalization vs lem-sbc-restricted-derived-evaluation-pullback: the existing node concerns the restricted derived section square for arbitrary source sheaves; this task requires existence and section-compatible normalization of internal scalar/geometric derived pullback and scalar-tensor comparisons for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-pullback-normalization vs lem-sbc-restricted-derived-sections-shift-transport: the existing node concerns transport of restricted section pullback through the shift comparison; this task requires existence and section-compatible normalization of internal scalar/geometric derived pullback and scalar-tensor comparisons for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-pullback-normalization vs lem-coef-enriched-sequence-projection-formula: the existing node concerns uncurried finite projections of the enriched sequence adjunction; this task requires existence and section-compatible normalization of internal scalar/geometric derived pullback and scalar-tensor comparisons for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-pullback-normalization vs lem-coef-scalar-hom-zero-compatibility: the existing node concerns degree-zero normalization of scalar internal hom; this task requires existence and section-compatible normalization of internal scalar/geometric derived pullback and scalar-tensor comparisons for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-pullback-normalization vs def-coef-compact-support-tensor-comparison: the existing node concerns universal coefficient tensor presentations and canonical compact-support coefficient map; this task requires existence and section-compatible normalization of internal scalar/geometric derived pullback and scalar-tensor comparisons for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-pullback-normalization vs def-sf-ringed-derived-adjoint-lift-data: the existing node concerns data of a normalized derived adjoint lift of a ringed-topos morphism; this task requires existence and section-compatible normalization of internal scalar/geometric derived pullback and scalar-tensor comparisons for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-mate-projection vs lem-sfb-integral-quotient-direct-image-comparison: the parent combines integral invertibility, resolution and tower assertions; this task isolates actual internal scalar/direct-image mate and projection-arrow equality, with the restricted balancing identity and a conditional invertibility test for arbitrary condensed coefficient maps and does not state that whole theorem.

lem-sfb-internal-scalar-mate-projection vs lem-pe-constructible-comparison-tensor-test-reflection: the existing node concerns reflection of a single comparison tensor test; this task requires actual internal scalar/direct-image mate and projection-arrow equality, with the restricted balancing identity and a conditional invertibility test for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-mate-projection vs def-sf-point-fibre-tensor-common-stage: the existing node concerns canonical common-stage point tensor and coefficient unit; this task requires actual internal scalar/direct-image mate and projection-arrow equality, with the restricted balancing identity and a conditional invertibility test for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-mate-projection vs lem-weil-pbc-ringed-slice-normalized-comparisons: the existing node concerns existence of normalized slice tensor, hom and koszul comparisons; this task requires actual internal scalar/direct-image mate and projection-arrow equality, with the restricted balancing identity and a conditional invertibility test for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-mate-projection vs def-sf-finite-open-tensor-operations: the existing node concerns canonical finite open tensor and pullback operations; this task requires actual internal scalar/direct-image mate and projection-arrow equality, with the restricted balancing identity and a conditional invertibility test for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-mate-projection vs lem-derived-right-exact-tensor-comparison: the existing node concerns normalized tensor comparison for a right exact strong monoidal functor; this task requires actual internal scalar/direct-image mate and projection-arrow equality, with the restricted balancing identity and a conditional invertibility test for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-mate-projection vs def-coef-semilinear-derived-calculus: the existing node concerns ordinary derived semilinear calculus interfaces; this task requires actual internal scalar/direct-image mate and projection-arrow equality, with the restricted balancing identity and a conditional invertibility test for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-mate-projection vs lem-sf-point-integral-completed-tensor-comparisons: the existing node concerns completed integral point tensor and scalar squares; this task requires actual internal scalar/direct-image mate and projection-arrow equality, with the restricted balancing identity and a conditional invertibility test for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-mate-projection vs lem-sf-completed-tensor-rational-naturality: the existing node concerns naturality and rationalization of a completed tensor comparison; this task requires actual internal scalar/direct-image mate and projection-arrow equality, with the restricted balancing identity and a conditional invertibility test for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-mate-projection vs def-coef-semilinear-geometry-derived: the existing node concerns derived geometric system operations and normalization; this task requires actual internal scalar/direct-image mate and projection-arrow equality, with the restricted balancing identity and a conditional invertibility test for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-mate-projection vs lem-sf-ringed-finite-free-tensor-complex: the existing node concerns actual scalar tensor comparison on complexes and k-flat preservation; this task requires actual internal scalar/direct-image mate and projection-arrow equality, with the restricted balancing identity and a conditional invertibility test for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-mate-projection vs def-sf-point-fibre-tensor-rational-compatibility: the existing node concerns canonical rational point tensor, unit, and scalar compatibility; this task requires actual internal scalar/direct-image mate and projection-arrow equality, with the restricted balancing identity and a conditional invertibility test for arbitrary condensed coefficient maps, which is absent from that statement.

lem-sfb-internal-scalar-mate-transitivity vs lem-sbc-derived-restriction-zero-transport: the existing node concerns restriction triangle and coefficient transport in degree zero; this task requires normalized internal derived scalar-composition square, its geometric direct-image mate equality, and composite scalar units for arbitrary condensed coefficient chains, which is absent from that statement.

lem-sfb-internal-scalar-mate-transitivity vs lem-sbc-restricted-derived-section-zero-comparison: the existing node concerns zeroth comparison for restricted derived section pullback; this task requires normalized internal derived scalar-composition square, its geometric direct-image mate equality, and composite scalar units for arbitrary condensed coefficient chains, which is absent from that statement.

lem-sfb-internal-scalar-mate-transitivity vs lem-sbc-derived-section-pullback-zero: the existing node concerns degree-zero derived section pullback before restriction coherence; this task requires normalized internal derived scalar-composition square, its geometric direct-image mate equality, and composite scalar units for arbitrary condensed coefficient chains, which is absent from that statement.

lem-sfb-internal-scalar-mate-transitivity vs lem-sbc-derived-section-single-unit: the existing node concerns derived section pullback intertwines the two single-object units; this task requires normalized internal derived scalar-composition square, its geometric direct-image mate equality, and composite scalar units for arbitrary condensed coefficient chains, which is absent from that statement.

lem-sfb-internal-scalar-mate-transitivity vs lem-sbc-restricted-derived-section-shift-comparison: the existing node concerns shifted single comparison for restricted derived section pullback; this task requires normalized internal derived scalar-composition square, its geometric direct-image mate equality, and composite scalar units for arbitrary condensed coefficient chains, which is absent from that statement.

lem-sfb-internal-scalar-mate-transitivity vs lem-sbc-restricted-derived-sections-single: the existing node concerns single comparison for restricted derived sections before homology; this task requires normalized internal derived scalar-composition square, its geometric direct-image mate equality, and composite scalar units for arbitrary condensed coefficient chains, which is absent from that statement.

lem-sfb-internal-scalar-mate-transitivity vs lem-sbc-restricted-derived-evaluation-pullback: the existing node concerns the restricted derived section square for arbitrary source sheaves; this task requires normalized internal derived scalar-composition square, its geometric direct-image mate equality, and composite scalar units for arbitrary condensed coefficient chains, which is absent from that statement.

lem-sfb-internal-scalar-mate-transitivity vs lem-sbc-restricted-derived-sections-shift-transport: the existing node concerns transport of restricted section pullback through the shift comparison; this task requires normalized internal derived scalar-composition square, its geometric direct-image mate equality, and composite scalar units for arbitrary condensed coefficient chains, which is absent from that statement.

lem-sfb-internal-scalar-mate-transitivity vs lem-coef-enriched-sequence-projection-formula: the existing node concerns uncurried finite projections of the enriched sequence adjunction; this task requires normalized internal derived scalar-composition square, its geometric direct-image mate equality, and composite scalar units for arbitrary condensed coefficient chains, which is absent from that statement.

lem-sfb-internal-scalar-mate-transitivity vs lem-coef-scalar-hom-zero-compatibility: the existing node concerns degree-zero normalization of scalar internal hom; this task requires normalized internal derived scalar-composition square, its geometric direct-image mate equality, and composite scalar units for arbitrary condensed coefficient chains, which is absent from that statement.

lem-sfb-internal-scalar-mate-transitivity vs def-coef-compact-support-tensor-comparison: the existing node concerns universal coefficient tensor presentations and canonical compact-support coefficient map; this task requires normalized internal derived scalar-composition square, its geometric direct-image mate equality, and composite scalar units for arbitrary condensed coefficient chains, which is absent from that statement.

lem-sfb-internal-scalar-mate-transitivity vs def-sf-ringed-derived-adjoint-lift-data: the existing node concerns data of a normalized derived adjoint lift of a ringed-topos morphism; this task requires normalized internal derived scalar-composition square, its geometric direct-image mate equality, and composite scalar units for arbitrary condensed coefficient chains, which is absent from that statement.

lem-sfb-integral-quotient-resolution-normalization vs lem-weil-pbc-completed-constant-sheaf-reduction: completion flatness and scalar reduction do not identify the actual pulled-back condensed map and its internal augmentation.

lem-sfb-integral-quotient-resolution-normalization vs lem-sfb-integral-ambient-tower-comparison: that statement assumes qcqs f and derived completeness for its main assertions and does not give the actual internal augmented sheaf resolution.

lem-sfb-internal-scalar-pullback-normalization vs lem-sfb-internal-section-scalar-adjunction: that statement transports scalar adjunctions on one site, and has no geometric scalar/pullback comparison.

lem-sfb-internal-scalar-pullback-normalization vs lem-pd-section-derived-tensor-normalization: that statement compares tensor for a fixed coefficient ring, not geometric pullback through a coefficient change.

lem-sfb-internal-scalar-mate-projection vs lem-fix-proetale-scalar-mate-normalization: that statement is restricted to finite constant commutative rings and section modules, excluding the integral condensed ring and normalized internal scalar interfaces.

lem-sfb-internal-scalar-mate-projection vs lem-pur-etale-scalar-mate-projection: that statement is on etale constant rings with bounded-below domain hypotheses, not arbitrary unbounded internal condensed coefficients.

lem-sfb-internal-scalar-mate-transitivity vs lem-sfb-successive-derived-quotient-normalization: that statement gives scalar composition on a single site and units, not its square with geometry and its actual direct-image mate.

lem-sfb-internal-scalar-mate-transitivity vs lem-sfb-scalar-inverse-image-tower-diagram: that statement is ordinary and termwise only, and expressly disclaims derived existence and K-flat preservation.

lem-sfb-internal-scalar-mate-transitivity vs lem-sf-scalar-pullback-composition: that statement composes geometric maps at one fixed constant-ring change, not coefficient changes at one geometric map.

lem-sfb-internal-scalar-mate-transitivity vs det-sp-unique-adjoint-coefficients: that statement assumes the coefficient mate composition identity and transports it to another right adjoint, on a restricted constructible domain.

lem-sfb-integral-quotient-resolution-normalization vs lem-weil-pbc-completed-adic-koszul-kflat: the existing node supplies k-flatness of the actual completed exterior koszul complexes; the new task requires identification of the actual pulled-back condensed finite projection with its quotient and internal augmented resolution, plus Noetherianity and all finite perfect scalar quotients.

lem-sfb-integral-quotient-resolution-normalization vs lem-weil-pbc-independent-bounded-flat-kflat: the existing node supplies bounded-above flat complexes are k-flat at independent universes; the new task requires identification of the actual pulled-back condensed finite projection with its quotient and internal augmented resolution, plus Noetherianity and all finite perfect scalar quotients.

lem-sfb-integral-quotient-resolution-normalization vs lem-weil-pbc-site-tensor-local-model-comparison: the existing node supplies tensor cohomology comparison from models of good truncations; the new task requires identification of the actual pulled-back condensed finite projection with its quotient and internal augmented resolution, plus Noetherianity and all finite perfect scalar quotients.

lem-sfb-integral-quotient-resolution-normalization vs lem-weil-pbc-split-perfect-tensor-kinjective: the existing node supplies tensoring k-injectives with bounded split-projective complexes; the new task requires identification of the actual pulled-back condensed finite projection with its quotient and internal augmented resolution, plus Noetherianity and all finite perfect scalar quotients.

lem-sfb-integral-quotient-resolution-normalization vs lem-sfb-finite-free-mono-cokernel-kflat: the existing node supplies finite free sheaf monomorphisms give normalized k-flat cokernel resolutions for an already supplied monomorphism and its cokernel; it does not prove that the actual condensed quotient is that cokernel or finite; the new task requires identification of the actual pulled-back condensed finite projection with its quotient and internal augmented resolution, plus Noetherianity and all finite perfect scalar quotients.

lem-sfb-integral-quotient-resolution-normalization vs lem-sfb-flat-scalar-tensor-resolution: the existing node supplies scalar tensor resolutions compute the recorded sheaf derived tensor; the new task requires identification of the actual pulled-back condensed finite projection with its quotient and internal augmented resolution, plus Noetherianity and all finite perfect scalar quotients.

lem-sfb-internal-scalar-mate-projection vs def-pd-section-derived-realization: the existing node supplies canonical derived section-module realization as data or a specified construction, not this existence/coherence assertion; the new task requires restriction of the actual internal scalar/direct-image mate equal to the specified projection arrow, including its balancing identity.

lem-sfb-internal-scalar-mate-projection vs def-pd-section-derived-tensor-data: the existing node supplies canonical derived section-module tensor data as data or a specified construction, not this existence/coherence assertion; the new task requires restriction of the actual internal scalar/direct-image mate equal to the specified projection arrow, including its balancing identity.

lem-sfb-internal-scalar-mate-projection vs lem-pd-module-ringed-topos-derived-comparison: the existing node supplies module-object and ringed-topos derived tensor comparison for separated finite-type schemes over a field of characteristic different from ell, and one coefficient ring; the new task requires restriction of the actual internal scalar/direct-image mate equal to the specified projection arrow, including its balancing identity.

lem-sfb-internal-scalar-mate-projection vs lem-pd-section-derived-tensor-normalization: the existing node supplies derived tensor and actual pullback tensor arrows under section equivalence for a single coefficient ring rather than across a scalar change; the new task requires restriction of the actual internal scalar/direct-image mate equal to the specified projection arrow, including its balancing identity.

lem-sfb-internal-scalar-mate-projection vs def-weil-pbc-normalized-origin-scalar-comparisons: the existing node supplies canonical quotient scalar-extension unit and associator as data or a specified construction, not this existence/coherence assertion; the new task requires restriction of the actual internal scalar/direct-image mate equal to the specified projection arrow, including its balancing identity.

lem-sfb-internal-scalar-mate-projection vs def-weil-pbc-ringed-projection-restriction-data: the existing node supplies normalized ringed projection and slice comparison data as data or a specified construction, not this existence/coherence assertion; the new task requires restriction of the actual internal scalar/direct-image mate equal to the specified projection arrow, including its balancing identity.

lem-sfb-internal-scalar-mate-projection vs def-weil-pbc-ringed-tensor-square-presentation: the existing node supplies representative presentation of a commutative ringed tensor square as data or a specified construction, not this existence/coherence assertion; the new task requires restriction of the actual internal scalar/direct-image mate equal to the specified projection arrow, including its balancing identity.

lem-sfb-internal-scalar-mate-projection vs lem-weil-pbc-augmented-cech-tensor-pullback: the existing node supplies augmented cech tensor actions commute with derived inverse image; the new task requires restriction of the actual internal scalar/direct-image mate equal to the specified projection arrow, including its balancing identity.

lem-sfb-internal-scalar-mate-projection vs lem-weil-pbc-augmented-diagram-projection-mate: the existing node supplies projection mate for an augmented coefficient diagram before taking inverse limit; the new task requires restriction of the actual internal scalar/direct-image mate equal to the specified projection arrow, including its balancing identity.

lem-sfb-internal-scalar-mate-projection vs lem-weil-pbc-cochain-pullback-tensor-shift: the existing node supplies the prescribed cochain pullback tensor comparison commutes with both signed shifts; the new task requires restriction of the actual internal scalar/direct-image mate equal to the specified projection arrow, including its balancing identity.

lem-sfb-internal-scalar-mate-transitivity vs def-pd-section-derived-realization: the existing node supplies canonical derived section-module realization as data or a specified construction, not this existence/coherence assertion; the new task requires the derived geometric pullback square for two scalar changes and its actual direct-image mate composition identity.

lem-sfb-internal-scalar-mate-transitivity vs def-pd-section-derived-tensor-data: the existing node supplies canonical derived section-module tensor data as data or a specified construction, not this existence/coherence assertion; the new task requires the derived geometric pullback square for two scalar changes and its actual direct-image mate composition identity.

lem-sfb-internal-scalar-mate-transitivity vs lem-pd-module-ringed-topos-derived-comparison: the existing node supplies module-object and ringed-topos derived tensor comparison for separated finite-type schemes over a field of characteristic different from ell, and one coefficient ring; the new task requires the derived geometric pullback square for two scalar changes and its actual direct-image mate composition identity.

lem-sfb-internal-scalar-mate-transitivity vs lem-pd-section-derived-pushpull-normalization: the existing node supplies section equivalence and canonical derived push-pull adjunctions for a single coefficient ring rather than a two-coefficient scalar square; the new task requires the derived geometric pullback square for two scalar changes and its actual direct-image mate composition identity.

lem-sfb-internal-scalar-mate-transitivity vs def-pbc-successive-derived-scalar-normalization-data: the existing node supplies normalized presentation data for successive derived scalar extensions as data or a specified construction, not this existence/coherence assertion; the new task requires the derived geometric pullback square for two scalar changes and its actual direct-image mate composition identity.

lem-sfb-internal-scalar-mate-transitivity vs def-weil-pbc-derived-direct-image-composition: the existing node supplies composition isomorphisms of derived direct images (conjugates of those of inverse images) as data or a specified construction, not this existence/coherence assertion; the new task requires the derived geometric pullback square for two scalar changes and its actual direct-image mate composition identity.

lem-sfb-internal-scalar-mate-transitivity vs def-weil-pbc-derived-normalization-arrows: the existing node supplies canonical derived coefficient normalization arrows as data or a specified construction, not this existence/coherence assertion; the new task requires the derived geometric pullback square for two scalar changes and its actual direct-image mate composition identity.

lem-sfb-internal-scalar-mate-transitivity vs def-weil-pbc-ringed-slice-derived-data: the existing node supplies derived slice adjunction presentations and coherence squares as data or a specified construction, not this existence/coherence assertion; the new task requires the derived geometric pullback square for two scalar changes and its actual direct-image mate composition identity.

lem-sfb-internal-scalar-mate-transitivity vs def-weil-pbc-successive-derived-quotient-data: the existing node supplies normalized presentations of derived coefficient extension as data or a specified construction, not this existence/coherence assertion; the new task requires the derived geometric pullback square for two scalar changes and its actual direct-image mate composition identity.

lem-sfb-internal-scalar-mate-transitivity vs lem-pbc-normalized-derived-adjunction-transport: the existing node supplies transport of a normalized left derived adjunction through exact equivalences between supplied equivalent adjunctions, without constructing the geometric scalar comparison; the new task requires the derived geometric pullback square for two scalar changes and its actual direct-image mate composition identity.

lem-sfb-internal-scalar-mate-transitivity vs lem-weil-pbc-cohomology-pullback-derived-unit: the existing node supplies the cohomology pullback is induced by the unit of the derived adjunction; the new task requires the derived geometric pullback square for two scalar changes and its actual direct-image mate composition identity.

lem-sfb-internal-scalar-mate-transitivity vs lem-weil-pbc-derived-adjunction-shift: the existing node supplies canonical derived ringed-topos adjunction is shift-compatible; the new task requires the derived geometric pullback square for two scalar changes and its actual direct-image mate composition identity.

lem-sfb-internal-scalar-pullback-normalization vs def-pd-section-derived-realization: the existing node supplies canonical derived section-module realization as data or a specified construction, not this existence/coherence assertion; the new task requires existence of the normalized internal scalar/geometric pullback isomorphism for a coefficient change, and its scalar-tensor identification.

lem-sfb-internal-scalar-pullback-normalization vs def-pd-section-derived-tensor-data: the existing node supplies canonical derived section-module tensor data as data or a specified construction, not this existence/coherence assertion; the new task requires existence of the normalized internal scalar/geometric pullback isomorphism for a coefficient change, and its scalar-tensor identification.

lem-sfb-internal-scalar-pullback-normalization vs lem-pd-module-ringed-topos-derived-comparison: the existing node supplies module-object and ringed-topos derived tensor comparison for separated finite-type schemes over a field of characteristic different from ell, and one coefficient ring; the new task requires existence of the normalized internal scalar/geometric pullback isomorphism for a coefficient change, and its scalar-tensor identification.

lem-sfb-internal-scalar-pullback-normalization vs lem-pd-section-derived-pushpull-normalization: the existing node supplies section equivalence and canonical derived push-pull adjunctions for a single coefficient ring rather than a two-coefficient scalar square; the new task requires existence of the normalized internal scalar/geometric pullback isomorphism for a coefficient change, and its scalar-tensor identification.

lem-sfb-internal-scalar-pullback-normalization vs def-pbc-successive-derived-scalar-normalization-data: the existing node supplies normalized presentation data for successive derived scalar extensions as data or a specified construction, not this existence/coherence assertion; the new task requires existence of the normalized internal scalar/geometric pullback isomorphism for a coefficient change, and its scalar-tensor identification.

lem-sfb-internal-scalar-pullback-normalization vs def-weil-pbc-derived-direct-image-composition: the existing node supplies composition isomorphisms of derived direct images (conjugates of those of inverse images) as data or a specified construction, not this existence/coherence assertion; the new task requires existence of the normalized internal scalar/geometric pullback isomorphism for a coefficient change, and its scalar-tensor identification.

lem-sfb-internal-scalar-pullback-normalization vs def-weil-pbc-derived-normalization-arrows: the existing node supplies canonical derived coefficient normalization arrows as data or a specified construction, not this existence/coherence assertion; the new task requires existence of the normalized internal scalar/geometric pullback isomorphism for a coefficient change, and its scalar-tensor identification.

lem-sfb-internal-scalar-pullback-normalization vs def-weil-pbc-ringed-slice-derived-data: the existing node supplies derived slice adjunction presentations and coherence squares as data or a specified construction, not this existence/coherence assertion; the new task requires existence of the normalized internal scalar/geometric pullback isomorphism for a coefficient change, and its scalar-tensor identification.

lem-sfb-internal-scalar-pullback-normalization vs def-weil-pbc-successive-derived-quotient-data: the existing node supplies normalized presentations of derived coefficient extension as data or a specified construction, not this existence/coherence assertion; the new task requires existence of the normalized internal scalar/geometric pullback isomorphism for a coefficient change, and its scalar-tensor identification.

lem-sfb-internal-scalar-pullback-normalization vs lem-pbc-normalized-derived-adjunction-transport: the existing node supplies transport of a normalized left derived adjunction through exact equivalences between supplied equivalent adjunctions, without constructing the geometric scalar comparison; the new task requires existence of the normalized internal scalar/geometric pullback isomorphism for a coefficient change, and its scalar-tensor identification.

lem-sfb-internal-scalar-pullback-normalization vs lem-weil-pbc-cohomology-pullback-derived-unit: the existing node supplies the cohomology pullback is induced by the unit of the derived adjunction; the new task requires existence of the normalized internal scalar/geometric pullback isomorphism for a coefficient change, and its scalar-tensor identification.

lem-sfb-internal-scalar-pullback-normalization vs lem-weil-pbc-derived-adjunction-shift: the existing node supplies canonical derived ringed-topos adjunction is shift-compatible; the new task requires existence of the normalized internal scalar/geometric pullback isomorphism for a coefficient change, and its scalar-tensor identification.

## Preserved proof material and task assignment

The following is the exact old six-step proof text, retained as proof material for the workers of the new statement-only nodes. It is not inserted as proof steps in those nodes. The assignment is explicit so no original balancing, counit, augmentation, or unit argument disappears.

### Original step 1: lem-sfb-integral-quotient-resolution-normalization

First identify the actual quotient and its resolution, for every positive integer $j$. By [lem-weil-l-adic-extension-integers-dvr], $A$ is a discrete valuation domain; in particular it is Noetherian and $\pi^j\ne0$. The two-term free $A$-complex $[A\xrightarrow{\pi^j}A]$ resolves $A/\pi^j$. The quotients are finite by [lem-weil-valued-dvr-finite-quotients]. The completed coefficient sheaf $R_T$ is the inverse limit of these constant quotients by [det-prop-sfb-qlbar-colimit-x-integral-limit]. Apply [lem-weil-pbc-completed-constant-sheaf-reduction] with $I=(\pi)$: $R_T$ is flat over the constant sheaf $\underline A$, and scalar extension of that finite free resolution is augmented to $S_{j,T}$ by the canonical finite projection. Consequently $R_T/\pi^jR_T\cong S_{j,T}$ with that projection, rather than an arbitrarily chosen quotient isomorphism. Apply [lem-sfb-flat-scalar-cyclic-resolution] with $a=\pi^j$: multiplication is injective and $[R_T\xrightarrow{\pi^j}R_T]$, in degrees $-1,0$, is a K-flat resolution of $S_{j,T}$. This proves the resolution assertion and supplies perfect coefficient complexes at every level.

Original cited nodes: lem-weil-l-adic-extension-integers-dvr, lem-weil-valued-dvr-finite-quotients, det-prop-sfb-qlbar-colimit-x-integral-limit, lem-weil-pbc-completed-constant-sheaf-reduction, lem-sfb-flat-scalar-cyclic-resolution.

### Original step 2: lem-sfb-internal-scalar-pullback-normalization

Work temporarily with section-ring module sheaves. The exact equivalences of [lem-pe-internal-section-tensor-comparison] identify the internal relative tensors, total tensor complexes and K-flat representatives with their section-module versions. Thus they also identify derived scalar extension: on a flat-term K-flat representative $P$, both are the complex $P\otimes_{R_T}S_{j,T}$, by [lem-pur-derived-change-of-rings]. The unbounded functor and adjunction comparisons of [lem-pd-section-derived-pushpull-normalization] identify the specified internal $L_f\dashv F_f$, including their counits, with the ringed-topos ones. Apply this separately to the integral condensed coefficient ring and the discrete finite quotient. Both coefficient identifications are cartesian by [sk-prop-sfb-cartesian-coefficients], and they commute with the finite projection, since all maps are pulled back from the point. Apply the normalized derived pullback composition comparisons of [lem-sfb-ringed-derived-monoidal-comparisons] to the two paths from $(X,S_{j,X})$ to $(Y,R_Y)$, through $(Y,S_{j,Y})$ and through $(X,R_X)$. They give $\lambda_{f,j}:L_{f,S_j}D_{j,Y}\cong D_{j,X}L_{f,R}$. Its flat-term formula is exactly the balancing map in the statement. These comparisons and the counit are natural, so taking their adjunct defines the specified natural transformation $\rho_{f,j}$.

Original cited nodes: lem-pe-internal-section-tensor-comparison, lem-pur-derived-change-of-rings, lem-pd-section-derived-pushpull-normalization, sk-prop-sfb-cartesian-coefficients, lem-sfb-ringed-derived-monoidal-comparisons.

### Original step 3: lem-sfb-internal-scalar-mate-projection

Record the balancing identity needed to identify the map, not merely its endpoints. Suppress $j$ and set $M=F_{f,R}K$. Write $b:V_XL_{f,S}\cong L_{f,R}V_Y$ for the comparison of [lem-weil-pbc-ring-sheaf-change-adjunction]. Under $V_TD_TN=N\otimes^L_{R_T}S_T$, the composite
$$L_{f,R}(M\otimes^L S_Y)\xrightarrow{b^{-1}}V_XL_{f,S}D_YM\xrightarrow{V_X\lambda_{f,M}}V_XD_XL_{f,R}M$$
is the canonical tensor comparison $L_{f,R}(M\otimes^LS_Y)\to L_{f,R}M\otimes^LS_X$. Indeed the first arrow regards inverse image of the scalar-extended module as an $S_X$-module; the second sends the inverse image of $x\otimes s$ to $f^{-1}x\otimes f^{-1}s$. This is precisely the pullback-tensor map, with $L_{f,R}S_Y\cong S_X$ from step 1 and the cartesian coefficient identification. The K-flat computation and coherence in [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] and [lem-sfb-ringed-derived-monoidal-comparisons] make this equality valid in the unbounded derived category, independently of representatives. The internal/section comparison used in step 2 preserves these same pure-tensor maps.

Original cited nodes: lem-weil-pbc-ring-sheaf-change-adjunction, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-sfb-ringed-derived-monoidal-comparisons.

### Original step 4: lem-sfb-internal-scalar-mate-projection

Now apply the adjunction-compatibility clause of [lem-weil-pbc-ring-sheaf-change-adjunction] to $t=D_X(\varepsilon^R_{f,K})\lambda_{f,M}$, whose $S$-adjunct is $\rho_{f,j,K}$. It says that the $R$-adjunct of
$$V_X(t)\circ b^{-1}:L_{f,R}V_YD_YM\longrightarrow V_XD_XK$$
is exactly $d_f\circ V_Y\rho_{f,j,K}$. By step 3 and the K-flat description of derived scalar extension, this first morphism is
$$L_{f,R}(M\otimes^LS_Y)\longrightarrow L_{f,R}M\otimes^LS_X\xrightarrow{\varepsilon^R_{f,K}\otimes1}K\otimes^LS_X.$$
The definition [def-weil-pbc-projection-formula-map] identifies its adjunct with the specified projection morphism $\pi_{f,K,S_Y}$. Uniqueness in the adjunction therefore gives $d_f V_Y\rho_{f,j,K}=\pi_{f,K,S_Y}$. All identifications are the internal/section and tensor identifications already fixed in steps 2 and 3. In particular this equality uses compatibility of the independently specified adjunctions; it does not infer equality of quotient-linear morphisms from equality after forgetting scalars.

Original cited nodes: lem-weil-pbc-ring-sheaf-change-adjunction, def-weil-pbc-projection-formula-map, lem-pur-derived-change-of-rings.

### Original step 5: lem-sfb-internal-scalar-mate-projection (conditional invertibility) and parent step 3 (application of the existing perfect projection formula)

Apply [lemma-weil-pbc-perfect-projection-formula] to $(A,I)=(\mathcal O_E,(\pi))$. Its hypotheses hold: $A$ is commutative Noetherian, all $A/\pi^j$ are finite (hence additively torsion), and all are perfect over $A$ by the two-term free resolutions of step 1. Its completed coefficient sheaves are exactly $R_X,R_Y$, and its finite quotient sheaves are $S_{j,X},S_{j,Y}$. It asserts that the precise $\pi_{f,K,S_{j,Y}}$ of step 4 is invertible for every $K$ in the ordinary unbounded category. Since $d_f$ is an isomorphism, step 4 makes $V_Y\rho_{f,j,K}$ invertible. Restriction reflects isomorphisms by [lem-weil-pbc-ring-sheaf-change-adjunction]; hence $\rho_{f,j,K}$ is invertible in $D(S_{j,Y})$. This proves the claimed natural isomorphism without any condition on $f$ or on the cohomological range of $K$.

Original cited nodes: lemma-weil-pbc-perfect-projection-formula, lem-weil-pbc-ring-sheaf-change-adjunction.

### Original step 6: lem-sfb-internal-scalar-mate-transitivity

Finally fix $n\geq m\geq1$, put $E_T=-\otimes^L_{S_{n,T}}S_{m,T}$, and write $\beta_T:E_TD_{n,T}\cong D_{m,T}$. Use exactly [lem-sfb-successive-derived-quotient-normalization]: on representatives $\beta_T$ sends $(x\otimes s)\otimes t$ to $x\otimes\bar s t$ and identifies the composite scalar units with the unit for $R_T\to S_{m,T}$. Let $\lambda^{n,m}:L_{f,S_m}E_Y\cong E_XL_{f,S_n}$ be the pullback balancing comparison and let $\sigma:E_YF_{f,S_n}\to F_{f,S_m}E_X$ be its mate. The normalized composition coherence of [lem-sfb-ringed-derived-monoidal-comparisons] identifies the pasted square $(E_X\lambda_{f,n})\circ(\lambda^{n,m}D_{n,Y})$ with $\lambda_{f,m}$ under $\beta_Y,\beta_X$: both balanced maps send the inverse image of $(x\otimes s)\otimes t$ to $f^{-1}x\otimes f^{-1}(\bar s t)$. Clause (1) of [lem-weil-pbc-mate-pasting] now gives the equality in $D(S_{m,Y})$
$$\rho_{f,m,K}\circ\beta_{Y,F_{f,R}K}=F_{f,S_m}(\beta_{X,K})\circ\sigma_{D_{n,X}K}\circ E_Y(\rho_{f,n,K}).$$
This is the required reduction compatibility retaining the quotient scalar action. The scalar-unit normalization also identifies the corresponding reduction-unit maps: take their transposes using [lem-pur-sheaf-ring-derived-coefficient-adjunction], whose unit is $x\mapsto x\otimes1$. No flatness of $S_n\to S_m$ is used. In particular the argument does not claim that $S_m$ is perfect over $S_n$ or that $\sigma$ is invertible on arbitrary inputs. For $n=m$ all balancing maps and scalar units are identities, giving the identity compatibility.

Original cited nodes: lem-sfb-successive-derived-quotient-normalization, lem-sfb-ringed-derived-monoidal-comparisons, lem-weil-pbc-mate-pasting, lem-pur-sheaf-ring-derived-coefficient-adjunction.

## Unfinished work

The four new nodes intentionally await their own stage-1 splits and later proofs, as the return instructs. The parent one-level split is complete. No Lean proof is claimed. The delivery wrapper records the server dry-run and push outcomes.
