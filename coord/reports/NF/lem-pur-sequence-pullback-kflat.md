# Worker report: lem-pur-sequence-pullback-kflat

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-sequence-pullback-kflat.json: repaired five-step split of the unchanged statement; no exact Mathlib match.
- citations.json: verbatim statement quotations for every step/node citation, including the actual constant-section scalar action.
- report.md: this repair report.

New nodes: 0. Mathlib leaves: 0. The original searches.jsonl and inherited mathlib_searches are retained with their original provenance. returned-22c47ebcbf1 preserves the returned item, report and citations inside the sandbox as historical evidence.

## Attachments

None. The prior attachment search in lean/WeilConjectures for the blueprint id, pullbackTensorSequenceGood and IsKFlatIndependentCoefficients found no exact finished project declaration. The item's lean_candidates record refers to a sorried declaration, not a finished proof. Its recorded Sheaf/Paper/CompletedPullbackTowerRealizations.lean file is absent from this read clone. No Lean file was written and no compiler was run.

## WANTED

None. The required sources are present locally.

## What was wrong and what changed

This repairs returned delivery 22c47ebcbf1, specifically C3/C4 and E5 in its Step 2 and the dependent Step 4. The statement remains unchanged, including the absence of a flat-term assumption. The accepted Steps 1 and 3 remain unchanged.

The returned Step 2 treated the existential GeometryOrdinary package as if it identified its system right adjoint with the actual f^s_*. Its prescribed inverse-image data do not fix the direct-image scalar action, addition or transitions, so that argument did not justify its comparison theta. I removed that construction and its semilinearGeometryOrdinary citation. The replacement uses the actual direct-evaluation theorem and the invertible inverse mate v_n under the specified sequence and finite adjunctions. At finite level I identify the actual right adjoint with the pushforward of the ringed-topos module adjunction, including addition, the constant-section scalar action and restrictions, and write out the normalized left-adjoint comparison. The final step computes stalks of F_f itself through these module-linear comparisons. It never uses an unpinned system right adjoint or its horizontal transitions.

The source field now points to Stacks 0DEP with 0DEN and 0992 rather than suggesting that the assertion was only an extension of the flat-term lemma 0G7E. The latter would not cover the statement. The inherited rejected argument is retained as historical material in split_report.retained_arguments, expressly marked unverified; it is not used in the proof.

The blueprint association is unchanged: the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-def-purity-conv/def-weil-frobenius-coefficient-twists.md supplies the parent finite-reduction/scalar-extension context. This is a supporting operation lemma, not an alternative purity route. The inherited broken created.item ancestry is documented in blueprint.from and split_report; same_as remains empty after the prior whole-blueprint search.

## Searches and reuse

Before the original attempt the exact archive-listing command found no abandoned attempt. The sandbox then contained no item or search log, so the live item was copied. The retained search records include the original attempt's item and structural searches and distinguish inherited records from searches performed in that attempt. I read and reused those records in this repair; I did not rerun unchanged questions or create any new nodes.

The recorded searches cover LeanFinder, LeanSearch, Loogle and whole-Mathlib grep, with a second semantic phrasing. Hits concern ordinary sheaf pullback, ordinary flat modules or categorical flatness, not the full sequence-site K-flat assertion. Structural hits include SheafOfModules.pullbackPushforwardAdjunction and Adjunction.leftAdjointUniq; the prior source inspection found no sequence-site assertion there. The repair uses existing DAG nodes for all substantive tools. The earlier consideration of a new structural node is historical only: the returned proof's use of GeometryOrdinary was rejected and has been removed.

## Not duplicates

No new nodes were created. The actual direct-evaluation and inverse-mate theorems already exist, as do the ringed-topos module adjunction, pullback-stalk theorem, scalar extension of K-flatness and both implications of the stalk criterion. Each is cited directly rather than restated as a new obligation.

## Review by NF

I reread Stacks sites-cohomology.tex 0DEN (lemma-check-K-flat-stalks) and 0DEP (lemma-pullback-K-flat-points). Neither requires flat terms. I checked sites-modules.tex 03D7 (lemma-adjoint-pullback-pushforward-modules) for the scalar-restricted right adjoint and 05V5 (lemma-pullback-stalk) for its natural module-linear stalk formula; more-algebra.tex 06Y1 supplies arbitrary scalar extension of ordinary-module K-flatness. For the unchanged geometric input I used sites-modules.tex 03D2/03D3 and proetale.tex 0992. The inverse-mate node cites Zheng Construction 4.1 and supplies its precise varying-ring sequence theorem. No SGA source is used. There are no new nodes requiring additional source statements.

Step 1 uses the vertical-slice topology in def-coef-ringed-sequence-site and the actual geometric adjunction in def-weil-proetale-inverse-image. The levelwise adjunction restricts to sequence maps by unit/counit naturality. The statement of lem-pe-constant-left-module-inverse-image supplies the canonical constant-ring identification. Its compatibility with quotient transitions follows by equality on constant presheaf generators, so the coefficient map is the actual c_n. No quotient transition is assumed invertible or flat.

Step 2 now uses exactly what its two citations state. lem-pur-integral-comparison-sequence-direct-evaluation identifies the actual direct image after evaluation with finite direct image, by identity on sections and for the canonical coefficient map. lem-sf-sequence-module-pullback-evaluation makes the inverse mate under the actual adjunctions invertible. The product site has the stated vertical topology and sliced map, and all carriers fit the larger coefficient universe. These are module-natural isomorphisms, so their application to differentials is a chain isomorphism. No assertion about GeometryOrdinary is used.

Step 3 uses arbitrary topos points supplied for every scheme by lem-sfb-proetale-enough-points, not merely scheme geometric points. lem-pur-system-evaluation-topos supplies evaluation as geometric inverse image, and def-trf-geometric-morphism supplies composition. The conservativity proof is written out componentwise using the vertical topology: inverse level maps commute with transitions. The set-indexed family N times I stays in universe u+1. This step and Step 1 were accepted in the return and are retained.

Step 4 checks the adjunction issue that caused the return. lem-weil-pbc-ringed-topoi-module-adjunction specifies its right adjoint action through the adjunct of c_n. def-weil-proetale-inverse-image defines that adjunct to be the actual constant-section rho_n, defines the same underlying direct image and restrictions, and defines its module scalar action through rho_n. Addition and zero are inherited from the same abelian direct image. Hence this finite module right adjoint is R_n from the direct-evaluation theorem, including its operations, not just an underlying set-functor isomorphism. The displayed unit/counit formulas compare the two left adjoints to this very same right adjoint. The triangle identities and naturality prove inverse composites and the unit normalization. This is an elementary uniqueness-of-adjoint calculation from the cited adjunction; no hidden system comparison is required. The finite tensor order is identified by the usual commutative-ring tensor symmetry, and all comparisons are natural module maps.

Step 5 applies the forward clause of lem-sfb-ringed-site-kflat-stalk-criterion to the source point q^{-1}E_{Y,n}; this point need not belong to a chosen source family. The composite is a point by the cited geometric-morphism definition. The stalk of v_n inverse from Step 2 and then of the normalized finite comparison from Step 4 identify the stalk of the actual F_f^cP. lem-sfb-ringed-topos-pullback-stalk gives M tensor_A B with exactly the stalk of c_n as scalar map, naturally and compatibly with differentials. lem-pc-kflat-extension-of-scalars applies to this ring homomorphism without flatness or boundedness. Tensor symmetry changes B tensor_A M to M tensor_A B if necessary. The converse stalk criterion applies to precisely the conservative target family constructed in Step 3. Finally def-pc-kflat-complex and def-pc-tensor-complex-sheaves translate that conclusion to the specified signed direct-sum total tensor predicate. Thus no ordinary right adjoint is assumed to preserve acyclic complexes.

I checked the empty scheme, identity morphism, zero complexes, noncartesian systems with noninvertible quotient transitions and unbounded complexes. Empty target module categories are trivial, and an empty conservative family causes no failure. Identity morphisms recover the normalized adjunction comparison. No horizontal transition is inverted. A contractible complex with nonflat terms is an admissible K-flat case, and none of the new steps excludes it. No statement dispute was found.

I reopened every cited node's statement and checked that it provides the operation or theorem used. citations.json has one verbatim quotation per step/node pair; the scalar-action definition now includes its actual module paragraph. proof_deps is precisely the union of step uses. The cited tools' dependency closures avoid this item and its parent. All five steps are shorter than 2000 characters. The only assembly arguments are levelwise adjunction, comparison of two finite left adjoints to the same specified right adjoint, and componentwise conservativity; the substantive geometric, module and K-flat facts are cited. Off-unit tools are declared in split_report.tool_uses.

## What could not be finished

Nothing remains in the mathematical stage-1 split. No Lean proof completion or compilation is claimed. Required dry-run and delivery validation are performed after this report.
