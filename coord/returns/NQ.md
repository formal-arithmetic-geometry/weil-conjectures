
## lem-weil-integral-scalar-extension-well-defined (2026-10-14 17:39 UTC, branch head d9205b1f14)

L: approved by the reader, but the landing refused it: NOT MERGED lem-weil-integral-scalar-extension-well-defined: lem-weil-integral-scalar-extension-well-defined: no longer stage-1-open; live completion takes priority Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## thm-fin-deligne-generic-open (2026-10-14 17:42 UTC, branch head 75b92a2aa0)

L: approved by the reader, but the landing refused it: NOT MERGED thm-fin-deligne-generic-open: thm-fin-deligne-generic-open: no longer stage-1-open; live completion takes priority Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-weil-pbc-weak-etale-integral-closure (2026-10-14 18:40 UTC, branch head 0838135937)

Full reading recorded in review.md. C1/C2/D3: step 1 treats uncited valuation-separation and product weak-dimension theorems as elementary. C1/C5: step 3 omits existing lying-over, faithful-flatness and equalizer-descent citations. B3: missing definition dependencies. F2/F5: second reading describes removed nodes and a flag absent from the final delivery. More than three repairable faults; no counterexample found to the item statement.

## lem-amb-p1-diagonal-integrals (2026-10-16 04:47 UTC, branch head ab9be6405c)

L: independent stage-2 immutable head ab9be6405c4d: file-only compilation failed: preliminary Sheaf/AlgebraicGeometry/OrdinarySupportedKummer.lean
timeout after 60 s: the fault is usually a definition that is expensive to unfold, not the limit


## lem-exc-constant-tensor (2026-10-16 04:53 UTC, branch head 464b69e393)

L (re-issued by the launcher; the entry had been lost): r-datum --stage 1 --reviewer NT-Codex-NY-105cbaf87 --head 105cbaf87fa0e0da457ab58c727cd18eb70960ed --spot-checked Read the full item, unit, chapter, master source, report, all 17 dependency statements and cited sources. Verified hypotheses, coefficient stages, base-change morphisms, compact-support direction/domain, constructible exceptional adjoint distinction, edge cases, duplicate status, route, and Mathlib searches. No faults or repairs required; review.md records the checks. --verdict PASS


## prop-exc-base-change-proper (2026-10-16 04:53 UTC, branch head 54b8f26c4a)

L (re-issued by the launcher; the entry had been lost): reviewer NT-Codex-NJ-5bcfca90e --head 5bcfca90e70d99c3f86221a07d9f9a53125e94cf --spot-checked Read the full item, report, cited statements, source passages, and unit/chapter route. All six steps check, including the canonical comparison’s normalization and tower compatibility. Edge cases and duplicate/dependency searches found no gap or cycle. No new nodes, fixes, or accepted tool_uses. Detailed checks are in review.md; no target-level coefficient-category comparison is inferred. --verdict PASS

## lem-sf-unbounded-compact-support-proper-composition (2026-10-16 05:19 UTC, branch head 761cdce727)

L: approved by the reader, but the landing refused it: NOT MERGED lem-sf-unbounded-compact-support-proper-composition: coord/.merge.lock held for 120 s by pid 3899732: /usr/bin/python3 tools/merge_delivery.py Q09 def-weil-point-fg-complete-complexes --stage 1 --reviewer NT-Codex-Q09-c11642d41 --head c11642d41f89636fded4141f370039aa584bd918 --spot-checked Read the item, full report, all five dependency statements, cited source passages, and unit/chapter route. All three category conditions match the source; edge cases pass. No new nodes, cycles, missing citations, or unsupported coefficient comparisons found. Exact archived target morphisms and cat Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-asd-etale-finite-twist-pullback (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 2 (2324 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 2 (2324 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## lem-amb-unbounded-compact-support-comparisons (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 7 (2762 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 7 (2762 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.

## det-pe-finite-local-systems-type (2026-10-18 02:09 UTC, branch head 3361d77f05)

L: independent stage-2 immutable head 3361d77f0558: All clauses match node: X : Scheme.{t}; Λ with ULift coefficient lift; Λ_X = constantSheaf on ProEt.topology composed with forget₂; hF = recorded IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses with Module.FinitePresentation models, varying per member (definition read); hM/hR give exactly one representative per iso class (∃!); U : R → X.Opens with IsClopenDecomposition and IsColimit of the cofan of (U r).ι; per-r covers of ProEt.mk (U r).ι with model fixed to M r. No extra assumptions. Empty X/pieces, zero ring, infinite R, universes t/u/v all fine. Statement verbatim, docstrings with source/blueprint and 8 proof steps, sorry only, no definitions, no pro-etale substitute. nt_compile (side overlay) clean in 2.5 s, reproducible. Second-reading section is an admitted self-check (noted). FAULT (delivery-errors H2/H12, statement must rest on definitions): stmt_deps adds theorem node lem-galois-coproduct-copies-morphisms-clopen, but the Lean statement uses only the def AlgebraicGeometry.IsClopenDecomposition (CoproductCopiesMorphismsClopen.lean:31) from its module; the theorem's conclusion is not needed. Correction: in this delivery create a definition node (item chapter, §5/H12 fields, source Groupoids 03YW/Schemes 01JB) owning a module with IsClopenDecomposition (source/blueprint docstring), import it in the item, and cite that definition node in stmt_deps instead of lem-galois-coproduct-copies-morphisms-clopen (keep the lemma as proof dependency only); recompile with nt_compile.py.

## sk-lem-geo-cartier (2026-10-18 02:21 UTC, branch head a18c124ad2)

L: independent stage-2 immutable head a18c124ad2da: Per-file compile reproduced clean (42.4 s, no errors or warnings). The étale family κ is uniquely pinned by SupportedKummerRelative (Ext^2_A(i_*A_D,-) equals Ext^2_Z(i_*Z_D,-) because i_*Z_D is Z-flat), so the étale Chern, exponent, coefficient (every φ) and base-change (every Cartier-preserving square) clauses are correct and not vacuous. The pro-étale c is uniquely the ν^*-transport of κ, and the comparison isomorphism is asserted. No hollow defs, sorry only in the theorem, docstrings and the record verbatim OK, edge cases OK. RETURN H3: the node's conclusions about c_D in D(Z_proet,Λ) are absent. (1) The composite of c with the pro-étale adjunction unit Λ_Z→i_*i^*Λ_Z=i_*Λ_D equal to ν^*c_1 is missing, and no pro-étale unit or c_1 is defined. (2) Coefficient compatibility of c for Λ→Λ' is stated only on étale κ. (3) Base change with the pro-étale g^*, the canonical exchange and the Tate-line pullback is stated only on étale κ. These need step-8 comparison theorems and are not in the statement; citers (det-prop-diagonal-tower-trace, sk-lem-geo-p1-cohomology) use the pro-étale composite. Correction: add the pro-étale Chern equation, coefficient square and base-change square for c in FiniteCoefficientDerivedCategory (finiteModuleAdjunction/finiteCoefficientDerivedDirectImage for the unit, finiteCoefficientDerivedPullback, comparisonDirectImageCanonicalMate, the canonical constant and Tate-line isomorphisms). H4: the recorded proEtaleSheafInverseImage and proEtaleConstantModuleDirectImage of the cited stmt_deps are unused; ProEtale.lowerStar (def-sfb-finite-lower-star, not in stmt_deps) is used with no §1(B) note. Use the recorded declarations or cite and note the substitution.

## def-per-support-condition (2026-10-21 11:42 UTC, branch head 4f05fbb5e34)

I read the item in full; the delivery adds no new nodes. Support half (SuppCon ⇔ dim Supp H^{-i}K ≤ i, closed rational-fibre support, subspace Krull dimension) matches main-20261015 order 3082. Edge cases checked: K=0 and empty X; a point with F[m] (support half holds iff m≥0, cosupport half iff m≤0); smooth L[d]. Making ℓ invertible explicit is a typing repair forced by def-weil-pbc-qbar-category. The worker is right that def-trf-dualizing-complex covers only finite coefficients over the finite-field closure. F1 (route decision 2026-10-19, B/C): the new D_X cite lem-per-qbar-arbitrary-field-duality is dropped (route-pivot-dropped.txt line 1836). Its closure contains the dropped Gabber local-duality chain (finite-residue-dualizing, potential-local-duality, gabber-local-duality-general, gabber-partial-algebraization, …). The item is a stmt_dep of live lem-per-artin-gabber-affine-curve, whose note coord/repair-notes/lem-per-artin-gabber-affine-curve.json lists this node in removed_deps and forbids arbitrary-field Qbar_l duality. The report justifies this at no step. A re-citation cannot fix it: no live node gives arbitrary-field Q̄_ℓ Verdier duality (thm-coef-qbar-verdier and def-weil-exceptional-inverse-image cover only the finite-field closure). Two repair routes need an author decision: (a) define ω_X as an object representing Hom(Ra_{X!}−, Q̄_ℓ), with Ra_{X!} from def-weil-integral-rational-qbar-compact-support (arbitrary field) and no existence claim, as the landed Lean QbarCosupportCondition does; or (b) narrow D_X to the finite-field scope with a recorded correction checked against the citers. F2 (error 7): the statement changed but the node has no statement_change field. Mechanical findings: the batch-5 flag on lem-per-adic-heart-pullback-fibres is accepted (it reaches only the definition def-pod-lisse-l-adic-sheaves); the batch-5 path of the duality node is general algebra but moot under F1; the artin-gabber finite-coefficient finding is upheld. Maintainer note: the item is Lean-closed (B10), and the two citers that would need arbitrary-field generality (qbar-middle-tstructure, qbar-affine-support-bound) are themselves dropped.

## lem-sfb-continuous-algcl-tame-boundary-comparison (2026-10-21 13:35 UTC, branch head 0e5c7e1cc70)

L: independent stage-2 immutable head 0e5c7e1cc703: H1: there is no Lean module and no item lean record, and the report has no '## Second reading by NQ' section; this is a stage-1 split head sent on the S2 lane. H2: the item's proof/proof_deps/proof_origin/split_report/status were changed, but stage 2 permits only lean and stmt_deps. H12: the 3 new nodes (tame-transverse-open-exchange, tame-stratum-inertia-model, tame-condensed-inertia-koszul) are statement-only lem- nodes, not def- nodes with modules. Superseded: NF 26a608e08's split of this item LANDed at 21:31:15 and is live with status split, reviewed by NT-cc-NF-26a608e08, lean null; the side-live clone is out of date. Correction: drop this head; a stage-2 delivery must state the item in one Lean module with a sorry proof on top of the live NF split, with a verbatim lean record, a Worker report and a Second reading by NQ, and no changes to proof fields. No compile: there is no file and no FIX.

## sk-lem-picard-cech-computes (2026-10-21 19:53 UTC, branch head 8dbe90e2256)

L: approved by the reader, but the landing refused it: NOT MERGED sk-lem-picard-cech-computes: sk-lem-picard-cech-computes: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.
