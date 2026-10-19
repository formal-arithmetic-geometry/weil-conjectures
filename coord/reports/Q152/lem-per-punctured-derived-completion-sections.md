# Stage-1 report: lem-per-punctured-derived-completion-sections

## Files written

All node paths below are under dag/nodes/sec-deligne-laumon-a1/.

- lem-per-punctured-derived-completion-sections.json: split in seven proof steps; imported statement unchanged verbatim.
- lem-per-derived-completion-pseudocoherent.json: statement-only Noetherian structure-sheaf derived-completion model, including the coherent-sheaf reduction comparison; Mathlib no match.
- lem-per-punctured-cohomology-ml.json: statement-only, exactly the two Mittag-Leffler assertions of 0DX1; Mathlib no match.
- lem-per-mittag-leffler-derived-limit-acyclic.json: statement-only general countable ML acyclicity; Mathlib no match.
- citations.json: full verbatim statements for every node cited by every proof step.

## Attachments

None. I searched /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the item tag and for punctured-spectrum and derived-completion notions. The derived-complete constant-coefficient sheaf APIs in CategoryTheory/DerivedCategory/Complete and the pro-etale trace-formula modules do not state this structure-module Zariski comparison. No Lean file was written and no compiler, Lake or build was run.

## WANTED

None. The sources used below are present under literature/stacks-project/.

## Repairs and searches

I retained and reread the saved work before editing. The required initial dry run exited with SEARCH CHECK FAILED because the three proposed helpers' recorded queries were absent from searches.jsonl. I ran their searches through msearch.py, read the hits, and replaced unsupported records with the actual outputs. LeanSearch and a second phrasing were also run. Old Loogle queries with unknown identifiers are recorded as rejected queries, and valid identifier queries or both semantic services supply the actual checks. The item's inherited queries were rerun and their results updated too. The full outputs and log remain in the sandbox. I did not alter any launcher or validation tool.

No match was found: AdicCompletion and its finite-module tensor equivalence are ordinary module results; localCohomology is the Ext-colimit construction and its radical comparison; the IsMittagLeffler and stable-range API is general set/category theory. None states the structure-sheaf completion comparison, Artinianness/local ML theorem, or derived-limit acyclicity. I read Mathlib/Algebra/Homology/LocalCohomology.lean, especially its definitions and radical-independence theorem at lines 159-218, and CategoryTheory/CofilteredSystem.lean at IsMittagLeffler (137) and surjective_toEventualRanges (262). Candidate finite-module completion declarations have neither the sheaf category nor the derived-completion reflection in the new statement.

The saved item was still marked unsplit; it is now split. I filled the new nodes' chapter, unit and complete blueprint.from.via ancestry. The current main-20261015 ancestor lem-per-artin-gabber-affine-curve was read: its duality symmetry is Step 3, so the saved Step 1 metadata was corrected while retaining the inherited potential-dualizing chain. No chapter or unit statement or route was changed.

A first repaired dry run passed at b5df1f1845. The subsequent broad same-tag comparison found lem-weil-pbc-ringed-pushforward-completion. I removed the proposed formal-functions helper as redundant, reused that existing theorem on the structure morphism to (pt,A), and reused lem-weil-pbc-constant-completion-equivalence on the one-point site for the module quotient-tower model. The remaining Noetherian sheaf-model helper now states 0A0K (1), (3), (4) relative to the existing intrinsic-completion reflection: this is the nontrivial model comparison needed for structure sheaves, not another copy of the pushforward theorem. Further searches for its expanded statement were actually run and recorded. A subsequent preflight rejected the phrase “the item's” in Step 2 (B2); I replaced it with the explicit quotient-tower completion formula so the node reads on its own. Final validation follows this wording repair.

## STATEMENT-DISPUTED: saved new helper

The saved helper asserted degree-zero ML for the punctured tilde sheaves of every inverse system of finite modules. This is false. Take A=k[[x,y]], maximal ideal (x,y), U its punctured spectrum, and the constant modules M_n=A with adjacent maps multiplication by x. The two principal opens D(x), D(y) give Gamma(U,O_U)=A_x intersection A_y=A inside the fraction field. The images in a fixed copy of A are x^r A, a strictly decreasing chain. Thus this degree-zero tower is not ML.

I removed the false clause and its proof sketch from the new helper; it now states exactly 0DX1 (1) and (2). Step 5 proves the needed degree-zero assertion for the actual quotient tower M/I^nM, whose module transition maps are surjective. The item's imported statement was not changed. This is a correction of a saved proposed new node, not a weakening of the item.

## Review by Q152

Sources read: algebraization.tex, lemma-compare-with-derived-completion (0DXI), its entire proof, lemma-ML-local (0DX1), lemma-derived-completion-pseudo-coherent (0A0K (1), (3), (4) and its proof), lemma-formal-functions-general (0BLX), lemma-pushforward-commutes-with-derived-completion (0A0G), and remark-localization-and-completion (0A0F). For the acyclicity node I read more-algebra.tex, lemma-compute-Rlim (07KW (1), (3) and proof). For the module model I read proposition-noetherian-naive-completion-is-completion (0922); for the constant-sheaf version I checked proetale.tex lemma-naive-completion (099M). I read cohomology.tex lemma-RGamma-commutes-with-Rlim (0D60), local-cohomology.tex lemma-local-cohomology (0DWR (2)), and dualizing.tex lemma-local-cohomology-noetherian (0955 (3)), checking that local cohomology means the derived ideal-power-torsion functor already used by the item and the existing affine-support triangle. No SGA source is used.

Step 1 uses exactly the principal-open localization and quasi-coherence assertions of lem-weil-pbc-spec-module-tilde-sections. Finite generators of M and M/I^nM generate their localizations, giving finite type. pqf-def-locnoeth includes restriction to opens, and pqf-lem-coherent-ft-locnoeth supplies coherence. I wrote the quotient-localization map and its kernel, including compatibility with further localization and quotient maps, so the reduction identification is a routine consequence of those citations.

Step 2 applies lem-weil-pbc-constant-completion-equivalence only on (pt,A): its last paragraph states the Noetherian Koszul/quotient completion-unit comparison for every object, with functorial derived-limit models. I do not apply its constant-coefficient assertion to the structure sheaf on U. Instead lem-weil-pbc-ringed-pushforward-completion supplies the canonical unit-normalized comparison for the actual ringed-topos morphism (U,O_U) -> (pt,A). The ideal on the source is the extension I O_U, locally of finite type since A is Noetherian. The new sheaf-completion node supplies the distinct structure-sheaf quotient model and the coherent specialization. Coherence is from Step 1. All these cited statements explicitly concern the units, so their composite to the n-th projection is the actual reduction map, not an arbitrary isomorphism of cones.

Step 3 uses the Milnor short exact sequence and the explicit projection formula for its right arrow in lem-pc-ringed-space-rgamma-derived-limit. Its ringed-space and integer-degree hypotheses hold. The item fixes derived-functor tower models; the theorem is applied to their specified Roos triangle and projection maps, without asserting uniqueness of abstract choices of cones.

Step 4 uses only the j>0 coherent-sheaf clause of the new local ML node; negative cohomology towers are zero. Step 5 takes cohomology of lem-per-affine-support-cech-localization with the finitely generated maximal ideal and L=(M/I^nM)[0]. That existing statement gives the natural localization triangle with the same derived torsion functor, and H^1(L)=0 gives M_n -> B_n -> H^1_m(M_n) -> 0. The images Q_n of M_n form a surjective tower. I verified the equality image(B_m -> B_n)=p_n^{-1}(image(H^1_m(M_m) -> H^1_m(M_n))) by lifting and correcting with Q_m. The local-cohomology clause of 0DX1 stabilizes the images on the right. This is where surjectivity of the quotient module maps is essential; the counterexample above lacks it.

Step 6 invokes the new general acyclicity node only after Steps 4-5 establish ML for the relevant countable tower of abelian groups. This removes the saved unsupported recursive-solving shorthand. The resulting isomorphism is the Milnor right map, so the reduction-coordinate assertion survives.

Step 7 repeats the comparisons on any open V and uses 0D60 in degree zero. Its left term is R^1 lim of the zero H^-1 tower, requiring no ML hypothesis on V. The new sheaf-model statement gives open-restriction compatibility. For the completion/direct-image comparison square, the existing pushforward theorem makes the target complete over A; both arrows become restriction followed by the completion unit after precomposition with the source completion unit. Uniqueness of factorization through the stated reflection gives equality. The projection formula in the Milnor node then identifies the n-th coordinates with restriction. This also verifies naturality in M and agreement with the first clause at V=U.

Small cases: M=0 and V empty give zero; for a field U is empty and both sides are zero; I=0 gives the constant reduction tower and identity completion; I=A gives zero completion and zero reductions; nilpotent I makes the tower eventually constant. Negative degrees are zero by the completed coherent-sheaf model and derived sections. The Noetherian sheaf-model node allows non-quasi-compact locally Noetherian X and uses derived products for sheaves, not exactness of ordinary sheaf products. The acyclicity statement is countable and does not claim an arbitrary-index result.

Every new node is statement-only, introduces its objects, has empty proof/proof_deps, includes its definition dependencies and exact blueprint passage, and has actual logged Mathlib searches with results. I read every proof-step citation's full statement; citations.json quotes them verbatim. All non-elementary steps are below 2000 characters. The four off-unit tools (coherence, Milnor, ringed pushforward completion and constant one-point completion model) are declared in split_report.tool_uses; they implement the source's 0BLX/0A0K/0D60 route without replacing it.

DAG/blueprint duplicate searches included tags 0A0K, 0A0F, 0DX1, 07KW and the completion, local-cohomology, punctured and Mittag concepts, plus blueprint_refs.py searches throughout the imported blueprint. The general ringed pushforward theorem was reused; the proper formal-functions and ideal-power cohomology nodes assume properness and cannot be used on the punctured open. The existing finite-group ML and surjective-tower acyclicity assertions have stronger hypotheses. The remaining helpers supply genuinely missing model and ML inputs, not a clause of the item's completion/cohomology conclusion.

## Not duplicates

- lem-per-mittag-leffler-derived-limit-acyclic vs det-pe-continuous-cohomology-etale: The existing node states Identification with continuous étale cohomology; its conclusion is not vanishing of all positive derived limits for an arbitrary countable ML abelian-group tower.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-fd-qbar-cohomology-finite-level-comparison: The existing node states Finite-level comparison for constant Qbar-l cohomology; its conclusion is not vanishing of all positive derived limits for an arbitrary countable ML abelian-group tower.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-pc-tower-enough-injectives: The existing node states Tower category has enough injectives; its conclusion is not vanishing of all positive derived limits for an arbitrary countable ML abelian-group tower.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-pc-roos-finite-prefix-construction: The existing node states Explicit finite-prefix towers and their short exact augmentation; its conclusion is not vanishing of all positive derived limits for an arbitrary countable ML abelian-group tower.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-pc-tower-limit-left-exact: The existing node states Inverse limit on abelian-group towers is additive and left exact; its conclusion is not vanishing of all positive derived limits for an arbitrary countable ML abelian-group tower.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-pc-unbounded-derived-functor-cohomological-bound: The existing node states Cohomological bound for a derived functor on unbounded complexes; its conclusion is not vanishing of all positive derived limits for an arbitrary countable ML abelian-group tower.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-pc-tower-abelian: The existing node states The category of towers of abelian groups is abelian; its conclusion is not vanishing of all positive derived limits for an arbitrary countable ML abelian-group tower.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-pc-derived-limit-eventually-iso: The existing assertion requires eventually invertible transitions; ML towers can have noninvertible transitions forever.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-pc-injective-split-tower-extension: The existing node states Compatible lifting along one monomorphism of split injective towers; its conclusion is not vanishing of all positive derived limits for an arbitrary countable ML abelian-group tower.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-pc-derived-limit-roos-abelian-groups: The existing assertion computes R1 lim as coker(1-shift) and vanishing for q>=2; it contains no ML-to-R1-vanishing assertion.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-pc-milnor-boundary-factorization: The existing node states Natural injection obtained from the Roos connecting map; its conclusion is not vanishing of all positive derived limits for an arbitrary countable ML abelian-group tower.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-pc-derived-limit-milnor-sequence: The existing assertion gives the Milnor sequence with an R1 lim term; it does not kill that term under the ML condition.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-pc-roos-prefix-acyclic: The existing node states Positive derived inverse limits of explicit finite-prefix towers vanish; its conclusion is not vanishing of all positive derived limits for an arbitrary countable ML abelian-group tower.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-pc-tower-injective-embedding: The existing node states Towers embed into levelwise injective split towers; its conclusion is not vanishing of all positive derived limits for an arbitrary countable ML abelian-group tower.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-pc-injective-split-tower-injective: The existing node states A tower with injective levels and split transitions is injective; its conclusion is not vanishing of all positive derived limits for an arbitrary countable ML abelian-group tower.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-pc-tower-surjective-lim-acyclic: The existing assertion requires surjective transitions; ML transitions need not be surjective.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-pc-roos-finite-prefix-limits: The existing node states The full product is the limit of a finite-prefix tower; its conclusion is not vanishing of all positive derived limits for an arbitrary countable ML abelian-group tower.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-pc-abelian-groups-exact-products: The existing node states Products of abelian groups are exact; its conclusion is not vanishing of all positive derived limits for an arbitrary countable ML abelian-group tower.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-pc-roos-functorial-acyclic-resolution: The existing node states Functorial acyclic finite-prefix resolution of an abelian tower; its conclusion is not vanishing of all positive derived limits for an arbitrary countable ML abelian-group tower.

- lem-per-mittag-leffler-derived-limit-acyclic vs det-proper-heart-bound-lattice: The existing node states The lattice bound $2d+1$; its conclusion is not vanishing of all positive derived limits for an arbitrary countable ML abelian-group tower.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-per-punctured-derived-completion-sections: The existing item concludes a punctured-spectrum completed-cohomology isomorphism; it does not state this independent completion-model or ML input.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-weil-pbc-mittag-leffler: The existing assertion assumes finite abelian groups (or the stated finite-coefficient sheaf situation); the new ML groups need not be finite.

- lem-per-mittag-leffler-derived-limit-acyclic vs prop-weil-pbc-roos-triangle: The existing assertion gives a Roos triangle and Milnor sequence for coefficient towers; it does not assert general abelian-group ML acyclicity.

- lem-per-mittag-leffler-derived-limit-acyclic vs lem-kun-0bkz: The existing node states Cohomology of unbounded complexes; its conclusion is not vanishing of all positive derived limits for an arbitrary countable ML abelian-group tower.

- lem-per-punctured-cohomology-ml vs lem-per-punctured-derived-completion-sections: The existing item concludes a punctured-spectrum completed-cohomology isomorphism; it does not state this independent completion-model or ML input.

- lem-per-punctured-cohomology-ml vs lem-per-formal-punctured-idempotent-algebraization: The existing node algebraizes punctured formal idempotents; it only cites this source input and does not state it.

- lem-per-derived-completion-pseudocoherent vs lem-per-punctured-derived-completion-sections: The existing item concludes a punctured-spectrum completed-cohomology isomorphism; it does not state this independent completion-model or ML input.

- lem-per-derived-completion-pseudocoherent vs lem-per-formal-punctured-idempotent-algebraization: The existing node algebraizes punctured formal idempotents; it only cites this source input and does not state it.

- lem-per-derived-completion-pseudocoherent vs lem-weil-pbc-ringed-pushforward-completion: The existing assertion commutes intrinsic completion with pushforward and is reused. It does not identify intrinsic structure-sheaf completion with the Noetherian quotient-tensor tower or ordinary coherent reduction limit.

## Unfinished work

The one-level mathematical split is complete. The three new statement-only helpers intentionally remain unsplit for later stage-1 work. The saved report and removed duplicate helper remain outside dag/ in the sandbox as reference, and are not delivered.
