# Stage-1 report: lem-pur-co-smooth-etale-locality

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-co-smooth-etale-locality.json`: existing blueprint statement promoted from `unsplit` to `split`; no new dependency node was created.
- `citations.json`: 59 step-to-node citations, with each quote copied verbatim from the cited node statement.
- `searches.jsonl`: eight Mathlib searches run through `msearch.py` (two phrasings each for LeanFinder, Loogle, grep, and LeanSearch).
- `report.md`: this report.

## Attachments

No attachment. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the upstream declaration-name indexes for the item id, its blueprint tag, and the notions `cohomologically smooth`, `dualizingComplex`, and `IsCohomologicallySmooth`; no sorry-free project declaration states the full item under the item hypotheses. The declarations found in the source concern individual affine-space/smooth dualizing-complex results and do not state source-étale locality together with trivial étale dualizing object.

## WANTED

None. The proof sources cited by the item are present in `literature/`, including the current main-20261015 blueprint proof and the Stacks Project files/tags named in the steps.

## What was wrong or needed repair

The repository copy contained the complete imported seven-step proof and its reviewed `split_report`, but its node status was still `unsplit`; I changed only that status in the sandbox copy. The proof already cites the existing unsplit node `lem-pur-etale-support-map-compatibility`, so I did not create a duplicate child. I retained all imported hypotheses and dependencies, including the distinction between separated finite-type source maps and arbitrary (possibly non-separated) base-change arrows. The Mathlib searches found only geometric smoothness/étale algebra facts, so this item remains a project-level statement rather than a Mathlib leaf. The two Loogle queries returned unknown identifiers; those failures are recorded in `searches.jsonl` and represented as no matches.

## What I could not finish

No unresolved split work remains. The target is natural-language stage 1 only; no Lean file was written and no compiler, Lake, or build tool was run.

## Review by Q129

I read the item statement, its source entry in `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-cohsm/lem-pur-co-smooth-etale-locality.md`, and the current proof in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-cohsm/lem-pur-co-smooth-etale-locality.proof.md`. I also read the existing dependency `lem-pur-etale-support-map-compatibility` in full before using it; its statement explicitly supplies the proper-support comparison normalization, arbitrary-base-change exchange identity, and counit-defined projection identity used by Steps 2, 4, and 6. I checked the item’s 41 `proof_deps` against the seven `uses` lists and regenerated `citations.json` from the exact statement text of all 59 cited occurrences.

Step 1 is the domain/typing argument: I verified the fixed finite coefficient stage, finite-type-over-a-field Noetherian hypotheses, compactification input, transported adjunction, source restriction comparison, constructible and finite-Tor preservation, and the arbitrary-base-change typing. The cited nodes are `def-pur-conventions`, `def-pur-co-smoothness`, `lem-weil-pbc-finite-type-over-noetherian`, `thm-nagata-compactification`, `def-weil-exceptional-inverse-image`, `lem-sf-proetale-constructible-origin`, `thm-weil-pbc-site-comparison`, `lem-sf-class-compact-support-comparison`, `def-weil-derived-pullback-tensor-hom`, `lem-weil-proetale-weakly-etale-localization`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `cor-pur-general-admissibility-datum`, `lem-sf-pullback-tor-amplitude`, `lem-sf-tensor-ctf`, `lem-weil-finite-compact-projection-formula`, `thm-cbc-finite-level-proetale`, `lem-kun-dimension-finite-type`, `thm-sf-ambient-adjoint-class`, `def-weil-pbc-site-comparison-morphism`, `lem-sf-comparison-tor-amplitude`, `lemma-constructible-pullback-stratification`, `lemma-constructible-pullback-constant`, `lem-weil-pbc-etale-covering-base-change`, and `lem-sf-flat-model`. I specifically checked that no separatedness of an arbitrary base-change map is smuggled into the typing argument.

Step 2 identifies the exact finite-coefficient étale proper-support/sum adjunction and its normalization. I checked that `lem-sfb-quasifinite-compact-support-exact` is used only for the canonical comparison and exactness, while the existing compatibility node supplies the actual exchange and projection maps; `lem-amb-etale-adjoint-locality` gives the sum/evaluation adjunction; `def-weil-pbc-etale-shriek-base-change-map`, `lem-weil-finite-compact-projection-formula`, `def-exchange-projection`, `thm-cbc-finite-level-proetale`, and `thm-sf-ambient-adjoint-class` transport the identities to the specified functors. The graph/counit calculation is stated at the level needed by the item, rather than inferred from an abstract right-adjoint isomorphism.

Step 3 uses `lem-amb-etale-adjoint-locality`, `lem-amb-etale-compact-comparisons`, and `thm-sf-comp-composition` to obtain the canonical source-restriction comparison and its counit formula. I checked the Hom chain is on the cited bounded-below domain and that the comparison is obtained by representing natural Hom bijections.

Step 4 uses `def-pur-co-smoothness`, `def-exchange-projection`, `lem-weil-pbc-mate-pasting`, `lem-pur-etale-iso-descent`, `fix-prop-projection-formula`, `thm-sf-ctf-stability`, and `lem-pur-etale-support-map-compatibility`. I recomputed the common transpose for the tensor map, including the composite counit and projection-formula composition, then checked that surjective étale pullback plus the cited descent theorem gives the tensor isomorphism on the base. The step’s source and target are the bounded constructible objects established in Step 1.

Step 5 constructs the global inverse by `lem-pur-rhom-global-sections` and `lem-weil-pbc-ringed-internal-hom-exact-restriction`; `lem-kun-dimension-finite-type` and `cor-weil-finite-constructible-hom` give the required bounded constructibility, while `lem-weil-proetale-weakly-etale-localization`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `def-pur-co-smoothness`, and `lem-pur-etale-iso-descent` identify and descend its evaluation map. I checked that the inverse is the already-defined internal Hom object, so no object is chosen by a mere existence assertion.

Step 6 is the arbitrary-base-change argument. I checked the fibre-product hypotheses using `lem-weil-pbc-etale-covering-base-change` and `lem-pod-separated-finite-type-base-change`, then checked the mate identity for beta against `lem-amb-unbounded-compact-support-comparisons`, `lem-pur-etale-support-map-compatibility`, `lem-weil-pbc-mate-pasting`, and `lem-cbc-proetale-stalk-conservative`; the latter is applied only to the singleton surjective étale cover and does not assume the base-changed source is separated. Step 7 is the final assembly and uses `lem-cbc-proetale-stalk-conservative` for the remaining descent/conservativity conclusion.

The steps with more than 2000 characters were reviewed for hidden lemmas. Their long portions are explicit typing, mate, and descent calculations whose constituent non-elementary facts are all named in `uses`; no additional independent lemma or comparison is hidden. I tested the identities conceptually on the identity étale map, an open immersion, a finite étale map, an empty source, and the zero coefficient ring while checking that the statement retains every hypothesis from the blueprint route. No SGA 4/4½ source is cited.
