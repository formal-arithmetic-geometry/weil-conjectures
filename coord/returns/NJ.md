

## lemma-weil-pbc-level-map-derived-limit (2026-10-13 20:44 UTC, branch head f4a5ec3e68)

E1, E5/E6, E7; C2 in step 2: the product calculations are sound, but the cited cone definition asserts functoriality without constructing it for these derived-category towers. Stacks 08TC/0H9J gives nonunique triangle fillers; Mathlib cone composition requires strict chain squares. The existing strict-tower functor also uses a different coefficient category, with no applicable comparison cited. Full checks and edge cases are recorded in review.md; no targets were weakened.



## prop-weil-pbc-levelwise-truncations (2026-10-16 04:53 UTC, branch head 79a576dd7c)

L (re-issued by the launcher; the entry had been lost): eviewer NT-Codex-NI-7a239cace --head 7a239cace67e059f0bfc8358cdc7560ca82d8847 --spot-checked Read the complete item, report, dependency statements, route and cited sources. Balmer–Schlichting Definition 1.2/Remark 1.4 and Mathlib fullyFaithfulToKaroubi exactly support the inclusion theorem. Checked projector identities, Hom inverses, matrix edge cases, non-Karoubian examples and whole-DAG reuse. No new nodes, missing citations, cycles or repairs. Detailed checks are in review.md. --verdict PASS


## thm-weil-pbc-finite-stage-karoubian (2026-10-16 04:53 UTC, branch head f9607f666a)

L (re-issued by the launcher; the entry had been lost): an: coord/.merge.lock held for 120 s by pid 1929829: /usr/bin/python3 tools/merge_delivery.py Q25 lem-pur-a1-components --stage 1 --reviewer NT-Codex-Q25-d377be861 --head d377be86104da92153a81eac72997334d9a9d14d --spot-checked Read the item, unit, all cited nodes, and cited sources in full. Verified all ten proof steps, hypotheses, relative-spectrum correction, component and fibre arguments, edge cases, duplicate searches, and DAG dependencies. No new nodes or repairs are needed. --verdict PASS


## thm-weil-pbc-integral-truncations (2026-10-16 04:53 UTC, branch head 50c97b9211)

L (re-issued by the launcher; the entry had been lost): NI-dbb05f32e --head dbb05f32eaa6e58f595028d584ab86a8bd44d934 --spot-checked Read the complete item, cited statements, master sources, report, and unit/chapter route. All four steps, associator directions, inverse calculations, edge cases, and dependency checks pass. Accepted lem-fix-operation-reduction as the declared comparison tool. No new nodes or repairs. Condensed-category and Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## def-weil-exceptional-adjoint-admissibility (2026-10-16 06:44 UTC, branch head f2dc2e680c)

L: approved by the reader, but the landing refused it: NOT MERGED def-weil-exceptional-adjoint-admissibility: def-weil-exceptional-adjoint-admissibility: no longer stage-1-open; live completion takes priority Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.



## det-proper-heart-bound-rational (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 2 (2792 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 2 (2792 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.

## lem-sfb-unbounded-sections-localization (2026-10-18 01:44 UTC, branch head e704d494fe)

L: independent stage-2 immutable head e704d494feec: Substance correct: Lean matches node and Stacks 0D6F clause by clause (small ringed site in universe u; W arbitrary; J.over W, R.over W, SheafOfModules.overFunctor; derivedSections = rightDerivedFunctor of evaluation followed by forget₂; natural iso e on all of D(O); normalized on every K-injective I to the definitional identity I(W)=(I|_W)(id_W) through the canonical model/localizedModel isomorphisms; H^q(e) for every q in ℤ; no boundedness). Edge cases, docstrings, no hollow defs and sorry-only proof checked; delivered module compiles clean with nt_compile --json (12-15 s; error reporting confirmed with a probe). RETURN on delivery-errors §2/§12, the mechanical finding: stmt_deps gains theorem node lem-pur-rhom-into-kinjective-local, but the statement uses only its helper module_overFunctor_preservesZero, not the theorem's conclusion, and that fact already follows from the cited definition node def-weil-pbc-ringed-derived-restriction. Correction: remove lem-pur-rhom-into-kinjective-local from stmt_deps and drop `public import Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal`; define instance restriction_preservesZero as `letI := (ringedOverFunctor_exactGeneral R W).1; inferInstance`; pass `(restriction_preservesZero R W)` to isKInjective_restrict_localized in localizedModel. This variant compiles clean (20 s) and the signature is unchanged. Merge fixes cannot remove an added item stmt_dep, hence RETURN rather than FIX. The use of isKInjective_restrict_localized (08FI) in localizedModel is a genuine use of that theorem's conclusion, recorded in proof_deps; accepted.

## lem-per-ind-etale-regular-coordinate-locus (2026-10-19 01:49 UTC, branch head 6c615f61fef)

F1/route-pivot. I confirmed the mechanical finding: Step 5 cites lem-per-snc-boundary-parameter-criterion, which is in the 2026-10-19 artin-gabber section of side coord/route-pivot-dropped.txt (line 1916), and the report gives no justification for it. The bigger problem is that the item itself is dropped (line 1649), and so is its only citer lem-per-henselian-regular-pair-spreading (line 1638). Its whole blueprint.from.via chain (uniformization-complete-local-descent, nodal-quotient-reduction, gabber-prime-to-ell-regular-cover, ..., qbar-arbitrary-field-duality) is the Gabber-uniformization branch of the Q144 split, which coord/repair-notes/lem-per-artin-gabber-affine-curve.json removed: 'do not cite ... Gabber's finiteness over quasi-excellent bases, Gabber uniformization, de Jong alterations or stable reduction: the Q144 split (5ea9835359) that did so is dropped ... and the review rejects citations of it.' Changing a citation cannot repair a split of a dropped, unreached item. I still read the maths in full and it is sound: J-2 openness over every marked intersection (Stacks 07P7), the RSOP count from 00NQ and the dimension formula, non-associate parameter primes giving a radical product ideal, SNC to coordinate condition via 0BI9/0BIA, the strict henselization shared under ind-etale maps with faithfully flat reflection of unit ideals, principality, cotangent independence and K=P. Small cases checked: m=0, V(x)∪V(y) with K=(xy), K=(x^2y) failing, unit labels, coincident labels. There are no new nodes. Maintainer: withdraw this item from stage-1 dispatch.

## lem-trf-derived-evaluation-canonical-map (2026-10-20 12:24 UTC, branch head no branch)

(the landing tools, head 1df3eea78) the delivery did not land: (merge queue) your landing 20261020T121954-NJ-450639-0 was taken out of the candidate: the global build of be2d44de55 failed in Sheaf.Algebra.Homology.DerivedEvaluationCanonicalMap Sheaf.Algebra.Homology.HomTensorTotal Sheaf.Algebra.Homology.KFlatConeTrianglePresentation job job computation; this change is a possible cause


