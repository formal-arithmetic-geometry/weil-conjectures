# Stage-1 worker report: def-pod-perfect-complex-on-x

## Files written

- `dag/nodes/sec-six-functors/def-pod-perfect-complex-on-x.json`: definition split through three existing definitions, with logged Mathlib searches and blueprint cross-reference; no new nodes and no Mathlib leaves.
- `citations.json`: `[]`; the item is a definition and has no proof steps.

## Attachments

None. `AlgebraicGeometry.ProEtale.DerivedCategory.IsLocallyPerfect` in `WeilConjectures/SixFunctors/ProEtale/Derived/Perfect.lean:428` defines local bounded finite-free-retract models in the ordinary derived category of constant-ring pro-etale module sheaves. It does not supply the completed integral, localized rational, and common-stage coefficient categories of this item. Its body contains no sorry, but the category mismatch rules out an attachment for the complete item.

## WANTED

None.

## What was wrong and what changed

The inherited attempt expanded degreewise retractions itself and called every coefficient stage a category of module sheaves. This leaves the rational and common-stage interpretations insufficiently precise. I replaced that expansion by the existing, reviewed `def-weil-site-perfect-complex`, whose statement explicitly distinguishes all four stages. This is a definitional clarification of the current blueprint's local condition, not a new equivalence with dualizability or a change in hypotheses. The ambient Poincare hypotheses and the input `K ∈ D^b_ctf` are retained. The direct dependencies are now `def-pod-conventions`, `def-weil-finite-tor-amplitude`, and `def-weil-site-perfect-complex`; the latter already supplies the site, coefficient sheaves, and local models. The earlier eight search records were checked against `searches.jsonl`; four further searches were run in this continuation. Searches using an invalid Mathlib subdirectory in the historical log remain excluded.

The previous sandbox changed the maintainer-owned `source` field. I restored it verbatim from the shared repository; `split_report.blueprint` identifies the current main-20261015 source actually read. The imported `blueprint_update`, import flags, and other maintainer metadata are retained.

## Existing-node and blueprint search

I searched the whole DAG and source checkout for the item id, `IsLocallyPerfect`, `finite projective`, and local-perfectness phrases. I ran `tools/blueprint_refs.py ancestor def-pod-perfect-complex-on-x` and whole-blueprint searches for `perfect`, `finite projective`, and `locally quasi-isomorphic`. `sk-def-perfect` contains the same local-model clause together with point perfectness and the dualizability equivalence, so it is recorded in `blueprint.same_as`; those additional assertions are not used. The reviewed `def-weil-site-perfect-complex` supplies exactly the stage-sensitive local condition and is reused, not copied into a child node. The generic strict-perfect package was also opened; it addresses a larger package of chosen splittings and is unnecessary here. No new-node duplicate pairs arise.

## Review by Q130

I read the chapter and unit records, the current main-20261015 `sec-six-functors/sk-thm-sf-package/def-pod-perfect-complex-on-x.md` (order 2590), its older master copy, and the current `def-weil-site-perfect-complex` definition (order 2225, as reproduced verbatim in that node's `blueprint_update`). The item says locally quasi-isomorphic to a bounded complex of finite projective coefficient modules, for `K ∈ D^b_ctf` in the fixed Poincare setting. The stage-specific explanation follows the current existing site-perfectness definition, without adding the dualizability equivalence from `sk-def-perfect` or replacing the completed integral category by discrete non-torsion coefficients.

I opened all three direct dependency statements. `def-pod-conventions` fixes the finite-field, smooth separated geometrically connected pure-dimensional scheme, coefficient stages, and Poincare ambient categories. `def-weil-finite-tor-amplitude` defines `D^b_ctf`, including uniform finite-reduction amplitude at the integral stage. `def-weil-site-perfect-complex` states the local bounded finite-projective definition at finite coefficients, the completed integral coefficient sheaf, the raw rational localization with finite-free summands there, and existence of a finite-extension representative in the common-stage category. These are exactly the notions the item's statement takes from them. I removed redundant direct dependencies whose notions are supplied through these interfaces. There are no proof steps, so the C1/C4 proof-citation audit and `citations.json` have no entries; no theorem is smuggled in as an elementary proof step, and no off-unit proof tool is used.

For the attachment check I read `Perfect.lean:424–438`, the coefficient variables at line 167, and the surrounding coefficient documentation. The local-model body has no sorry but concerns the ordinary constant-ring sheaf category; the later dualizability equivalence is explicitly sorry. Neither supplies all coefficient-stage clauses of the item. No source declaration was accepted merely because its docstring names the blueprint id.

I checked edge cases: the zero complex has a bounded local model with rank zero; an actual bounded finite-projective complex satisfies the finite-stage local condition on the identity cover; local bounds and ranks need not be uniform over the cover. At the integral stage the coefficient unit is completed, and at the rational stage splittings are taken in the localization, so no unjustified integral model or reduction of an arbitrary rational object is required. There are no new statements to test, no hidden existence theorem, no hollow definition, no SGA source, and no unit-route replacement.

I reran LeanFinder, Loogle, LeanSearch, and source grep using msearch.py. LeanFinder/LeanSearch return sheaf finite-presentation and finite-generation APIs plus general derived-category and K-projective APIs. I read `Quasicoherent.lean:236–269`, `Generators.lean:113–144`, and `TStructure.lean:180–188`: none defines local bounded finite-projective models. The grep hits `Contraction.lean:151,156` and `PicardGroup.lean:378` concern ordinary scalar finite-projective modules or invertible modules, not perfect complexes of sheaves. The earlier valid searches supply second phrasings as well. All recorded queries occur in the immutable search log, and no unavailable service is represented as proof of absence.

## What could not be finished

No mathematical work remains unfinished. The mandatory no-push delivery dry run must print OK before this sandbox is handed off as READY; its durable receipt records validation. No delivery or push is authorized for this first-reader handoff.

## Second reading by Q130

- Item statement: compared the complete paragraph with main-20261015 `sec-six-functors/sk-thm-sf-package/def-pod-perfect-complex-on-x.md`, order 2590, and its `blueprint_update`; PASS. The fixed Poincare hypotheses and restriction to $K\in D^b_{ctf}(X,\Lambda)$ are unchanged. Local quasi-isomorphism, boundedness, and finite projectivity remain the defining condition; dualizability is not asserted.
- Constituent `def-pod-conventions`: opened its complete current statement and dependencies; PASS. It supplies the finite-field base, $\ell\ne p$, $n\ge1$, smooth separated finite-type geometrically connected pure-dimensional $X_0$, the exceptional-adjoint admissibility assumption, and all four coefficient stages. Properness is not imposed by this item.
- Constituent `def-weil-finite-tor-amplitude`: opened its complete current statement; PASS. The item uses exactly its bounded constructible finite-Tor category, with a single interval for every integral reduction and the rational/common-stage conventions at field coefficients. Perfectness is an additional local predicate on these objects, not a claim that finite Tor amplitude implies site-perfectness.
- Constituent `def-weil-site-perfect-complex`: compared its complete statement with main-20261015 `sec-six-functors-basics/sk-prop-sf-pf-reduction/def-weil-site-perfect-complex.md`, order 2225; PASS. Finite projective means a direct summand of a finite sum of the coefficient sheaf. The integral unit is completed, rational summands are taken in the localized category, and the algebraically closed stage requires some finite-extension representative. This is the same local condition restricted to the item's setting; no comparison theorem is required.
- Proof steps: none, as verified in the current blueprint and the sandbox node; PASS. This is a definition split into existing constituent notions under stages/1-dag.md section 3(2). Both `proof` and `proof_deps` are empty, and `citations.json` correctly remains `[]`. There is no elementary proof claim, uncited non-elementary step, or appeal to a dependency's proof.
- New nodes: none, verified by listing every sandbox node file; PASS. B1-B7 and the per-new-node statement, duplicate, citation, and source audits therefore have no instances. Existing whole-DAG keyword matches include `def-weil-site-perfect-complex`, which is reused, and `sk-def-perfect`, which additionally asserts dualizability equivalences and point perfectness. No new copy of either is introduced.
- Edge cases: PASS. The zero complex has the all-zero bounded model (rank zero); at $X=\operatorname{Spec}k$ and field coefficients, a bounded finite-dimensional constant complex supplies its own model. At finite level $n=1$ the same definition applies, and $n=0$ is outside the fixed hypotheses. If an empty scheme is admitted by the ambient conventions, the empty covering makes the local predicate vacuous. Bounds and ranks may depend on the covering member; no global bound or free model replaces the local projective condition.
- Lean attachment and Mathlib audit: PASS with no attachment or Mathlib leaf. I independently read `WeilConjectures/SixFunctors/ProEtale/Derived/Perfect.lean:424-438` and its coefficient variables at line 167: `AlgebraicGeometry.ProEtale.DerivedCategory.IsLocallyPerfect` has the finite-coefficient local-model body, but not the integral completed, rational localized, or common-stage categories. Its later dualizability equivalence at lines 439-449 contains `sorry` and supplies no finished proof. A search of the read-only upstream master and slopmaster2 trees found no complete replacement. Fresh msearch.py queries used retracts of bounded finite free complexes, `SheafOfModules, "projective"`, and `StrictlyPerfect|IsPerfectComplex|LocallyPerfect|PerfectComplex`. Loogle and source grep returned zero hits; LeanFinder returned local presentation/generator APIs, whose definitions I read in Mathlib `Quasicoherent.lean:200-269` and `Generators.lean:106-144`. They concern individual sheaves and do not define this complex predicate. The actual results remain in `searches.jsonl` and are recorded in the node.

Changes made by the second reader:

- Added three independently run Mathlib searches and their source-checked verdicts to the item's search evidence, using different phrasing from the first reader.
- Added this independent source, dependency, edge-case, and attachment audit. The mathematical statement, constituent dependencies, first-reader report, source metadata, and empty citation list required no repair and were retained.

The required final server dry run is performed after this section is complete, and delivery follows only after that invocation exits successfully. No Lean was written and no compiler, Lake, local preflight, or local DAG-review tool was run.
