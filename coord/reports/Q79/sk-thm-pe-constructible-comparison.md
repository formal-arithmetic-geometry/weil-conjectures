# Stage-1 delivery: sk-thm-pe-constructible-comparison

## Files written

- `dag/nodes/sec-proetale-coefficients/sk-thm-pe-constructible-comparison.json`: the existing statement node, retained and marked `split` with its three complete proof steps; no new child nodes.
- `citations.json`: 23 verbatim statement quotations, one for every cited node in every proof step.
- `searches.jsonl`: the four Mathlib searches run through `msearch.py` for this Q79 item.
- `report.md`: this report.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` for the exact item id, the blueprint tag, constructible-comparison terminology, and the relevant comparison declarations. The source contains finite-coefficient constructibility declarations such as `AlgebraicGeometry.ProEtale.isConstructible_comparisonUpperStar_obj` and derived-origin definitions, but no sorry-free declaration stating this Noetherian qcqs sheaf-and-derived comparison item. The upstream master checkout is reference material with sorry declarations and is not treated as an attachment. No Lean was written or compiled.

## WANTED

None. The item proof follows the local main-20261015 blueprint and existing DAG statements.

## What was checked and changed

The item statement is retained verbatim. Its three imported proof steps already realize the current blueprint: (1) the affine-local constructibility/classicality identification and qcqs finite disjointification, (2) the constructible sheaf equivalence by pullback to strata and the finite-local-system twist, and (3) the bounded derived equivalence via cohomology and reflection of boundedness. I retained all statement dependencies, source fields, blueprint ancestry, import flags, and prior search metadata, and changed only the status to `split` and the mechanically regenerated proof-dependency ordering. No new node was necessary because every non-elementary fact used by the steps already has a DAG node. No unit record required editing; its `realized` fields already record this item.

The exact item declaration was absent from the slopmaster2 source, so there is no Lean attachment. The source files `SixFunctors/ProEtale/ConstructibleSheaf.lean` and `SixFunctors/ProEtale/Derived/Constructible.lean` were read to distinguish their finite-coefficient/étale-origin declarations from the broader DAG statement.

## Mathlib searches

I ran and recorded LeanFinder, Loogle, grep, and LeanSearch through `msearch.py` using the item’s constructible pro-étale comparison wording, then repeated all four with a second phrasing and a source-root grep. LeanFinder and LeanSearch returned generic étale-site, pullback, and condensed-sheaf declarations; Loogle reported unknown identifiers and no hits; grep found only generic pro-étale site declarations and no constructible-comparison declaration in Mathlib. None is an exact statement or a one-line specialization, so the item is not a Mathlib leaf.

## Review by Q79

I read the current item node, `dag/chapters/sec-proetale-coefficients.json`, `dag/units/sk-thm-pe-constructible-comparison.json`, the main-20261015 blueprint section, its `-classical.md`, `-equivalence.md`, and both detailed proof files, plus the current statements of all 15 distinct cited DAG nodes. The citations file copies each cited statement verbatim; no step relies on a node’s hidden proof.

Step 1 uses `det-pe-classical-definition-continuity-map` for small cofiltered affine presentations, the opposite filtered colimit, the scalar action, the affine-base qualification, and the cohomological convention; `sk-def-sfb-constructible` for finite constant local models and the qcqs/global versus affine-local constructibility definitions; `det-pe-classical-sheaves-modules` for the coefficient identification and exact fully faithful comparison; the Noetherian finite-module finite-presentation lemma; and `det-pe-constructible-comparison-classical` for the final classicality implication. The affine scheme qcqs, affine-open basis, quasi-separated affine-intersection, and Boolean constructible-subset nodes supply exactly the finite-cover and disjointification hypotheses used in the paragraph. I checked that the pieces remain constructible, locally closed, disjoint, and covering, and that no Noetherian hypothesis on `X` is silently added. The empty scheme and zero sheaf are included.

Step 2 uses `def-pe-etale-constructible-module` for the affine-open finite-stratification definition with finitely generated module models; `sk-thm-pe-direct-image-comparison` for inverse-image compatibility on each stratum; the Noetherian finite-to-finite-presentation lemma; `det-pe-finite-local-systems-twist` for an étale finite-presentation antecedent of each pro-étale local system; `det-pe-classical-sheaves-modules` for full faithfulness and the construction `G = nu_*F`; `det-pe-constructible-comparison-classical` for classicality of a constructible `F`; and `sk-def-sfb-constructible` for the target constructibility condition. I checked both directions, the pullback to each locally closed stratum, lifting of the stratum isomorphism and its inverse by full faithfulness, and the finite-presentation hypotheses. This proves essential surjectivity without an uncited gluing assertion.

Step 3 uses the complex clause of `det-pe-classical-definition-continuity-map`, `sk-prop-sf-comparison` for the bounded-below derived unit, and `det-pe-classical-derived-equivalence` for the inverse equivalences on `D+` and classical complexes. It uses exactness and full faithfulness from `det-pe-classical-sheaves-modules`, the bounded-constructible definition `sk-def-sfb-bounded-constructible`, the classicality result from `det-pe-constructible-comparison-classical`, and the étale bounded constructible definition from `def-pe-etale-constructible-module`. I checked the cohomology identification `H^q(nu^*L) = nu^*H^q(L)`, finite vanishing intervals, reflection of zero cohomology by faithfulness, and the conclusion that the antecedent `L` is bounded constructible. The zero complex and acyclic complexes were checked as edge cases.

I checked delivery-errors B–E: the item is self-contained through its statement dependencies; no new node is elementary, duplicate, or a relabelled clause; every non-elementary ingredient is cited; every citation quote is verbatim; all hypotheses used in the finite-cover, local-system, and derived-equivalence applications are present; no SGA source is used; and the proof has no hidden long auxiliary lemma. The server-side `check_dag` preflight passed before this report was written.

## What could not be finished

The required server-side `check_dag` passed before this report was written. The full delivery dry run then passed with `OK (not pushed)` and receipt `84f888dc30`; preflight, DAG checks, split review, and citation validation all succeeded. Only the final push delivery remains.
