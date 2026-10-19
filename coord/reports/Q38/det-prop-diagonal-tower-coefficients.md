# Stage-1 report: det-prop-diagonal-tower-coefficients

## Files written

- `dag/nodes/sec-six-functors-basics/det-prop-diagonal-tower-coefficients.json`: repaired statement dependencies, proof steps, blueprint metadata, and split report; no statement change.
- `dag/nodes/sec-six-functors-basics/lem-six-diagonal-tower-pullback.json`: one new statement-only helper for pullback of the torsion diagonal/trace tower and its derived inverse-limit comparison; Mathlib searches found no exact match.
- `citations.json`: verbatim quotations for every node cited by every proof step.
- `report.md`: this report. `searches.jsonl` records the exact msearch calls for the item and new helper.

New nodes: 1. New Mathlib leaves: 0. Existing DAG statements are reused for coefficient limits, scalar colimits, finite freeness, continuity, and coefficient pullback.

## Attachments

None. I searched both read-only slopmaster2 `WeilConjectures/` trees for the target id/tag, diagonal-tower terminology, diagonal classes, traces, and the coefficient-stage names. No sorry-free project declaration states this item exactly. The nearby declarations are unrelated category-theory uses of the symbol `δ`.

## WANTED

None. The current main-20261015 blueprint proof and all cited DAG statements are available locally.

## Findings and corrections

The statement is mathematically coherent; no `STATEMENT-DISPUTED` marker is needed. The imported proof had an uncited use of the bounded-continuity result in its rationalization paragraph, omitted `det-prop-diagonal-tower-limit` from the first proof step, and did not state the finite-level pullback/derived-limit comparison used in the base-change paragraph. I added the missing proof dependencies and the helper node. The phrase “equivalently modulo `\\ell^n`” is interpreted through the cofinal towers `\\ell^n\\mathcal O_E=\\pi_E^{en}\\mathcal O_E` up to a unit, so the indices need not be identical.

The helper is strictly smaller than the item: it concerns only torsion Cartier/Kummer classes, torsion projective-line traces, and their derived-limit pullback; it does not construct the `\\mathcal O_E`, `E`, or `\\Qlb` scalar extensions or assert the item’s three coefficient clauses. A whole-blueprint search for this pullback/limit statement returned no other node. The helper carries no Stacks tag and is not a Mathlib leaf.

## Not duplicates

`lem-six-diagonal-tower-pullback` vs `det-prop-diagonal-tower-coefficients`: the helper states only finite torsion-system naturality and the derived-limit pullback comparison; the item additionally constructs all scalar extensions, traces, identities, and coefficient-stage base change.

## Review by Q38

I read the target node, `dag/chapters/sec-six-functors-basics.json`, `dag/units/sk-prop-diagonal-tower.json`, and the current blueprint statement and proof file `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-diagonal-tower/sk-prop-diagonal-tower-coefficients.proof.md`. I also opened the statements of every cited node and checked the target source for exact project declarations. The Mathlib searches were run with `msearch.py` for the item and the new helper using LeanFinder, Loogle, grep, and LeanSearch; the returned hits were generic algebraic-geometry or Kähler-differential declarations and did not state either pro-étale result.

Step 1 uses the existing finite-free coefficient statement for `\\mathbf Q_\\ell\\subset E`, the explicit `\\mathcal O_E` inverse-limit statement, the diagonal-limit node for the completed class and torsion reductions, and the trace node for the trace reductions and integration identities. I checked that each cited sentence says exactly the finite freeness, coefficient limit, class reduction, or trace property used. The finite-free tensor argument is spelled out as finite sums, products, and cones; the ramification relation gives cofinal reductions.

Step 2 uses the coefficient colimit statement for localization and `\\Qlb`, and the bounded-below filtered-colimit direct-image statement. I verified that `q` and each `p_i` are projective, hence qcqs, and that the two colimit systems have a common lower bound. The step applies the continuity statement to both direct images before preserving the identities by functoriality.

Step 3 uses the new helper for the finite Cartier/Kummer and trace tower comparison, the cartesian-coefficient statement for inverse-image rings and Tate twists, and the coefficient pullback statement for integral limits, localization, and the filtered `\\Qlb` colimit. I checked that after identifying the base change with `\\mathbf P^1_{Y'}`, the diagonal and section equations remain effective Cartier equations, so the finite constructions pull back with the same sign. The helper’s statement supplies the derived-limit comparison that the imported proof had used without a node.

For delivery-errors B–E, I checked that every statement introduces its objects, every cited node supplies the exact fact used, no clause was moved wholesale into a helper, and the hypotheses are retained. Small edge cases include `Y=\\varnothing`, the zero coefficient object, `E=\\mathbf Q_\\ell` (ramification index one), and unramified/ramified finite extensions; all reduce to the stated towers and finite-sum arguments. No Lean source or compiler was modified or run.

## What remains unfinished

The helper is intentionally statement-only and joins the later DAG queue. This is stage 1 only; no Lean proof work is part of this delivery. The second reader should review and deliver this dry-run-accepted split.


## Second reading by Q38

This independent reading supersedes the first worker's delivery inventory and the helper discussion above; those sections, including `## Review by Q38`, are preserved as requested. The final delivery has **zero new nodes and zero Mathlib leaves**, and five proof steps.

- Item statement: compared all three clauses with `main-20261015/.../sk-prop-diagonal-tower-coefficients.md`, and the standing hypotheses with `sk-def-sfb-dc-setting`; verdict: exact source text retained, standing-setting and coefficient definition dependencies added. No statement dispute or weaker assertion was needed.
- Step 1, integral coefficients: read the statements of `sk-prop-sfb-cartesian-coefficients` (2), `det-prop-sfb-qlbar-colimit-x-integral-limit` (3), `det-prop-diagonal-tower-limit` (3), `det-prop-diagonal-tower-trace` (1),(2), `sk-lem-geo-cartier`, and `sk-lem-geo-p1-cohomology`, against blueprint proof (1); verdict: corrected the unsupported claim that direct image is computed by finite sums and cones. The finite-free basis makes its canonical comparison an identity on finite biproducts. Wrote the additional reduction from a sufficiently large ell-power quotient to every uniformizer-power quotient; cofinality alone only named a subsystem.
- Step 2, rational coefficients: read `sk-prop-sfb-qlbar-colimit-x`, `det-lem-bounded-continuity-direct-image`, and `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact` against blueprint proof (2); verdict: retained the colimit route, made the common bound explicit (at least degree -2), and verified qcqs for all three projective-line projections directly by their two standard affine charts, affine overlap, and diagonal equation. Every colimit comparison is checked in every cohomological degree before preserving the identities.
- Step 3, Cartier/Kummer systems: read `det-prop-diagonal-tower-system`, `sk-lem-geo-cartier` and its current blueprint source, `det-pe-topos-functoriality-inverse-image` (4),(5), and `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` against blueprint proof (3), first sentence; verdict: wrote the unit/local-generator map, the relation on changing the Cartier equation, and the transition maps of the two-term free resolutions. This proves one commuting system diagram and does not infer equality of derived system morphisms from levelwise equality. The map on multiplicative sheaves is explicitly a natural map, not an assumed isomorphism.
- Step 4, specified derived limits: read `lem-weil-pbc-proetale-abelian-closed-support`, `det-pe-topos-functoriality-inverse-image` (2),(5), `det-prop-diagonal-tower-limit` (1),(2), and `sk-prop-sfb-cartesian-coefficients` (1) against blueprint proof (3), comparison paragraph; verdict: derived closed base change in three explicit operations (zero complementary restriction; closed counit after restriction to the support; closed-support unit). Checked the quasi-compact complement on the actual Cartier charts. The limit comparison is established only on the supported constant and twisted coefficient systems occurring as endpoints, with no preservation claim for arbitrary inverse systems.
- Step 5, traces and remaining coefficients: read `lem-weil-pbc-finite-type-over-noetherian`, `sk-lem-geo-p1-cohomology`, `det-prop-diagonal-tower-trace` (1), `det-prop-diagonal-tower-limit` (1), `sk-prop-sfb-cartesian-coefficients` (1), `det-pe-topos-functoriality-inverse-image` (3),(4), `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, and `det-prop-sfb-qlbar-colimit-x-pullback` against blueprint proof (3), last sentences; verdict: checked Noetherian hypotheses, wrote the unit/section decomposition comparison, its inverse and summand projection, and applied it also with base P and morphism P' to P for each projection. Tensor and colimit comparisons then give each scalar stage.
- New node `lem-six-diagonal-tower-pullback`: opened its statement and source paragraph and searched the whole DAG and blueprint for Cartier, closed-support, pullback, and inverse-system facts; verdict: **deleted**. It bundled the finite-level naturality, the limit comparison, and almost the complete integral base-change clause into an unsplit helper, contrary to D1/D2. Existing statements and the explicit diagrams in steps 3-5 supply the needed argument. No replacement helper is introduced; B1-B7 are therefore vacuous for the final inventory.

Sources additionally opened: `literature/stacks-project/proetale.tex`, Tag 09AA (`lemma-closed-immersion`, lines 4945 onward) and Tag 09AH (`lemma-ses-associated-to-open`, lines 5138 onward), for the actual closed unit/counit used in step 4; `sites-cohomology.tex`, Tags 0G7E (`lemma-pullback-K-flat`) and 07A4 (`lemma-pullback-tensor-product`), for the K-flat tensor comparison used in steps 3 and 5. No SGA source is used. The chapter and unit records and the current unit `_section.md` were read without changing them.

Small cases checked: empty Y or Y' gives the zero sheaf diagrams; g equal to the identity makes each comparison the identity; zero input objects are preserved by all additive functors; n and m start at 1 (no nonexistent level-zero class is used); E equal to Q_l gives rank and ramification index one; ramified E with e greater than one requires the explicit further quotient in step 1, which now covers m not divisible by e. Over a field and even a nonreduced base ring, the diagonal equation a-b and section equation t remain nonzerodivisors, so nonflat g is allowed and was not silently excluded.

Independent Mathlib searches were actually run with msearch.py and remain in `searches.jsonl`: LeanFinder query “Exact inverse image functor on sheaves preserves a compatible system of finite constant sheaves and Tate twists under change of scheme” returned eight generic condensed-sheaf declarations, none a diagonal-class theorem; grep query `Cartier|Kummer|derived.*[Ll]imit` in AlgebraicGeometry returned zero hits. The read-only slopmaster2 and upstream master searches found no exact completed diagonal-tower declaration; master sorry declarations were not used as proofs.

Changes: removed the bundled helper; expanded base change to three explicit proof steps; corrected finite-biproduct direct-image reasoning; explained all uniformizer reductions; added the standing definition dependencies and the exact statement citations used by the repaired proof. `citations.json` was regenerated as 25 full, verbatim statement quotes for the five steps. First-worker sections are retained above for history; their claimed helper inventory and three-step count are superseded by this section. No Lean file, compiler, Lake, build, live repository, or launcher script was modified.


Final citation audit also added exact filtered colimits on the underlying abelian sheaves in step 2, so continuity gives the derived colimit comparison over a single common coefficient ring.

Validation: the required dry run printed `OK (not pushed) deliver/Q38/det-prop-diagonal-tower-coefficients at cf485db0d5: preflight passed`. The delivery invocation reruns preflight before pushing. The raw dry-run output is retained in `second-reading-dry-run.log` in the sandbox.
