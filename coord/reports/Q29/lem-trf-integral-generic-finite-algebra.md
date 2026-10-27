## Files written

- `dag/nodes/sec-trace-formula/lem-trf-integral-generic-finite-algebra.json`: existing statement, now split into five steps; no exact Mathlib match. Statement retained verbatim.
- `citations.json`: one verbatim statement quotation for every cited node in each proof step.
- `report.md`: this report. `searches.jsonl` is maintained by the required search command.

No new nodes; no new Mathlib leaves. No unit record changed: this is not the unit's key node.

## Attachments

No exact attachment for the item. Searched the live `lean/WeilConjectures/` for the blueprint id and integral/generic/rank/finite-normalization language, and inspected the closest finite-normalization theorem. `Algebra.FiniteType.finite_integralClosure` belongs to the existing node `lem-weil-pbc-finite-type-field-integral-closure-finite`; its statement is about integral closure in one finite field extension, not the arbitrary algebra S of this item. It is reused, not reattached or recreated.

## WANTED

None. All mathematical ingredients used here are available in `literature/stacks-project/algebra.tex` and in existing DAG statements.

## What was wrong or incomplete

The item's statement is correct; no STATEMENT-DISPUTED correction is needed. Its proof and dependency list were empty. The source description named the right broad ingredients but supplied no assembly, and it did not separately name Hilbert's basis theorem. The split supplies that theorem through the existing `lem-wf-affine-noetherian-components` and spells out localization injectivity, reducedness, finiteness of each field factor, preservation of a monic equation under the component maps, coordinate generators for the product, and lifting generators from the image.

The newest blueprint `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md` and its proof use the contracting-correspondence route; neither asserts this algebra lemma. The item's existing blueprint provenance expressly records a historical analytic input through the canonical-reduction normalization chain. That provenance is retained. This below-node commutative algebra split changes neither the unit statement nor its contracting-correspondence proof route. Whole-blueprint searches for `integral generic`, `torsion free reduced`, `finite generic`, `finite normalization`, and `reduced Artinian` found no exact blueprint statement for this item; returned curve normalization statements have additional geometric conclusions and do not state this algebra lemma. Thus `same_as` remains empty.

## Not duplicates

No new nodes are proposed. Searches of the whole DAG for Tags 00J6, 00JB, 0335 and 00IK located the existing decomposition, normalization and submodule nodes; these are cited instead of duplicated. The finite-type-field normalization theorem is only one ingredient, not a restatement of this item.

## Mathlib search assessment

Ran the required command for LeanFinder, Loogle, grep in RingTheory, and LeanSearch, and then a second LeanFinder phrasing. Read the actual returned hits and the source of the closest candidates. All services answered. The finite-type integral-algebra theorem `Algebra.IsIntegral.finite` at `Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:96` requires finite type of S, which is absent here. `RingHom.IsIntegral.to_finite` has the same restriction. `IsIntegralClosure.finite` at `Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean:175` requires normality and separability (read with its surrounding assumptions), and is not a theorem about arbitrary reduced integral algebras. The generic-fibre quasi-finiteness hits require finite type too. The true arbitrary-finite-extension normalization theorem is in the project, at `lean/WeilConjectures/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean:299`, and is already represented by the cited node. No exact project declaration for the item was found, and Mathlib's results do not supply a one-line specialization.

## Review by Q29

I read delivery-errors B through E, the stage-1 brief, the chapter and unit records, the three-level rule of SETUP.md, GOAL.md, and the latest blueprint statement and proof. For the mathematical source I read algebra.tex at Tags 00J6 (`lemma-finite-dimensional-algebra`), 00J7 (`lemma-artinian-finite-nr-max`), 00JB (`lemma-artinian-finite-length`), 0335 (`proposition-ubiquity-nagata`, especially fields and finite-type extensions), 00FN (`lemma-Noetherian-permanence`), and 00IK (`lemma-Noetherian-basic`). The exact tag-to-label pairs were checked in `tags/tags`. This is an agent assembly of these source results, marked as such, not a claim that Stacks states the assembled item verbatim. There are no new-node sources to audit.

For step 1 I checked both fraction calculations explicitly. Vanishing in the localization gives a nonzero scalar annihilator; torsion-freeness is used before reducedness. This also handles the zero algebra without asserting it is a field or a nonzero domain. No general localization preservation theorem is being silently cited.

For step 2 I opened the full statements of `lem-weil-pbc-finite-dim-algebra-artinian` and `lem-sfb-reduced-artinian-residue-product`. The former needs only a commutative finite-dimensional algebra over a field, which T is. The latter gives the finite maximal spectrum, actual quotient fields, and the canonical product isomorphism, including its formula. It requires reducedness, established in step 1. I did not cite a decomposition definition or a weaker Artinian theorem for the quotient-field conclusion. Each quotient has the Q-vector-space structure induced by a unital map from the field Q; images of a basis of T give its finite spanning family. The product isomorphism is Q-linear since its components are precisely the quotient maps. This establishes every hypothesis needed in step 3.

For step 3 I read `def-weil-pbc-integral-closure` and `lem-weil-pbc-finite-type-field-integral-closure-finite` in full. The definition gives an actual subring containing R, and the theorem gives a finite R-module in every finite extension of Frac(R). R is exactly the finite-type domain in our hypotheses, and each L_i has the compatible R/Q structure from step 2. There is no normality or separability hypothesis in this node's statement or its project Lean declaration. In particular I checked the positive-characteristic purely inseparable case, which would invalidate a shortcut through Mathlib's separable integral-closure theorem.

For step 4 the previously introduced C_i remain the same integral closures. Applying a ring homomorphism to a monic equation preserves its leading coefficient 1, so the image really lies in each C_i. The resulting map is injective by step 1 and the product isomorphism. Coordinate insertions of finite generating sets give an explicitly finite generating family of the product; no tensor exactness, flatness or unproved finiteness theorem is used. Its image is closed under addition and R-scalars by the two formulas written in the step. These few-line arguments are elementary consequences of the preceding steps, not new nodes or disguised clauses of the item.

For step 5 I opened `lem-wf-affine-noetherian-components` and `lem-weil-pbc-noetherian-submodule-finite`. The first explicitly states that a finitely generated field algebra is Noetherian; only that clause is used, not a theorem about a merely locally finite type scheme. The second explicitly states finiteness of every submodule of a finite module over a Noetherian ring. The ambient product C is finite by step 4 and its submodule is N=f(S), so all hypotheses hold. Lifting finite generators of N and using injectivity gives actual generators of S. This is more than a claim that S embeds into a finite module: the required Noetherian assumption has been proved and cited.

I tested S=0, generic fibre zero, R=k with S a finite product of finite fields, a singular finite-type domain R whose normalization is larger than R, and positive-characteristic finite purely inseparable field factors. The same proof handles all. Reducedness and torsion-freeness are not interchanged or weakened. No finite-type hypothesis on S is introduced. All six cited statements were checked against the use; the quotation file contains literal parts of those statements and was checked for substring equality. The elementary steps have no missing black-box uses. Each proof step is under 700 characters; the full assembly is 2704 characters, so there is no long step hiding an auxiliary lemma.

The finite-normalization theorem is a generic tool from another unit. Its use and why the trace-formula unit provides no replacement are recorded in `split_report.tool_uses`. The other statement tools are existing Mathlib leaves. No forbidden SGA source is used. No Lean files were written and no compiler, Lake or build tool was run.

## What remains unfinished

No mathematical part of this one-level split remains. The existing dependency nodes retain their existing statuses; no proof of those nodes is invented in this delivery. Independent maintainer review follows delivery.

## Delivery validation

The first dry run required a longer quotation for the Noetherian-ring clause in step 5. Replaced the short clause with the whole verbatim statement of `lem-wf-affine-noetherian-components`; the mathematical citation and proof were unchanged.
