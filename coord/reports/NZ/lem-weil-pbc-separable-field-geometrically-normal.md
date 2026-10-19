## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-separable-field-geometrically-normal.json`: five-step split; statement unchanged; no exact Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-geometrically-normal-perfect-closure-criterion.json`: statement-only algebraic criterion, Tag 037Z; unsplit, no Mathlib match.
- `citations.json`: verbatim statement quotes for every step citation.

## Attachments

None. Searched the item id, blueprint tag, geometric-normality terminology, and separable-extension terminology in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `dag/lean_names_upstream.json`. No project declaration states the item exactly. Master source is reference material only.

## WANTED

None.

## What was incomplete

The imported item had no proof. Its statement agrees with Tag 0C30, including nonalgebraic separable extensions and arbitrary scalar extensions. Its original searches were retained; I reran the item searches through msearch and recorded actual queries for the new criterion. LeanSearch returned Internal Server Error and is recorded unavailable. The successful searches gave reducedness and field-theoretic Normal APIs, not normal prime localizations.

The first dry run requested duplicate comparisons. I removed the proposed separate perfect-closure field lemma and put that calculation into the item's steps, avoiding a new lemma that would hide the substance of 0C30. A second proposed reducedness lemma was also removed: the existing separably-generated tensor-reduced statement suffices, after the finite-coefficient reduction written in step 2. Only the general algebra criterion remains.

## Not duplicates

lem-weil-pbc-geometrically-normal-perfect-closure-criterion vs lem-weil-pbc-perfect-purely-inseparable-overfield: the latter (046W) constructs the field P; the new statement (037Z) tests normality of an arbitrary algebra after all field extensions using P. Existence is neither assumed as a conclusion nor reproved in the new node.

lem-weil-pbc-geometrically-normal-perfect-closure-criterion vs lem-weil-pbc-normality-perfect-closure-test: the existing scheme statement is an equivalent geometric formulation, but its proof depends on lem-weil-pbc-normal-algebra-separable-scalar-extension, whose proof cites this item, so using it here would create a cycle. The new ring statement gives the independent algebra input of 037Z with a different route: make a finitely generated field extension separable after finite purely inseparable extensions, use smooth ascent, localization and descent, then normal filtered colimits. The future split must follow 037Z and not cite the existing scheme criterion or this item. I searched all DAG statements and the whole blueprint (geometrically normal, perfect closure, 037Z); no other ring criterion node occurs.

## Review by NZ

I read `algebra.tex` Tag 0C30 (`lemma-separable-field-extension-geometrically-normal`), Tag 030U (`lemma-separable-extension-preserves-reducedness`), Tag 046W (`lemma-perfection`), Tag 0BRD (`lemma-radicial-integral-bijective`), and Tag 037Z (`lemma-geometrically-normal`) in full at their labels, and verified tags with `tags/tags`. The new node states precisely the equivalence (4)/(1) of 037Z, using the explicit perfect purely inseparable hypothesis of 046W instead of leaving “perfect closure” undefined. It has no proof or proof dependencies. Its zero-algebra case is valid: normality is vacuous on an empty prime spectrum. No finite type, Noetherian, domain or nonzero condition was added.

Step 1 cites the actual existing perfect-overfield statement, which supplies both the power condition and perfectness, in characteristic zero and positive characteristic. Step 2 opens and uses the existing `lem-weil-pbc-separably-generated-tensor-reduced`: its assumption is met only after taking the finitely generated field F of the finite tensor coefficients and using the item's separability hypothesis. P is a field, hence reduced. I opened `lem-weil-pbc-module-over-field-flat` and `def-weil-pbc-flat-ring-map`; together they assert exactly injectivity after tensoring the inclusion F into K. The tensor definition supplies finite expressions. Injectivity ensures the nilpotence equation holds already in F tensor P, so no colimit theorem is tacitly assumed.

Step 3 uses only the power property already obtained in step 1 and the binomial formula, with the divisibility of interior binomial coefficients explicitly explained. A common exponent is chosen for finitely many coefficients. In characteristic zero q=1 forces P=k. Step 4 uses the existing vector-space basis assertion (part of the statement of `lem-weil-pbc-module-over-field-flat`) to build a retraction of K into the tensor. It then writes an explicit inverse for each nonzero element using its nonzero power in K; reducedness is essential here and has been proved. No unique-prime, lying-over or fieldness lemma is left implicit. Step 5 uses the normal-ring definition for the resulting field, the actual new criterion for arbitrary E, and the explicit tensor-swap maps. Ring isomorphisms preserve prime localization and monic equations, as explained in the step.

I checked the item when K=k, when k has characteristic zero, when K is transcendental such as k(t), and when P is an infinite perfect closure in positive characteristic. None requires algebraicity of K, finite degree of P, or finite generation of E. By contrast the existing `lem-weil-pbc-separable-tensor-purely-inseparable-field` assumes algebraicity and finiteness, so it is not used. `lem-weil-pbc-geometrically-reduced-extension-separable` states the reverse implication and is not misused. The preserved blueprint route is the second paragraph of the normalization exact sequence: normality after extension. The proposed new nodes that just hid the field calculation were removed after self-review.

## What could not be finished

No mathematical part of this one-level split remains unfinished. The new 037Z input is deliberately left statement-only for a later worker. No Lean writing, compiler or Lake command was run. `check_dag.py --cycles` on the read-only repository returned success; the standalone `review_split.py` failed because its configured live-DAG path is outside its root, so validation of the sandbox is delegated to the required delivery dry run, which sets the branch DAG path correctly.

The final metadata check inserted the item itself at the front of the new node’s blueprint.from.via, retaining the existing ancestor chain, and named the precise second-paragraph sentence served. The delivery dry run is repeated after this correction.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against Stacks algebra.tex Tag 0C30, label `lemma-separable-field-extension-geometrically-normal`; field, separability, arbitrary scalar extension, and normal-ring clauses agree, with no finiteness or algebraicity added.
- New node `lem-weil-pbc-geometrically-normal-perfect-closure-criterion`: checked against Tag 037Z (`lemma-geometrically-normal`) and Tag 046W (`lemma-perfection`); its criterion and explicit perfect purely inseparable hypotheses match, including the zero-algebra edge case.
- Step 1: checked the perfect-overfield existence statement against Tag 046W and its cited node; the power condition and perfectness are supplied.
- Step 2: checked finite tensor expressions, finitely generated separable subextension, reducedness, and tensor-injection claims against each cited definition and lemma; flatness applies over the field base.
- Step 3: checked the Frobenius/binomial calculation in characteristic zero and positive characteristic; one common exponent handles all finitely many coefficients.
- Step 4: checked the vector-space retraction and explicit nonzero-power inverse; reducedness is used exactly to preserve nonzeroness.
- Step 5: checked normality and the tensor-swap identification against the normal-ring definition and Tag 037Z; localization and integral-closure invariance are stated.
- Existing-node searches: checked cited DAG tags and terminology with repository grep and the recorded LeanFinder/Loogle searches; no duplicate algebra criterion was found, and the scheme criterion cycle is avoided.
- Small cases: checked $K=k$, characteristic zero, $K=k(t)$, infinite perfect closures in positive characteristic, and the zero algebra; all remain valid.
- Changes made: none to mathematics or node statements; verified citations, search records, blueprint metadata, and delivery preflight after the worker's duplicate-node removals.

## Returned-delivery metadata repair

The return requested `created.by` and `created.date` on `lem-weil-pbc-geometrically-normal-perfect-closure-criterion` (Stage 1 §2, A4/B9). On inspecting this sandbox, both fields were already present. I explicitly normalized and saved them as `by: "worker"` and `date: "2026-10-14"`, retained `item: "lem-weil-pbc-separable-field-geometrically-normal"`, and verified that the complete created record meets the required form. The mathematics, cited statements, source checks and searches passed the maintainer review and are unchanged. The required no-push dry run is rerun on this saved version.

## Second reading by NZ

- Item statement: compared every hypothesis and conclusion with algebra.tex Tag 0C30, `lemma-separable-field-extension-geometrically-normal`, and separability Definition 030O; agrees for nonalgebraic separable extensions and arbitrary scalar extensions. Tested $K=k$, $K=k(t)$, characteristic zero, and positive characteristic with an infinite perfect closure; no statement dispute.
- Step 1: read the statement of `lem-weil-pbc-perfect-purely-inseparable-overfield` and algebra.tex Tag 046W, `lemma-perfection`; it supplies exactly the perfect field and elementwise power property used, without finite-degree assumptions. Pass.
- Step 2: read `def-weil-pbc-module-tensor-product`, `def-weil-pbc-separable-field-extension`, `lem-weil-pbc-separably-generated-tensor-reduced`, `lem-weil-pbc-module-over-field-flat`, and `def-weil-pbc-flat-ring-map`, and Tag 030U, `lemma-separable-extension-preserves-reducedness`; finite coefficients give a separably generated subfield, and flatness makes its tensor inclusion injective. Added the elementary proof that the field P is reduced. Pass, including the empty tensor sum and nilpotence exponent 1.
- Step 3: checked the power calculation against the purely inseparable hypothesis of step 1 and the binomial identity; made explicit why enlarging the finitely many exponents keeps the powers in k. Pass for n=0, q=1, and p>0; no non-elementary input is hidden.
- Step 4: read the basis assertion in `lem-weil-pbc-module-over-field-flat` and the tensor universal property in `def-weil-pbc-module-tensor-product`; replaced extension of the vector 1 to a basis by a coordinate functional on an already supplied basis, divided by a nonzero coefficient of 1. The retraction is now obtained explicitly from the cited universal property. Reducedness and the displayed inverse prove fieldness for every positive q^n, including q^n=1. Pass.
- Step 5: read `def-weil-pbc-normal-ring`, the new criterion, and Tag 037Z, `lemma-geometrically-normal`, equivalence (4)/(1); the criterion applies with A=K and P as chosen, with no Noetherian or finite-type premise. Added the tensor definition citation and explained that the swap respects multiplication on pure tensors. Prime-localization normality is preserved by the described ring isomorphisms. Pass.
- New node `lem-weil-pbc-geometrically-normal-perfect-closure-criterion`: compared each clause with Tag 037Z, `lemma-geometrically-normal`, and the perfect-closure hypotheses with Tag 046W, `lemma-perfection`. It is a self-contained, statement-only general algebra input with definition citations, single-escaped TeX, and exact tags/labels; the zero algebra has no primes and satisfies both clauses. It is neither elementary nor a restatement of 0C30. Read the existing scheme criterion `lem-weil-pbc-normality-perfect-closure-test`: its dependency `lem-weil-pbc-normal-algebra-separable-scalar-extension` depends on this item, so reusing it would make a cycle. The independent ring criterion is retained; its eventual proof must use the 037Z route without that scheme criterion or this item.
- Searches and route: independently searched DAG tags 037Z/0C30 and perfect-closure/geometric-normality wording, the entire blueprint via `blueprint_refs.py search`, and slopmaster2 by the item id and terminology; no other independent ring criterion or finished attachment found. Ran fresh LeanFinder, Loogle and grep queries in Mathlib vocabulary through msearch and recorded their actual outputs. Read `TensorProduct.toIntegralClosure_bijective_of_tower` at Mathlib/RingTheory/Smooth/IntegralClosure.lean:59: its two bijectivity assumptions and conditional composition conclusion do not state this criterion. Other hits concern integral extensions or geometric reducedness. No Mathlib leaf gained. Checked the normalization exact sequence's second paragraph and sk-thm-p1: the normality input preserves their route.

Changes made: strengthened the explanations in steps 2–5 without changing any statement; added tensor-definition citations to steps 4 and 5 and their verbatim quotes in citations.json; recorded three independent second-reader Mathlib searches on the new node. Verified every citation quote against the actual cited node statement and exact per-step coverage. Retained all first-worker sections, including `## Review by NZ`.
