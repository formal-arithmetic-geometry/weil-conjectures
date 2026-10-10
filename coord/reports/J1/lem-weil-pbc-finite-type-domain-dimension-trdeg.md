# Worker report: lem-weil-pbc-finite-type-domain-dimension-trdeg

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-type-domain-dimension-trdeg.json`: split Stacks Algebra Lemma 00P0 into four proof steps; no change to its statement or statement dependencies.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-integral-injective-dimension-equal.json`: new unsplit statement for Stacks Algebra Lemma 00OK, integral injective extensions preserve Krull dimension. LeanSearch, LeanFinder, Loogle and Mathlib source grep found no general matching theorem. The dimension-at-most-one and polynomial-ring results are narrower.

## Attachments

`ringKrullDim_eq_of_isIntegral` belongs to `lem-weil-pbc-integral-injective-dimension-equal` (`/home/ubuntu/weil-src-slopmaster2/WeilConjectures/Mathlib/RingTheory/Ideal/HasGoingUp.lean:28`). Its hypotheses `Algebra.IsIntegral R S` and `FaithfulSMul R S` encode an integral, injective algebra map, and its conclusion is equality of the two Krull dimensions. The declaration has no visible `sorry`; L must check its transitive dependencies against a refreshed sorry map, since the committed map predates this source checkout. The 00P0 item has no exact Lean declaration: `Algebra.trdeg_eq_of_ringKrullDim_eq` (`WeilConjectures/Mathlib/RingTheory/NoetherNormalization.lean:355`) proves its core equality given finite dimension, but does not state the fraction-field and maximal-local-ring clauses.

## Wanted

None. The Stacks Project source is available locally.

## Source and blueprint checks

Stacks `algebra.tex` Lemma 00P0 (label `lemma-dimension-prime-polynomial-ring`, lines 28177-28200) gives the exact statement. Its local-dimension sentence invokes Lemma 00OR; the split cites the existing 00OS node, which derives the required consequence from 00OR. Its normalization step invokes Lemma 00OY. The proof then says that the fraction field is finite over the rational function field in the normalization coordinates. The split expands this by localizing the finite polynomial-module algebra, using the existing finite-dimensional-domain-is-field node, and applying the transcendence-basis definition.

The proof cites `lem-weil-pbc-finite-type-domain-dimension-local-ring`, `lem-weil-pbc-noether-normalization-field`, `lem-weil-pbc-finite-algebra-is-integral`, `lem-weil-pbc-integral-injective-dimension-equal`, `lem-weil-pbc-polynomial-ring-maximal-localization-dimension`, `lem-weil-pbc-finite-dimensional-domain-is-field`, `def-weil-pbc-transcendence-basis`, and `def-kun-transcendence-degree`. The 00OK result supplies the dimension clause omitted by the current Mathlib Noether-normalization theorem; the polynomial-ring dimension follows from the existing maximal-localization calculation together with 00OS. Stacks 00OK explicitly cites 00GU, 00GQ, 00OI and 00OJ in its proof; its own proof remains for a later split.

The item's existing LeanSearch, LeanFinder, Loogle and Mathlib grep records found no exact 00P0 match. The newly available project source changes the verdict for 00OK: its `ringKrullDim_eq_of_isIntegral` is an exact attachment even though the earlier Mathlib searches found no match. Whole-blueprint searches by finite-type domain, fraction-field transcendence degree and integral-extension dimension found no blueprint node stating either full assertion. Both nodes have `blueprint.same_as = []` and trace through the dimension-at-point branch to step 7 of `thm-weil-pbc-finite-etale-lifting` (Lemma 0GS2). The item's `split_report.blueprint` records the four source steps.

## Checks and remaining work

`python3 tools/review_split.py lem-weil-pbc-finite-type-domain-dimension-trdeg` passes with one new node. The local checkout predates `tools/blueprint_refs.py`; the required B9 fields were checked against the schema in `origin/sheaf-dag:tools/blueprint_refs.py` and parsed with `jq`. `python3 tools/check_dag.py` found no cycles or route errors for this item, but exits nonzero for seven pre-existing unreachable nodes elsewhere. No Lean was written or compiled. The new 00OK node remains unsplit.

## Review by J1

I read Algebra Lemmas 00P0, 00OY, 00OS, 00OR and 00OK in `algebra.tex` and checked the item against them. The statement includes both the fraction-field transcendence degree and the maximal-local-ring clause. Step 1 cites the existing 00OS node for the local dimension consequence of 00OR. Step 2 uses the exact Noether normalization node to obtain a finite injective polynomial subalgebra, the finite-implies-integral node and the new 00OK node to identify dimensions, and the polynomial maximal-localization node to compute `d`. Step 3 explicitly localizes the finite module, then applies the cited finite-dimensional-domain-is-field statement to show the resulting algebra is the fraction field. Step 4 uses the two cited definitions to conclude that the normalization coordinates are a transcendence basis. The field case `d=0` and the polynomial ring case check the endpoints; the domain hypothesis is used in the field argument.

The new 00OK node agrees with Stacks 00OK for an injective integral map, states its objects independently, has no proof steps while unsplit, and has its B9 provenance and searches. I searched the current DAG for 00OK and integral-extension dimension equality before accepting its new id. The read-only Lean source audit found the exact declaration above; I leave attachment and closure to L's sorry-map verification. I checked A-F of `coord/delivery-errors.md`: each non-elementary step uses a node whose statement supplies the fact, the route stays within the unit's proof and generic tools, and no unstated Noetherian hypothesis is used. The worker corrected the source citation from 00OS to 00OR as the source's direct reference; no further proof change was needed.
