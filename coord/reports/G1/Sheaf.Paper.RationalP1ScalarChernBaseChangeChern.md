## What changed

The parent Chern exchange theorem now performs a real case split on its option-valued
coefficient and invokes one concrete component theorem in each branch. Added the
`Some` and `None` coefficient modules, each carrying the same hypotheses with a fixed
coefficient choice and one remaining geometric exchange obligation. The specialized
statements retain only the coefficient, Chern arrows, pullback, and exchange map needed
for that equation; the parent’s unused unit and twisted-line lets are absent from
them. Updated the parent DAG node to record the case-assembly proof and added matching DAG nodes for both
specializations.

## Proved and sorry left

Closed the parent declaration `scalar_chern_base_change_chern` by exact case assembly.
The following strictly specialized declarations remain as split obligations:

- `scalar_chern_base_change_chern_some`, node
  `lem-sfb-rational-p1-scalar-chern-base-change-chern-some`.
- `scalar_chern_base_change_chern_none`, node
  `lem-sfb-rational-p1-scalar-chern-base-change-chern-none`.

No `sorry` was added to a definition.

The split covers exactly the two constructors of `Option`: a supplied finite
intermediate field and the closure coefficient. Empty schemes, zero Chern arrows, and
identity coefficient comparisons reduce each branch to the same displayed composition;
no branch adds a nonemptiness, invertibility, or normalization hypothesis.

## No longer needed

None. The original geometric dependency route remains attached to the two concrete
coefficient obligations; the parent proof uses only those two new declarations.

## Where the brief, the DAG or earlier work was wrong

The available declarations expose the normalized q and p2 Chern arrows independently,
without a theorem relating them through `secondTraceExchange`. The prior parent
component was therefore too general to close directly from the published interfaces.
The option case split is the strict finite decomposition needed before the remaining
geometric proofs can proceed.

The generic ordinary-finite projective-line Chern base-change theorem was also checked,
but its arrows live in ordinary finite-etale module categories and cannot typecheck
against these condensed coefficient arrows; it therefore does not close either branch.

## New nodes

`lem-sfb-rational-p1-scalar-chern-base-change-chern-some` records the finite
intermediate-field coefficient case. `lem-sfb-rational-p1-scalar-chern-base-change-chern-none`
records the closure coefficient case. Each node has its own module and declaration.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RationalP1ScalarChernBaseChangeChern": "936cced537a8dd8e385d27b4e21513a4fab546a0", "Sheaf.Paper.RationalP1ScalarChernBaseChangeChernNone": "00d2e13080d6079840b6a092598671c214bb65de", "Sheaf.Paper.RationalP1ScalarChernBaseChangeChernSome": "24b2fe8b0192054be5ff78a2f1ca728cf9ef835b"}, "results": {}, "time": "2026-10-28T05:51:00+0800", "transitive": 0, "version": 1}
```

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
