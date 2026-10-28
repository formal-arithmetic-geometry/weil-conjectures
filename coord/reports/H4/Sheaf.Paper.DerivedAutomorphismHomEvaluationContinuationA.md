## What changed

Proved `WeilConjectures.podRationalClosed_existsUnique` in
`Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA`, preserving its statement.
The parent privately imports two new, fully proved modules:
`Sheaf.Paper.PodRationalClosedExistence` and `Sheaf.Paper.PodRationalClosedUniqueness`.
No existing definition, signature, instance, attribute or public import changes.

The existence proof first derives integral linearity from parameter naturality at
scalar multiples of the identity and the existing integral tensor bilinearity.
It applies `LinearEquiv.baseChange`, transports the endpoints by the specified
rational tensor and Hom object equalities, and proves parameter naturality by
induction on both tensor-product Hom modules. The inverse has precisely the
original pure-tensor normalization. Uniqueness needs only additivity: the inverse
transposes agree on pure tensors, hence on every arrow, and partial-closed-data
extensionality identifies the structures. The parent combines these two results.
The existing parent node's final proof step and dependencies record this route.

All three files compiled together in import order through `lcompile.py`: existence
23.7 s, uniqueness 5.8 s, parent 4.9 s. Subsequent edits only clarified source
citations in the two new docstrings; the delivery recompiles the final files.
The argument is generic in linear categories: it uses no cancellation,
nonvanishing, finite-dimensionality of Hom modules, or extra invertibility
assumption. Zero and torsion Hom modules obey the same tensor induction, and the
original admissible-pair restriction is preserved.

## Proved and sorry left

Closed 1 of the item's 6 initial holes:
`WeilConjectures.podRationalClosed_existsUnique`.
Added 0 holes; this is a proof, not a decomposition into unproved statements.
The new helper theorems `WeilConjectures.podRationalClosed_exists` and
`WeilConjectures.podRationalClosed_unique`, including all their private helpers,
are fully proved.

Five existing holes remain unchanged, all under
`lem-pod-derived-automorphism-hom-evaluation`:

- `WeilConjectures.podRationalHomComparison_laws`;
- `WeilConjectures.podCommonClosed_existsUnique`;
- `WeilConjectures.podCommonHomComparison_laws`;
- `WeilConjectures.podOrdinaryLimitReindexing_existsUnique`;
- `WeilConjectures.podLimitReindexing_existsUnique`.

## No longer needed

No existing import, node or module is withdrawn. No imports were removed.
The rational closed normalization is proved directly from the integral datum,
the already proved rational operation normalizations and scalar localization;
it does not need the coefficient-descent lemma's separate rational currying
construction. The coefficient-descent module remains needed by other parts of
the item, so this does not prune that whole dependency or any unit step.
The new modules contain only imports used by their statements or proofs.

## Where the brief, the DAG or earlier work was wrong

The shared queue snapshot lists 8 holes; the current server queue and source
have 6 before this delivery. The source already contains the earlier ordinary
finite-restriction and system-Hom proofs; this delivery claims neither as new.
There is no current rework row or build-error record for this item.

The inherited node cites an older blueprint path and a longer enhanced proof.
The current blueprint is under `sk-thm-frobenius` and has five proof steps;
its coefficient transport assertion is Step 5. The current coefficient-operations
text uses a newer presentation. This delivery preserves the exact assigned
scalar-localization statement and records its explicit algebraic refinement;
it does not change coefficient definitions or claim a new statement review.

## New nodes

`lem-pod-rational-closed-existence`, attached to
`WeilConjectures.podRationalClosed_exists` in
`Sheaf.Paper.PodRationalClosedExistence`, records linear base change of the
integral transpose, arbitrary-arrow naturality and the inverse normalization.
It is completely proved and introduces no new obligation.

`lem-pod-rational-closed-uniqueness`, attached to
`WeilConjectures.podRationalClosed_unique` in
`Sheaf.Paper.PodRationalClosedUniqueness`, records tensor-product induction on
the inverse additive transposes and partial-closed-data extensionality.
It is completely proved and introduces no new obligation.

Both new nodes cite the coefficient-transport step and Stacks Tag 08J9 as their
source context, with the localization argument explicitly agent-formulated.
LeanSearch, Loogle, LeanFinder and Mathlib-source searches are recorded.
No change record is needed: all existing statements and definitions are unchanged.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA": "2262c021414d20e2b1ab6256e69e66f0a40b74fc", "Sheaf.Paper.PodRationalClosedExistence": "d79739eedfd283332d0445676a95dfcbcd3d9f06", "Sheaf.Paper.PodRationalClosedUniqueness": "507e9fc98f0232d6ff76a494ca51ffea629c56a0"}, "results": {}, "time": "2026-10-28T10:30:11+0800", "transitive": 0, "version": 1}
```

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
