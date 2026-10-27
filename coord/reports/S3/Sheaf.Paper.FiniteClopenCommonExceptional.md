## What changed

Replaced the sole sorry in `Sheaf.Paper.FiniteClopenCommonExceptional` by an assembly
proof. The singleton identity partition supplies an identity record even when the
assigned index type is empty. The existing `finiteClopenExceptionalRestriction`
supplies the initial component records.

Proved the private `coefficient_rebase` calculation. It synchronizes both base-field
functors using integral right-adjoint uniqueness and the proved raw scalar-localization
component-isomorphism API. The integral formula, limit restriction, integral comparison
and rational comparison are transported explicitly. The inverse-limit equation follows
from functoriality; the rational comparison equation uses the recorded pure-tensor
pullback formula and heterogeneous composition. All other coherence conjuncts are
retained. This calculation works for any finite coefficient field and any clopen
inclusion with the stated geometry.

The separate common-stage action synchronization is isolated as
`clopenExceptional_action_transport` in `Sheaf.Paper.ClopenExceptionalActionTransport`.
It assumes existing identity/component comparison records and changes only their
common-stage part, keeping the supplied base record. After that step, the proved
base-field transport gives the other two equalities, without changing any stage or
action coherence field. The public statement and public imports of the assigned module
are unchanged; the three added imports are proof imports. No other existing module
is changed.

## Proved and sorry left

Original holes: 1, in
`WeilConjectures.PurityFiniteSetting.finiteClopen_common_exceptional`.
Its proof is now complete relative to the imported theorems.

Added holes: 1, in
`WeilConjectures.PurityFiniteSetting.clopenExceptional_action_transport`, node
`lem-pur-clopen-exceptional-action-transport`. This is the entire remaining common-stage
synchronization step. Its statement assumes the initial records, does not construct a
partition or an initial identity record, and does not synchronize either base-field
functor. It is strictly the third coefficient-stage obligation, rather than the original
three-equality theorem under another name.

Thus this is a decomposition with one original hole closed and one strictly smaller
hole added, net zero; it is not a claim of an axiom-free proof of the original theorem.
There are no sorries in the assigned module and no other newly added holes. The private
helpers `rationalSupport_additive` and `coefficient_rebase` are fully proved. Existing
imported holes, including `finiteClopenExceptionalRestriction`, are unchanged.

Edge cases: the identity comparison uses a singleton partition independently of the
original index type; no inhabitant of that type is selected. Empty components are
allowed throughout the transport statements. The new action lemma also includes the
identity inclusion; its base-record equality can be satisfied independently because
the all-coefficients coherence predicate does not mention that field.

## No longer needed

No imports were removed, and no module is globally pruned. The assigned module's
original low-level construction dependencies are no longer used directly:

- `lem-pur-clopen-strict-system-support` / `Sheaf.Paper.ClopenStrictSystemSupport`;
- `lem-pur-etale-coefficient-system-adjoint` / `Sheaf.Paper.EtaleCoefficientSystemAdjoint`;
- `lem-pur-clopen-counit-adjoint-comparison` / `Sheaf.Paper.ClopenCounitAdjointComparison`;
- `lem-pur-clopen-system-integral-realization` / `Sheaf.Paper.ClopenSystemIntegralRealization`;
- `def-weil-exceptional-inverse-image` /
  `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`;
- `lem-pur-clopen-exceptional-scalar-descent` / `Sheaf.Paper.ClopenExceptionalScalarDescent`;
- `lem-weil-pbc-mate-pasting` / Mathlib's adjunction mate lemmas.

They remain needed through the initial restriction theorem, the comparison definitions,
or the new action-transport proof plan. The direct proof now uses the existing initial
restriction theorem, adjoint uniqueness, scalar-localized component isomorphisms,
the finite/rational pullback specifications, the comparison definitions and the new
common-stage transport statement. No blueprint unit or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement was found false, and no existing signature or definition was changed.
The existing restriction theorem gives separately chosen records, not equality of their
global functors. Consequently it cannot alone justify the simultaneous choices in the
original proof plan. Base integral/rational synchronization is now an explicit checked
calculation; prescribed common-stage action transport remains the named smaller task.
The newest blueprint section-invariant file contains the invertibility assertion only;
the detailed argument used here is retained in the restriction theorem's proof docstring
(steps 8–10) and in the assigned node's simultaneous-choice proof plan.

## New nodes

`lem-pur-clopen-exceptional-action-transport` records transport of only the common-stage
part of an already existing normalized clopen comparison to a fixed identity record's
action, preserving its independent base record. Its new module contains one public
named theorem with the complete source proof plan in its docstring. Actual LeanFinder,
Loogle and Mathlib grep searches are recorded in its node. The assigned node's proof,
proof dependencies and proof origin now describe the Lean assembly and the proved
base-field transport. There are no change records because no other existing module,
statement or definition was modified.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ClopenExceptionalActionTransport": "8031293ed4b738e58f0ce6dcfc42f8154403476a", "Sheaf.Paper.FiniteClopenCommonExceptional": "95c785e1136c66cfd8668bf9005696aa5a4cc06a"}, "results": {"Sheaf.Paper.VaryingDimensionDualizingInverse": {"hash": "b76346912b6b41dc747a104b368dfa3b09ca165a", "status": "OK"}}, "seconds": 43, "time": "2026-10-28T03:30:37+0800", "transitive": 0, "version": 1}
```

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
