# ClosedTestDerivedExchangeModel affine specialization

## Reason

The existing theorem
`AlgebraicGeometry.ProEtale.NonaffineClosedTestExchangeIdentification.nonaffine_closed_test_exchange_identification`
contains the complete conclusion of `closed_test_derived_exchange_model`, with additional
shift-compatibility and closed-immersion assertions. A morphism between affine schemes
is quasi-compact and quasi-separated, so its hypotheses apply directly.

Its module needs only the canonical constructions, not any theorem or coefficient
definition of ClosedTestDerivedExchangeModel. Redirect its import to the existing
ClosedTestDerivedExchangeMaps module, allowing the affine theorem to import and
specialize it. No definition, theorem signature, visibility, attribute or proof in the
nonaffine module changes. No source-library file changes.

With the two original imports, lcompile.py --all diagnosed:
`the modules import one another in a cycle: Sheaf.Paper.ClosedTestDerivedExchangeModel,
Sheaf.Paper.NonaffineClosedTestExchangeIdentification`.
The launcher reported that diagnostic as a missing compile result; the detached error
contains the import-cycle diagnosis. Redirecting the dependency removes this cycle.

## Old

In `Sheaf.Paper.NonaffineClosedTestExchangeIdentification`:

```lean
public import Sheaf.Paper.ClosedTestDerivedExchangeModel
```

The affine theorem had proof `:= by sorry` and no import of the nonaffine theorem module.

## New

In `Sheaf.Paper.NonaffineClosedTestExchangeIdentification`:

```lean
public import Sheaf.Paper.ClosedTestDerivedExchangeMaps
```

In `Sheaf.Paper.ClosedTestDerivedExchangeModel`, a proof-only import is added:

```lean
import Sheaf.Paper.NonaffineClosedTestExchangeIdentification
```

The affine theorem specializes the existing qcqs theorem and projects its first three
normalization conclusions. Its statement is verbatim unchanged. Its two natural
isomorphisms and canonical maps are exactly the ones in the nonaffine theorem, with
no additional hypothesis or transport.

## Users

`tools/downstream.py Sheaf.Paper.NonaffineClosedTestExchangeIdentification` reported
zero downstream modules before this change. A direct import search likewise found none.
The only new direct importer is the item module, compiled in this delivery.
The nonaffine module never names any theorem or coefficient definition from the affine
model module. Its three shift instances, three theorem signatures and theorem bodies
are unchanged. The removed theorem reexports have no existing Lean consumer through
this module. Both modules still obtain all canonical constructions from the same maps
module, with identical declaration names and bodies.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ClosedTestDerivedExchangeModel | A4 | Specializes the qcqs theorem; public signatures and definitions unchanged. |
| Sheaf.Paper.NonaffineClosedTestExchangeIdentification | unclaimed | Redirects one public import to canonical maps; all declarations unchanged. |

No target statement or definition used by a target changes its meaning.

## Status

landed 20261026T080752-L-1570888 2026-10-26 (merge of deliver/A4/Sheaf.Paper.ClosedTestDerivedExchangeModel)

## Companion DAG correction

The nonaffine node formerly cited the aggregate
`lem-sfb-closed-lifted-test-isomorphism-criterion` in proof step 1, explicitly for its
source-independent geometry paragraph only. That aggregate's later exchange implication
uses the affine model, giving a spurious reverse path in the node graph.
The delivered nonaffine node expands exactly the aggregate's first three proof steps
and cites their existing dependencies directly: henselian closed-lift geometry,
w-contractible covers and stability, exact and derived sections, and the
cone/sheaf-separation argument for joint conservativity. No exchange statement is used
in those steps. The remaining nonaffine proof steps and the whole statement are unchanged.
Removed only the obsolete aggregate tool_uses entry; no approval was added or reordered.
This is a dependency-granularity correction, not a new mathematical assertion.
