# completedRootProjection_linear proof context

## Reason

The proof reconstructs section rings for a finite coefficient module and compares
its cyclic scalar action with the normalized completed action. All new declarations
are private and proved. The public theorem signature and public import are unchanged.
This record documents local proof context for the stage-3 preflight.

## Old

The original module uses this local proof context:

```lean
attribute [local irreducible] upperStarFromPoint
  Scheme.purTwistZlCompletionOfUniverses
  InternalAbelianSheafModule.sectionModuleEquivalenceCore
```

Its only public declaration is completedRootProjection_linear, whose original
signature is retained verbatim in the delivered module and its node's lean.statement.
Its public import is Sheaf.Paper.DiagonalCoefficientMaps.

## New

The original context and public import remain. The added local attributes are:

```lean
attribute [local irreducible] constantPresentation
attribute [local irreducible] projectionConstantRingIso projectionConstantMonIso
  projectionRingSectionsIso
```

The main theorem also has this declaration-scoped instance selection:

```lean
attribute [-instance] WeilConjectures.SixFunctors.integralModel_coefficientMonObj in
```

This selects the canonical inverse-image monoid instance used by the section-module
API. The generic imported coefficient-monoid instance is definitionally the same
structure but blocks synthesis of its commutativity. It is restored immediately
after this theorem. A private local finitePointCommMon proves commutativity of the
existing finite continuous-function ring; it changes no ring data. The new private
section-ring and constant-comparison definitions are actual functor and isomorphism
constructions, without postponed proofs or chosen arbitrary data. No existing global
attribute or definition is modified. All proof imports are private.

## Users

The read-only downstream.py query for completedRootProjection_linear lists these
uses. No other existing declaration or interface changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedRootProjectionLinear | V3 | Completes its single theorem proof with private helpers and local proof context. |
| Sheaf.Paper.CompletedCoefficientRootLineComparison | unclaimed | Uses the same theorem signature; no source edit or adaptation. |

The delivery has no shared-definition change and needs no forced consumer adaptation.
Validation is recorded in report.md.

## Status

landed 20261026T235949-L-1474118 2026-10-26 (merge of deliver/V3/Sheaf.Paper.CompletedRootProjectionLinear)
