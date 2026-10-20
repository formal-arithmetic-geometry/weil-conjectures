# AlgebraicGeometry.ProEtale.StrictTower.singleBetaInv_isIso: proof helper scope

## Reason

The stage-3 static check requests a change record for the added `variable` and
`attribute` commands. These commands support fully proved private helpers for
the two original holes. They occur in a new, closed section; the instance
registration is local. No existing public signature, definition body, visibility,
public import, notation, or global instance registration changes. No target
statement or definition meaning changes, and no consumer adaptation is needed.

The proof transports ordinary open base change through the constant coefficient
equivalence. Full faithfulness and the counit formula then prove invertibility
of the original, prescribed unit transpose. All added helpers are private and
contain no holes.

## Old

The existing ambient variable declaration, retained verbatim, is:

```lean
variable (B : Type (u + 1)) [CommRing B]
```

Between `singleBetaInv` and `singleBetaInv_isIso` there was no helper section,
variable command, or instance registration. Both theorem signatures and every
existing definition remain verbatim; only their two `by sorry` proofs change.

## New

The new helper section has the following scope commands, verbatim:

```lean
section

variable [Finite B] [TopologicalSpace B] [DiscreteTopology B]
```

After the fully proved private theorem `realization_equivalence`:

```lean
attribute [local instance] realization_equivalence
```

The section ends before the existing public theorem `singleBetaInv_isIso`.
Thus neither its extra hypotheses nor its instance registration escapes into
the existing public declarations. The proof supplies a discrete topology
locally. Proof-only imports are:

```lean
import all Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
```

The `import all` forms provide private scalar-unit equations and the constructed
scalar equivalence only to this file's private helpers. They are not public
imports. The original two public imports remain unchanged.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
--uses singleBetaInvApp_naturality singleBetaInv_isIso singleBetaInv singleBeta`
reports 773 transitive downstream modules and the textual users listed below.
The holder column records the shared snapshot. There are no adapted modules:
the existing interface and all data definitions are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized | P5 | Two proofs completed; private helper section added. |
| Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars | C9 | Unchanged theorem and comparison signatures and bodies. |
| Sheaf.SecSmoothPurity.OpenBaseChangeDerivedUnit | unclaimed | Unchanged theorem and comparison signatures and bodies. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | Y7 | Unchanged comparison signature and body. |
| Sheaf.AlgebraicGeometry.OpenBaseChangeSiteTransport | P7 | Unchanged comparison signature and body. |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows | F5 | Unchanged comparison signature and body. |
| Sheaf.SecSmoothPurity.OpenScalarExchange | unclaimed | Unchanged comparison signature and body. |

## Status

landed 20261020T122120-L-479272 2026-10-20 (merge of deliver/P5/Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized)
