# WeilConjectures.PurStrictScalar.scalar_refinement_origins_E

## Reason

Prove the existing E-side origin theorem from the actual finite reduction and
its bounded constructible etale origin. The limit-reduction module contributes
nothing to the statement or proof, so remove its public import. All existing
public declaration signatures, definitions and attributes remain unchanged.
The added scalar quotient construction and scalar comparisons are private and
fully proved. No target definition or statement changes meaning.

## Old

The old public import block, verbatim:

```lean
public import Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
public import Sheaf.Paper.CompactSupportStrictScalarMate
public import Sheaf.Paper.CompactSupportScalarLimitReduction
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteTorAmplitudeSites
```

## New

```lean
public import Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
public import Sheaf.Paper.CompactSupportStrictScalarMate
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteTorAmplitudeSites
import all Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
import all Sheaf.Paper.ProEtaleConstructibleOrigin
```

The two private imports expose already proved helper declarations to this proof
only. The theorem signature is identical to the original.

## Users

`tools/downstream.py Sheaf.Paper.ScalarRefinementOriginsE --uses
WeilConjectures.PurStrictScalar.scalar_refinement_origins_E` lists the following
users and exactly one downstream module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ScalarRefinementOriginsE | A2 | Replace its one sorry with a complete proof. |
| Sheaf.Paper.CompactSupportStrictScalarRefinement | D5 | No adaptation; check unchanged. |

The direct importer already publicly imports
`Sheaf.Paper.CompactSupportScalarLimitReduction` itself. Its unchanged source
is checked against this delivery; no module held by D5 is edited.

## Status

landed 20261026T065007-L-2662492 2026-10-26 (merge of deliver/A2/Sheaf.Paper.ScalarRefinementOriginsE)
