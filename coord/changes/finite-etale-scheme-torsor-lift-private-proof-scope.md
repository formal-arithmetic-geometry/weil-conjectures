# AlgebraicGeometry.Etale.finiteEtale_lifts_scheme_torsor

## Reason

The proof ports the existing representation constructions as private helpers and proves
reflection of the geometric torsor conditions. The static interface checker records added
`open Opposite`, section variables, `include`/`omit`, namespaces and two elaboration options
as a command change. Every added declaration is private. The theorem signature and every
public definition are unchanged; the added imports are proof-only.

## Old

The original command scope after `@[expose] public section` was:

```lean
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale
```

## New

The original commands remain, with private representation helpers in the namespace
`AlgebraicGeometry.Scheme.EtaleTorsor.SchemeLiftRepresentation`, a file-local
`open Opposite`, and these file-local elaboration options before the main theorem namespace:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

Section variables, `include` and `omit` delimit the private proof scopes. In the repair,
private-action lemmas spell out their binders, cancellation is obtained from general Mathlib
iso laws, and private decomposition/local-triviality/stalk helpers have more general statements.
The four standalone helper declarations named in the return are removed. The action and
equivariance checks occur directly in the private constructions.
These commands affect elaboration inside this module and export no instance or attribute.
No public signature has changed; downstream files require no adaptation.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteEtaleSchemeTorsorLift --uses
finiteEtale_lifts_scheme_torsor` returned no listed users. Direct import search identifies
the following consumer, whose theorem call remains valid because the public signature is
identical:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteEtaleTorsorLifting | not adapted | none; signature unchanged |

## Status

landed 20261012T135334-L-1700172 2026-10-12 (merge of deliver/X2/Sheaf.AlgebraicGeometry.FiniteEtaleSchemeTorsorLift)
