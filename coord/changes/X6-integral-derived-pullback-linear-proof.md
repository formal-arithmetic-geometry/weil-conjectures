# WeilConjectures.integralDerivedPullback_linear

## Reason

The proof adds proved private helpers and proof-local commands (`open`,
`section`, `variable`, and a local instance attribute). The static interface
comparison records these commands even though they change no public statement,
definition, import or instance. This record documents that syntactic change.

## Old

The original proof was `:= by sorry`. Its surrounding nondeclaration commands
were:

```lean
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
end WeilConjectures
```

The original theorem signature and both public imports are preserved verbatim.

## New

The proof uses the finite adjunctions, diagonal product and mapping-cone maps,
and the existing normalized good-complex comparison. Every added declaration
is private and completely proved. No existing definition is changed.

The private proof region opens `CategoryTheory.Limits` and `Opposite`, and its
Roos region opens `CochainComplex`. Sections bind the existing coefficient data
and the generic abelian category used for Roos. Inside `Representatives`, the
local instance attribute on the existing private `coefficientModuleLinear`
supplies the canonical sheaf-module action while proving chain-level linearity.
That attribute ends with the section; the final theorem uses the published
ambient derived linear structures. No exported instance or attribute changes.
No transparency or compiler-limit option is changed.

## Users

`tools/downstream.py Sheaf.Paper.IntegralDerivedPullbackLinear --uses
WeilConjectures.integralDerivedPullback_linear` lists the following declaration
users (including the defining file). All public signatures and public imports
are identical, so no consumer adaptation is necessary. The other transitive
importers also see the same interface.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.DerivedPullbackTensorHom | T4 | Same theorem, with its proof completed; no edit. |
| Sheaf.Paper.FrobeniusSquareExchange | V4 | Same theorem, with its proof completed; no edit. |
| Sheaf.Paper.IntegralDerivedPullbackLinear | X6 | Assigned proof completed; all helpers private. |

## Status

landed 20261026T003210-L-152589 2026-10-26 (merge of deliver/X6/Sheaf.Paper.IntegralDerivedPullbackLinear)
