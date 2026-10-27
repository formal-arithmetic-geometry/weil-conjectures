## What changed

Filled `AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.coefficientHeartPullIso_monoidal`
in `Sheaf.Paper.FiniteCoefficientHeartEncoding`. Its statement and the definitions of the
encoding, direct-image comparison and specified pullback mate are unchanged.

The proof retains local pure-tensor normalization when constructing the encoding's
monoidal structures. It proves that the specified direct-image comparison preserves
tensors on local pure pairs, obtains its unit equation from uniqueness of a monoid
unit, and applies the generic monoidal adjunction conjugate identities to the exact
uniqueness-of-left-adjoints map in `coefficientHeartPullIso`.

The canonical internal direct-image pure-pair formula is reused from the proved
`ModuleRingedComparison.canonicalInternalPush_normalized` in
`Sheaf.Paper.ProEtaleSectionModuleFunctors`. The new module
`Sheaf.Paper.FiniteCoefficientHeartTensor` proves the independent encoding normalization
by composing the existing internal/section, ring-isomorphism and constant-scalar
comparisons, retaining their generator formulas. The existing
`coefficientHeartEncoding_monoidal` proof now also uses this normalized construction.

Validation: the public item compiled with no errors or warnings in 31.3 seconds.
The new normalization module compiled separately with no errors or warnings in
55.9 seconds. Both use the normal 60-second file limit and default heartbeat limit.
The original finite/discrete binders are retained verbatim; the unused-section-variable
linter is disabled only for this existing theorem, since the proof works more generally.
Delivery preflight is the remaining check.

## Proved and sorry left

Original holes: 1, in
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.coefficientHeartPullIso_monoidal`.
This hole is closed by the compiled proof. Added holes: 0. Split-off holes: 0.
There is no `sorry` in either submitted Lean module. The new theorem
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.coefficientSectionTensor_normalized`
has a complete proof, not a postponed normalization obligation.

## No longer needed

Removed the private proof import `Sheaf.Paper.FiniteDiscreteEncodingTensorTor`.
The heart argument uses the normalized underived construction directly, so it no
longer uses the arbitrary monoidal existence helpers from that derived-comparison
module. This removes an import of this item; it does not withdraw that module or any
of its declarations, which other consumers may still require.

None of the original planned normalization dependencies is discarded: the three
comparison nodes now occur through the new proved normalization helper. The unit's
proper-base-change route is preserved. No existing module or declaration is deleted.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The planned generator calculation
must retain the normalization while constructing monoidal structures; arbitrary
independent monoidal witnesses do not supply that equation.

Repository search found the needed canonical internal direct-image calculation
already proved in `ProEtaleSectionModuleFunctors`; a duplicate derivation was removed
from the sandbox. The proof uses that existing result with its actual adjunction
structure. A proof import also registers transported pullback instances; local instance
selection retains `CondensedRing.monoidal_upperStar`, which is the native structure
in the unchanged public statement. The right-adjoint lax structure is taken from its
oplax projection explicitly. The invertibility of the direct-image comparison also makes a separate
local unit calculation unnecessary: multiplication determines a monoid unit.

The local build mirror temporarily lacked imported `.olean` files. The supported
`LCOMPILE_NO_LOCAL` setting of `lcompile.py` selects the project server for validation.
No launcher or project tool was changed. The cached direct-image comparison was private
until the public export reached the compiled build. A temporary private probe checked
the argument during that wait and was removed. The actual public item now compiles
against the published dependency; no dependency was copied or redeclared.

## New nodes

`lem-sfb-finite-coefficient-section-tensor-normalization` records the proved theorem
`coefficientSectionTensor_normalized`. It concerns one encoding on one scheme and
contains neither a scheme morphism, an adjunction nor the pullback-mate obligation.
Its proof composes existing normalized tensor comparisons and is valid for zero
coefficients and empty schemes. The parent node's proof and proof dependencies now
record this helper, the existing canonical direct-image normalization and the generic
mate calculation. There are no change records because no existing signature or
definition was changed.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
