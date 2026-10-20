## What changed

Proved `AlgebraicGeometry.ProEtale.completedCondensedRational` and
`AlgebraicGeometry.ProEtale.completedCondensedPadicRational` in
`lean/Sheaf/Paper/CompletedCondensedCoefficients.lean`, with their existing statements
unchanged. Added a proof-only `import all Sheaf.Paper.ContinuousIntegralScalarExact`.
All definitions, public imports and existing public signatures are unchanged.

The proof transports the explicit continuous-function localization cocone through
monoidal sheafification and inverse image, identifies its vertex with the rational
regular module restricted to integral scalars, and checks the zeroth leg. Private
categorical helpers extract the sequential colimit universal property and prove
naturality of every leg by cancelling the invertible scalar. Multiplication by the
prime is proved invertible sectionwise and then mapped through inverse image. The
base-field proof identifies PadicInt.subring with continuousIntegers by their norm
predicates and applies the same assembly.

The cleaned module compiled through lcompile.py in 27.4 seconds. Keeping
`upperStarFromPoint` and its monoidal structure definitions locally irreducible from the start of the file avoids expanding
its composed inverse-image construction during typeclass inference. Regular-module transport isomorphisms are checked in
a generic private construction before specializing to sheaves. The one proof
that uses its construction unfolds it explicitly. No other module is adapted.
The scoped projection notation and local reducibility controls are recorded in
`coord/changes/completed-condensed-proof-scopes.md`; they affect local elaboration
only. Private helpers from the unsuccessful integral experiments were removed.

## Proved and sorry left

Original holes: 4. Closed: 2. Added: 0. Split off: 0.

Closed:
- `AlgebraicGeometry.ProEtale.completedCondensedRational`.
- `AlgebraicGeometry.ProEtale.completedCondensedPadicRational`.

Remaining, unchanged, both attached to `sk-prop-sfb-qlbar-colimit-x`:
- `AlgebraicGeometry.ProEtale.completedCondensedIntegral`.
- `AlgebraicGeometry.ProEtale.completedCondensedPadicIntegral`.

The already proved algebraic-closure and pullback declarations are retained.
This is a partial proof delivery, not a decomposition. There are no new holes,
axioms, public definitions, or public helper declarations.

## No longer needed

For the rational comparisons, `det-prop-sfb-qlbar-colimit-x-invert-ell`
(`Sheaf.Paper.PadicIntegersInvertEll`) is replaced by the existing explicit scalar
localization construction in `Sheaf.Paper.ContinuousIntegralScalarExact`.
The same rational argument does not import
`Sheaf.Paper.ContinuousIntegralRegularTelescope`: its underived regular-module
transport is proved privately from the scalar-localization cocone instead.
No original import was removed. No entire module is withdrawn. The integral-limit
dependency is still needed by the remaining integral statements and is not pruned.

## Where the brief, the DAG or earlier work was wrong

The declared PadicIntegersInvertEll proof interface reaches this item through
EllAdicRationalization, the continuous integral-model chain, and derived bounded
constructible coefficients. Importing it here creates a cycle. The public
ContinuousIntegralRegularTelescope module similarly reaches the item through
ContinuousIntegralLocalization and derived integral-model modules. The existing
ContinuousIntegralScalarExact module has no such cycle and already proves the
needed explicit presheaf localization universal property. This delivery uses that
construction and proves the underived transport privately; the unit localization
route is retained. The DAG proof steps 2 and 9 and proof dependencies now record it.

The integral-limit declaration uses the spectral-norm coefficient presentation,
whereas this item specifies the embedded integer ring and an arbitrary chosen
uniformizer. Identifying their normalized towers is additional interface work;
these two integral holes remain unchanged. No statement is disputed or weakened.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
