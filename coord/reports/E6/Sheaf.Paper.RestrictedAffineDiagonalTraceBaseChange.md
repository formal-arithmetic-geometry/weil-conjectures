## What changed

Filled the proof of
`WeilConjectures.PurityFiniteSetting.restrictedAffineDiagonalTraceBaseChange`
in `Sheaf.Paper.RestrictedAffineDiagonalTraceBaseChange`, retaining its statement
and its original public import. Added private proof imports and proved private
helpers. Added the proved module `Sheaf.Paper.AffineCounitMateUnitChange` for
the categorical unit conversion. No existing definition, public interface, other module, or target
statement is changed.

The proof converts the actual affine mate to the monoidal-unit counit transpose,
uses the existing affine counit base-change and coefficient-descent equations,
pastes the coordinate and open/self-product squares, and restricts along the
diagonal. The section coefficient equation cancels the inverse exceptional mate.
Naturality of the site comparison then gives the specified alpha/rho/Tate formula.
The node's proof, proof dependencies, and proof origin describe this argument.
Both delivered modules compiled together through `lcompile.py --all`; style
warnings were resolved by documenting the scoped elaboration budget and
removing blank lines within proof commands.

## Proved and sorry left

Closed one existing hole:
`WeilConjectures.PurityFiniteSetting.restrictedAffineDiagonalTraceBaseChange`
(node `lem-pur-restricted-affine-diagonal-trace-base-change`).

Added zero holes; zero holes remain in the delivered module. All private helpers
are proved. The new public theorem
`WeilConjectures.PurityFiniteSetting.affineCounitMate_unitChange` is proved too,
with zero holes. Existing imported obligations, including affine counit normalization,
coefficient descent, and Tate section coherence, are used as declared rather
than restated or split again. This is a proof from existing declarations, not a
new decomposition.

## No longer needed

No original public import was removed and no module is withdrawn. The following
old direct proof dependencies are not needed directly by this argument:

- `lem-amb-affine-space-top-trace`, module
  `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`: use the already stated affine
  counit normalization theorem instead of reproving its trace input here.
- `lem-amb-affine-trace-unit-compact-base-change`, module
  `Sheaf.AlgebraicGeometry.AffineTraceUnitCompactBaseChange`: its transposed
  conclusion is supplied by the existing counit normalization theorem.
- `det-prop-sfb-cartesian-coefficients-twists`, module
  `Sheaf.Paper.CartesianCoefficientTwists`: the equation is at fixed finite
  coefficients; ordered finite Tate composition and section coherence suffice.
- `lem-weil-pbc-comparison-pullback`, module
  `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`: only naturality
  of the already constructed `OrientationCounit.comparisonPull` is required.

These remove direct DAG edges only; they do not claim those modules are absent
from transitive imports or unnecessary to other consumers. The original unit
route is preserved. The proof does not import the older
`Sheaf.Paper.AffineDiagonalTraceRestriction` or
`Sheaf.Paper.AffineDiagonalPresentedBaseChange`, whose import closure reaches
this item. A temporary proof import of
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit` was removed:
adjunction naturality handles the unit conversion.

## Where the brief, the DAG or earlier work was wrong

No statement correction is needed. The existing smaller counit-normalization,
coefficient-core, composition, and section-coherence declarations suffice to
formalize the plan. The older affine-diagonal restriction theorem cannot serve
as an independent shortcut because importing it would create a cycle. The
fourth split need not be repeated: no new mathematical obligation is introduced.

## New nodes

`lem-pur-affine-counit-mate-unit-change`, realized by
`Sheaf.Paper.AffineCounitMateUnitChange`: the coefficient-unit affine mate,
followed by inverse unitChange, is the ordered coefficient descent inverse
followed by the monoidal-unit tower counit transpose. It is proved directly
from adjunction naturality and associativity. It is a strictly smaller
categorical conversion, with no base-change, diagonal, open-restriction, or
site-comparison equation. No hole is split off. Profiling isolated this proved
calculation as the runtime bottleneck; after simplifying its proof, placing
it in its own module keeps the complete files within the 60-second limit.

No change record is required: only the item, its node, and this new proved
module and its node are changed.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
