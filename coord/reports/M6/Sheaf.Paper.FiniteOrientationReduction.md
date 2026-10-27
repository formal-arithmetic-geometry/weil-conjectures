## What changed

Partial stage-3 proof delivery for `Sheaf.Paper.FiniteOrientationReduction`.
Proved `coefficient_ideal` by the unit-invariance of a principal ideal and ideal-power
identities. Proved both conjuncts of `coefficient_unit_purity` from the existing proved
ordinary-etale `projectionMap_rightUnitality`: transpose through the exceptional
adjunction, use the canonical braiding to change tensor ordering, and use whisker
exchange and left-unitor naturality for gamma. All added categorical helpers are
private and fully proved. Existing public signatures and definitions are unchanged.

Added the private proof import
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit`.
Updated proof steps 2 and 3 of `lem-sp-finite-orientation-reduction` to record this
shorter route. The other clauses retain their existing statements and proof plans.

## Proved and sorry left

Closed 2 of the original 8 holes; added 0 holes and split off 0 statements.
All names below are in `AlgebraicGeometry.ProEtale.SpFiniteOrientation` and belong
to node `lem-sp-finite-orientation-reduction`.

Proved: `coefficient_ideal`, `coefficient_unit_purity`.

The six unchanged sorry declarations are:

- `canonical_purity_at_unit`
- `uniformizer_orientation_agreement`
- `finite_orientation_reduction`
- `uniformizer_purity_agreement`
- `unit_tower_mem`
- `unit_tower_reduction`

The ideal proof allows exponent zero and arbitrary ramification. The categorical
unit calculation does not require smoothness, a nonempty scheme, or a nonzero ring.
No additional hypothesis is introduced.

## No longer needed

Removed the direct proof imports `Sheaf.Paper.ProjectionMateExact` and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`.
Their separate unit-factor arguments are superseded by the proved source-library
projection-unit normalization. Removed their nodes
`lem-weil-pbc-ringed-projection-mate-exact` and
`lem-cbc-extension-zero-projection-formula` from this node's proof dependencies and
obsolete tool approvals. No module is withdrawn: these modules may remain needed by
other consumers or transitive imports. All public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The DAG's proper/open unit-factor calculation can be shortened to the source
library's already-proved `projectionMap_rightUnitality`. No mathematical statement
was found false. The remaining finite-ring reduction input is stated in pro-etale
coordinates with a common annihilating exponent; it does not directly discharge the
ordinary-etale equation with two possibly different exponents in this module.
The tower gluing interface supplies the reduction equation, but proving that the
actual coefficient-unit reduction is invertible still requires the strict-system
and derived-scalar calculation described in the existing docstring.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
