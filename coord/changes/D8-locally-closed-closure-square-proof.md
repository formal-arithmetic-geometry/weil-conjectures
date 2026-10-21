# Locally closed closure square proof and import pruning

Item: `Sheaf.AlgebraicGeometry.LocallyClosedClosureComparisonSquare` (D8).

## Reason

The five theorem proofs were holes. The main comparison can instead be proved from
its specified open-unit and closed-counit equations by restriction and adjunction
triangle identities. This avoids the general locally closed extension coherence
interface. Unused imports are removed to keep the proof dependency graph accurate.

## Old

The module contained five theorem holes and publicly imported the general modules
`Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison`,
`Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`,
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero` and
`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`.
Its private imports included `WeilConjectures.SixFunctors.Finite.Exact` and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

## New

All existing declaration signatures, attributes and construction bodies are preserved.
Five theorem holes are replaced by proofs using the specified unit/counit equations,
exact-derived composition, adjunction triangle identities and isomorphism cancellation.
Private proved helpers implement the categorical calculations. The node's proof,
proof dependencies and proof origin follow that argument; its statement is unchanged.

Removed the first three public imports listed above.
`SupportComparisonPullbackCoherence` is now a private proof import.
The precise public import
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso` provides
`upperStarCongr` used by the existing public pullback-compositor definition.
The intrinsic extension module remains indirectly available to this proof through
`OpenComparisonUnitNormalization`; no declaration from it occurs in a public signature.
Removed the two redundant private imports listed above. New private proof imports
supply open-unit normalization, the derived mate calculation, inverse-image exactness,
exact-derived square composition and closed-immersion normalization.

The proof context opens `CategoryTheory.MonoidalCategory`, sets `maxRecDepth` to 2048
(as in the existing open-unit calculation), and locally enables the two composite
finite-limit/finite-colimit preservation instances. These support private helpers;
no instance, notation or public declaration is added to the exported interface.

## Users

A current search of `lean/Sheaf` and `lean/WeilConjectures` found no Lean module
importing the item. No consumer adaptation is needed. Its DAG parents and Lean
attachment are preserved; this is not a withdrawal. The unchanged semantic statement
dependencies remain recorded. No source-library module is changed. No target,
statement, definition or underlying choice of comparison is changed.

## Status

landed 20261021T151113-L-1129265 2026-10-21 (merge of deliver/D8/Sheaf.AlgebraicGeometry.LocallyClosedClosureComparisonSquare)

Proved all five original holes, with zero holes added, left or split off. The complete
module compiled through `lcompile.py` in 17.5 seconds. All existing declaration
signatures match the current shared source exactly. There are zero `sorry` tokens.
Two unused simp arguments were removed before the delivery check. The delivery tool
repeats compilation and preflight; independent review remains with the maintainer.

Empty schemes and the zero coefficient ring require no special choice or hypothesis:
the proof uses the same formal equations. The only geometric inheritance needed is
Noetherianity of the open intermediate scheme V.
