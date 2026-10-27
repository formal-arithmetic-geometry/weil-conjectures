## What changed

Prove `AlgebraicGeometry.ProEtale.CondensedRing.det_cor_affine_space_rational_line`
by composing the restricted open adjunction with the rational projective-line
adjunction. The compactification coherence theorem compares the standard chart
compactification with the Nagata choice. Strong monoidality, the canonical Tate
line pullback and shift comparisons identify the composite right adjoint.
Mathlib supplies the unique counit-compatible isomorphism to any right adjoint.

Move `rationalLocalizingCategory`, `rationalLocalizingInclusion` and
`rationalTwistFunctor`, with their bodies and signatures unchanged, into
`Sheaf.Paper.RationalLocalizingTwist`, publicly re-exported by the item. Redirect
only the corresponding import in `Sheaf.Paper.TateTwistedProjection`. This removes
the old import cycle through RationalP1Triangle. No target signature changes.

The split-off helper module `Sheaf.Paper.AffineLineAdjunctionAssembly` states the
canonical projective-line adjunction obtained from the strict diagonal cycle
system, its uniquely normalized completed limit and its coefficient reference.
Its proof plan supplies the localization instances from Grothendieck categories
of sheaves and sequences of sheaves in the coefficient universe.

The definition node attachment and the affine-line proof route are updated.
Change record: `coord/changes/R3-affine-line-shared-definitions.md`.

Validation: the final item compiles with `lcompile.py` (55.9 seconds). The shared
definitions, the redirected Tate module and the new assembly statement also compiled.
The target signature and retained definition bodies were compared with the source;
they are unchanged. All Lean lines have at most 100 characters and debug options
have been removed.

## Proved and sorry left

The original item has one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.det_cor_affine_space_rational_line`
(node `det-cor-affine-space-rational-line`). The submitted combination proof closes it.
One new hole is split off:
`AlgebraicGeometry.ProEtale.RationalP1.rationalP1_adjunction_assembly`
(node `lem-sfb-rational-p1-adjunction-assembly`). It supplies the canonical diagonal
data to the already stated projective-line adjunction. This is a decomposition:
one original hole closed, one strictly simpler projective-line assembly hole added.
The item's combination proof has no `sorry`.

## No longer needed

The generic `det-sp-unique-right-adjoint` proof dependency is replaced by the
proved Mathlib adjunction uniqueness API. The proof does not need
`sk-prop-sf-existence` to select a pre-existing exceptional adjoint: the assertion
quantifies over any right adjoint and we construct the required adjunction by
composition. The statement's existing setting import is retained.
The aggregate coefficient-twist dependency
`det-prop-sfb-cartesian-coefficients-twists` is replaced by the existing canonical
rational line comparison, strong monoidality and CommShift comparison. Its
underlying coefficient-cartesian facts remain dependencies of those interfaces.
The direct dependencies `sk-prop-sfb-cartesian-coefficients` and
`sk-def-sfb-module-pushforward-pullback` are likewise supplied through the existing
derived pullback composition and single-functor comparisons; the affine-line proof
does not separately use them. `det-prop-p1-adjunction-rational-triangle` moves to
the assembly lemma's proof dependencies and is still required, rather than pruned.

The public import of `Sheaf.Targets.AffineSpaceRationalLine` in
`Sheaf.Paper.TateTwistedProjection` is replaced by the smaller shared definition
module. No module is withdrawn: the projective-line triangle theorem and the
unit's affine-line step remain required.

Removed redundant proof imports (their declarations remain available through public
imports of the necessary interfaces):

- `WeilConjectures.Compactification.ProjectiveSpace`
- `Sheaf.Compactification.BoundaryRefinement`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.Paper.CartesianCoefficientTwists`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`

## Where the brief, the DAG or earlier work was wrong

The mathematical plan applies. Its old module placement made the plan impossible
to import directly: P1Triangle imported P1UnitCounit, whose TateTwistedProjection
imported this affine-line item for three definitions. Separating those definitions
fixes the cycle without changing any declaration's meaning. The projective-line
triangle interface additionally requires explicit canonical diagonal data and
localization choices; the assembly helper records this precise remaining step from existing
statements. No arbitrary existential witness is used in a public definition.

## New nodes

`lem-sfb-rational-p1-adjunction-assembly` records the remaining assembly of the strict
cycle system, its unique completed limit and its coefficient reference into the
existing projective-line adjunction. It is a proper projective-line input to the
affine-line argument, not a renamed affine-line statement. Empty schemes and both
coefficient conventions are included; no point or nonempty-base assumption is
used. The new module is `Sheaf.Paper.AffineLineAdjunctionAssembly`.

The moved definitions retain their existing node
`def-sfb-rational-localizing-twist`. Their move and consumers are recorded in
`coord/changes/R3-affine-line-shared-definitions.md`.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
