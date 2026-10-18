## What changed

Proved `AlgebraicGeometry.smooth_curve_points_decomposition` in
`Sheaf.AlgebraicGeometry.SmoothCurvePointsDecomposition`, with its signature and public imports
unchanged. The construction uses `ConnectedComponents C`, its canonical clopen open subschemes,
the smooth-regular and regular-connected-integral lemmas, the existing zero-dimensional
integral-point theorem, and Mathlib's colimit criterion for disjoint covering open immersions.
The maps to the base and the isomorphism are constructed explicitly; the coprojection equations
and their open- and closed-immersion properties are proved.

Updated the existing node's proof, proof dependencies and proof origin to this implementation.
No definitions, signatures, instances, attributes, consumer modules or target statements changed.
Validation: the required deliver3.py dry run compiled the final module and passed stage-3
preflight; review class CODEX because the existing node proof record changed.
The empty scheme gives empty component types; a point gives only a point summand; the dimension-one
subtype excludes point components. The index type remains in universe u without a small-universe
restriction.

Searches: LeanFinder on the finite smooth curve/point decomposition found coproduct-existence
and integrality facts, but no decomposition theorem. Loogle on `Sigma.ι` and `IsClosedImmersion`
returned no hits. Repository and Mathlib grep found the connected-component construction in
`WeilConjectures.AlgebraicGeometry.Curve.SerreDuality`, the regularity API, and
`AlgebraicGeometry.nonempty_isColimit_cofanMk_of` in Mathlib's `AlgebraicGeometry.Limits`.
Those declarations were read and used rather than introducing intermediate statements.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.smooth_curve_points_decomposition`
(node `lem-sbc-smooth-curve-points-decomposition`).

The delivered module contains zero `sorry`. Added zero holes and split off zero statements.
The proof uses the existing, unchanged theorem
`AlgebraicGeometry.isIso_structure_of_integral_zero_dim`
(node `lem-weil-pbc-zero-dim-integral-point`) from
`Sheaf.AlgebraicGeometry.ZeroDimIntegralPoint`, whose proof remains `sorry` in the shared library.
Thus this delivery closes the assigned proof hole from the project's stated dependencies;
it does not claim that the result's entire axiom closure is already sorry-free.

## No longer needed

Removed these proof-only imports:

- `Mathlib.Topology.KrullDimension`
- `Mathlib.Topology.Irreducible`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.RingTheory.RegularLocalRing.Defs`
- `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`

Except for the irrelevant VeryAmple import, the needed notions and instances from these modules
are already supplied by the unchanged public imports and the retained Regular and
ZeroDimIntegralPoint proof imports. Removing redundant imports does not claim their transitive
source modules are absent from the library's import closure.

Removed these explicit DAG proof dependencies:

- `def-sbc-locally-finite-presentation`: finite type follows by composition with the closed
  component inclusion, rather than an explicit polynomial-presentation argument.
- `def-sbc-smooth-morphisms`: only the existing restriction/composition API is invoked;
  its definition is already part of the statement and restriction theorem's interfaces.
- `def-weil-irreducible-components` and `lem-sc-irreducible-components-cover`: use the canonical
  connected-component quotient, without constructing a graph of irreducible components.
- `def-weil-regular-scheme`: the separate `IsRegularScheme` wrapper is unnecessary; the existing
  stalkwise regularity theorem and `IsRegular.isIntegral` supply precisely the needed result,
  with local Noetherianity established independently.
- `lem-pc-closed-imm-base-change`: separatedness follows from composition instances; no
  diagonal/base-change proof or VeryAmple theorem is needed.

No existing module is withdrawn. No unit statement or realized step is bypassed: the item's
unit `sk-thm-vanishing` has no realized nodes in its current record, and this is still the
same finite-component reduction below that unit.

## Where the brief, the DAG or earlier work was wrong

The node's graph and manual gluing plans hide already available APIs. Connected-component
subschemes and `nonempty_isColimit_cofanMk_of` implement these steps directly.
The dependency `lem-pc-closed-imm-base-change` is currently attached to
`AlgebraicGeometry.IsVeryAmple.pullback_of_field`, which is not the generic closed-immersion
base-change assertion its name suggests. This delivery needs neither assertion and removes
that dependency and its VeryAmple import rather than changing that other node.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
