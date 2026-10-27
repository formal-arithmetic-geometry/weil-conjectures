## What changed

Replaced the hole in `tower_chernOrdinaryScalar_pullback` by a proof combining two
strictly smaller ordinary constructions. Its statement is unchanged verbatim, and
all three original public imports are preserved. The only additional imports are
private proof imports of the three new modules.

The coefficient arrows are constructed explicitly as the inverse ordinary
scalar-adjunction transposes of `scalarGenerator`. Three proved private helpers (the first two following the local calculations
of `TowerChernScalarUnit`)
show that the coefficient single is K-flat, compute an ordinary adjunction on
single complexes, and identify each scalar-counit composite with the prescribed
`scalarUnit.hom`. The last helper uses `ScalarData.transpose_model`, cancellation
of the exact restriction single comparison, and the third Chern normalization.
It does not assume the desired derived coefficient equations.

The integral construction and ordinary tensor comparison are isolated in separate
modules. The first also records that the middle Kummer component is the actual
full-units pullback; this equation is passed to the second to fix its root map.
The main proof constructs the ordinary coefficient arrows, passes their adjunct
identities to the comparison, proves both derived coefficient equations, and
assembles the original five conclusions.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.SpTowerClasses.tower_chernOrdinaryScalar_pullback`
(node `lem-sp-tower-chern-ordinary-scalar-pullback`). Its complete Lean proof uses
the three new intermediate statements below. This is a decomposition, not a net
hole reduction: one original hole closed, three new holes added, net +2 holes.

The derived coefficient-counit calculation is isolated as the strictly smaller
public theorem `scalarCounitNormalization`, with node
`lem-sp-tower-scalar-counit-normalization`.

Every remaining hole added by this delivery is the entire proof of one public
theorem, with a source, a complete proof in words and its own node:

- `AlgebraicGeometry.ProEtale.SpTowerClasses.scalarCounitNormalization`,
  node `lem-sp-tower-scalar-counit-normalization`, in
  `Sheaf.Paper.TowerScalarCounitNormalization`: the normalized derived counit
  equation for a coefficient arrow whose ordinary transpose is scalarGenerator.
- `AlgebraicGeometry.ProEtale.SpTowerClasses.integralCoefficientPullback_exists`,
  node `lem-sp-tower-integral-coefficient-pullback-existence`, in
  `Sheaf.Paper.TowerIntegralCoefficientPullbackExistence`: the integral inverse
  image, its canonical Kummer middle map, and its flat-term K-flat preservation.
- `AlgebraicGeometry.ProEtale.SpTowerClasses.ordinaryScalarAssociation_exists`,
  node `lem-sp-tower-ordinary-scalar-association`, in
  `Sheaf.Paper.TowerOrdinaryScalarAssociation`: balanced ordinary association and
  its coefficient/root equations for already supplied integral inverse image
  and ordinary-adjunction-normalized coefficient arrows. Its conclusion has
  neither integral-data existence nor K-flat preservation nor derived equations.

There are zero holes in the item module and three in the new modules. There are
no data definitions using an unproved arbitrary witness. No existing module
besides the assigned item is changed.

## No longer needed

No original public import is removed, and no module is withdrawn. No unit step
is bypassed: the two constructions still realize classes proof (2).

The updated proof does not use `exists_normalizedScalarUnit` or its module
`Sheaf.Paper.TowerChernScalarUnit` (node `lem-sfb-tower-chern-scalar-unit`). It
constructs ordinary coefficient arrows by the given adjunction and proves their
derived normalization directly; no separately chosen derived unit is needed.

It also does not use the full derived algebra-diagram coherence theorem
`algebraDiagramPullbackExtensionCoherence` or its module
`Sheaf.CategoryTheory.AlgebraDiagramPullbackExtensionCoherence`
(node `lem-pur-algebra-diagram-pullback-extension-coherence`). The remaining
association obligation is entirely ordinary and can use the normalized
`scalarAssociation_existsUnique` interface in
`Sheaf.SecSmoothPurity.CochainCoefficientArrows` instead.

The existence theorem `semilinearDerivedSections` (node
`lem-coef-semilinear-derived-sections`) is not needed to prove the new main
combination or construct the ordinary coefficient arrows. The already supplied
`ScalarData` representative formula suffices. Its defining node
`def-coef-semilinear-system-models` is retained explicitly.

The generic inverse-image and cartesian-root construction dependencies remain
in the integral construction node; the flat resolving theorem remains there as
well. These dependencies are moved to the step that needs them, not claimed to
be globally unused. No global module-pruning claim is made.

## Where the brief, the DAG or earlier work was wrong

The existing `ordinaryInverseSystem_exists` and `forget_evaluation_iso` provide
the ordinary system assembly and per-level additive comparisons. The integral
node now names these more precise dependencies, as well as the ringed-site
construction and flatness inputs. They do not by themselves supply the complete
normalized integral pullback record.

The original plan's named general algebra-diagram declarations do not directly
supply the integral inverse-image record and its forgetful/unit/Kummer
normalizations in these concrete tower coordinates. Their ringed-site and
coefficient-square inputs still have to be constructed. The three new statements
isolate these ordinary geometric constructions instead of asserting that the
general comparison can be applied without its inputs.

The existing scalar-unit existence theorem is stronger than what the two
coefficient equations require. Their ordinary arrows need not be obtained by
choosing another derived unit: the supplied ordinary adjunction defines them,
and the representative transpose formula proves the required comparison with
the given normalized `scalarUnit`.

The middle Kummer map is recorded explicitly by the new integral construction
so that the root comparison can be read from the actual inclusion square. This
strengthens only the intermediate construction, not the assigned statement.
The statements include empty schemes and empty charts; no root flatness,
flatness of f or unramified-coefficient hypothesis is introduced.

## New nodes

`lem-sp-tower-integral-coefficient-pullback-existence` records only the integral
geometric construction and resolving property. Its source is classes proof (2),
with the ringed-topos flat pullback result in Stacks `sites-modules`,
`lemma-pullback-flat`, and K-flat pullback in `sites-cohomology`,
`lemma-pullback-K-flat`. It is independent of ordinary or derived extension to A.

`lem-sp-tower-ordinary-scalar-association` records ordinary balanced association
for fixed integral data and fixed coefficient arrows. Its source is the ordinary
scalar extension in classes proof (2), using the normalized balanced-association
interface of `def-pur-cochain-coefficient-arrows`. It has no derived conclusion.

Both nodes record actual LeanSearch, Loogle and Mathlib grep searches made by
msearch.py. Local searches found the general scalar-association and resolving
interfaces, but no declaration of these specialized normalized constructions.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
