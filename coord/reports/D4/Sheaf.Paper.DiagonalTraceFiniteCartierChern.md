## What changed

Replaced the original hole in `DiagonalTraceFiniteCartierChern` by unpacking its
presentation and applying the proved `DiagonalTraceFiniteCartierChernStrict`
calculation. That module gives the categorical argument that projects the whole-system equation from `IsDiagonalLimit`, moves
its strict-system arrow across the projection by naturality, and applies two
separate finite equations. The original theorem signature is unchanged.

`DiagonalTraceNormalizedRootIso` proves the normalized linear isomorphism from
the strict root system in `IsDiagonalLimit` to the coefficient root system.
Its components are the prescribed additive root maps: a p-adic approximation
argument proves linearity because their targets are killed by the finite prime
power. Faithfulness and reflection of isomorphisms finish the system comparison.
`DiagonalTraceNormalizedRootCone` also proves that this isomorphism transports
the ordinary root-limit cone to the specified coefficient root cone.

`DiagonalTraceRootTransport` constructs `rootSystemTransport` from the exact
single and shift comparisons. Its specialized `coefficientRootTransport` has the
published Tate-line endpoint, so this identification is checked once.
`DiagonalTraceRootProjection` states the remaining root-projection equation.
`DiagonalTraceSupportedFiniteBoundary` states the finite supported Cartier/Chern
calculation for a strict degree-two class, without any completed diagonal arrow
or `IsDiagonalLimit` hypothesis. These are distinct parts of the existing plan:
the first has no Cartier class or Chern arrow, and the second has no delta,
derived reduction functor, or whole-system limit characterization. The parent
uses its whole-system equation, functoriality and projection naturality to
combine them; neither split is the parent statement under another name.

The genuine construction `completedSupportedUnit` is moved, byte for byte, to
`DiagonalTraceCompletedSupportedUnit`, avoiding an import cycle with the finite
strict-class calculation. The original module publicly imports it, preserving
its public name. `DiagonalTraceProjectionEquations` provides two real definitions
of the composite-arrow equations with shared categorical parameters, so checking
their concrete types does not repeatedly expand the same sheaf category data.
All proof imports are private; existing public imports remain. The source-cone
and Ext-arrow presentation hypotheses are likewise real named predicates,
allowing their concrete categorical structures to be shared.
`ExtDerivedPresentation` packages the actual endpoints, isomorphisms and arrow;
its Ext equation is a separate explicit hypothesis. `supportedSourceComparison`
names the existing single-limit comparison on that data. Both are real
constructions.
`finiteChernComposite` names the existing projected coefficient input followed
by the evaluated Chern morphism, sharing its source and target types.
`finiteBoundaryEquation` names exactly the supported finite composite equation
without any normalization hypothesis, sharing its checked endpoint types.
`completedBoundaryEquation` and `finiteChernEquation` likewise name the original
completed composite equality, without asserting it. They let the abstract
combining lemma share the same endpoints as the finite calculation.

`IsDiagonalLimit` now uses the definitionally identical
`FiniteCartierNormalization` for its expanded finite clause. Profiling isolated
the old existential elimination at about 41 seconds and its root-only diagnostic
at 66 seconds; sharing this predicate addresses that type-checking cost.
The original signature and every other clause remain unchanged. Its change
record lists all direct and named indirect consumers and current claim holders;
no other group's source is changed. The three finite predicate/construction
helpers have no unnecessary noetherian binders: the original finite clause is
valid without them.

Validation: `lcompile.py --all` accepts all nineteen delivery modules in import
order within the per-file limit, with debug options removed. The seven existing
consumers compile unchanged against the packet: `DiagonalTraceSources`,
`RationalP1CompletedLimitBridge`, `RationalP1Triangle`,
`AffineLineAdjunctionAssembly`, `DiagonalTraceFiniteAdjunctionSupported`,
`DiagonalTraceFiniteAdjunctionGeometric`, and
`DiagonalTraceFiniteAdjunctionFactorization`. Their temporary sandbox copies
were removed after checking. The two proved root-comparison lemmas were also
checked with `#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound`.

The complete combining proof was first checked in the item itself but took
96 seconds, after the definition refactor. The proved strict-presentation module
and its generic categorical combining lemma separate that calculation from
existential elimination; no additional mathematical hole is introduced by this
performance split. Delivery also checks all 23 related modules successfully.
The first preflight found one metadata-format mismatch in the structure node;
its Lean record now contains the header signature, with fields described in the
node's mathematical statement.

## Proved and sorry left

The hole in `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finiteCartierChern`
is replaced by a complete combining proof. This delivery is a decomposition,
not a net closure of the mathematical obligation: one original hole is replaced
by two strictly separate lower holes. The original module has no remaining
`sorry`. The actual delivered hole count is two: one original hole is closed
and two are added, so the ledger net is minus one.

The new theorems
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_normalizedRootIso` and
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_normalizedRootCone`
are proved without adding a hole. The new
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finiteCartierChern_strict`
is also proved: it contains the actual comparison/naturality combination,
separated from existential elimination for kernel performance. `rootSystemTransport` and both equation
wrappers are genuine constructions; the moved supported unit has no hole.

Exactly two new holes remain:

- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_rootProjection`, node
  `lem-sfb-diagonal-trace-root-projection`.
- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_supportedFiniteBoundary`,
  node `lem-sfb-diagonal-trace-supported-finite-boundary`.

Their docstrings and nodes give their source, the complete intended argument,
and the declarations needed for the subsequent proof. Each unfinished proof is
exactly `by sorry` in its own new module. No definition contains `sorry`.

## Forced adaptations

None forced. `Sheaf.Paper.DiagonalTowerTraceLimit` (unclaimed) is changed like an own module and its
change record is `coord/changes/D4-diagonal-limit-finite-normalization-sharing.md`. The finite clause of
`IsDiagonalLimit` is replaced by the definitionally equal `FiniteCartierNormalization` (the only instance
argument that differs, `HasExt`, is a `Prop`). The two `backward.isDefEq.respectTransparency` options are
switched from `false` to `true`. This switch is not forced: in the reviewer's scratch build the module and the
whole delivery compile with the options left `false` (DiagonalTowerTraceLimit 25 s, item 37 s). All four direct
importers compile with `true` (packet §3b), so the switch is kept.

## No longer needed

None globally. The parent's direct proof dependencies on Cartier reduction,
supported Kummer realization, scalar-unit Ext bijectivity and the exact-cone
projection equation move to the finite boundary node; those dependencies remain
needed. No source-library declaration or unit realization is removed. No old
public import is removed. Redundant imports of `DiagonalTowerTraceLimit` are
removed from the new root modules: those modules use ordinary root cones, not
`IsDiagonalLimit`. The finite-boundary argument uses `DiagonalTraceRootTransport`
through its equation module and does not import the unfinished root-projection
theorem. The source-comparison module needs only the generic Ext presentation
and ordinary trace models. These are dependency
separations within the new argument, not global pruning of the original route.

The combining proof does not use the canonical source-counit equation or the
completed-reduction compatibility field of `IsDiagonalLimit`: the strict Ext
presentation, its finite normalization, the ordinary cones and the whole-system
equation suffice. Those fields and their statement dependencies remain in the
predicate unchanged; they are not globally pruned.

## Where the brief, the DAG or earlier work was wrong

No statement correction is made. The queue was checked on the live server:
this is a proof-route item, with no current rework or build-error entry. The
snapshot's old quarantine entry is stale; the current item source exists.

The DAG's combined projection/finite-class step concealed two different
comparison calculations. These are now explicit, and the normalization of the
ordinary linear root-system isomorphism is proved. Neither equality of arbitrary
derived maps from their finite evaluations nor faithfulness of additive
forgetting on Ext is assumed.

## New nodes

`def-sfb-diagonal-trace-completed-boundary-equation` and
`def-sfb-diagonal-trace-finite-chern-equation` name the original completed
composite equality with generic and concrete shared interfaces, respectively.
Neither adds an assumption or a proof hole.

`lem-sfb-diagonal-trace-finite-cartier-chern-strict` is the proved calculation
from explicit normalized strict-system data and its whole-system equation.
It contains no new hole.

`lem-sfb-diagonal-trace-normalized-root-iso` is the proved, normalized linear
root-system isomorphism.

`lem-sfb-diagonal-trace-normalized-root-cone` is the proved equality between the
transported ordinary root cone and the prescribed coefficient cone.

`def-sfb-diagonal-trace-root-system-transport` is the explicit derived transport
through the strict root isomorphism and canonical single/shift comparisons.

`def-sfb-diagonal-trace-coefficient-root-transport` specializes that transport
to the published coefficient Tate-line endpoint.

`def-sfb-diagonal-trace-supported-source-cone-normalization` and
`def-sfb-diagonal-trace-ext-arrow-presentation` name the existing source-cone
equation and the degree-two Ext presentation equation, respectively. They have
real bodies and add no mathematical condition.

`def-sfb-diagonal-trace-finite-boundary-equation` names the actual supported
finite composite equation without asserting it.

`def-sfb-diagonal-trace-finite-chern-composite` names the actual projected
coefficient Chern composite.

`def-sfb-diagonal-trace-derived-presentation-equation` shares the class equation
on the bundled endpoint data.

`def-sfb-diagonal-trace-ext-source-comparison` forms the source comparison with
abstract category parameters.

`def-sfb-diagonal-trace-ext-derived-presentation` packages the existing chosen
derived presentation, and
`def-sfb-diagonal-trace-supported-source-comparison` names its existing
single-limit source comparison. Neither introduces a proof obligation.

`lem-sfb-diagonal-trace-root-projection` is the root-only finite projection
calculation. It has no Cartier boundary or Chern arrow.

`lem-sfb-diagonal-trace-supported-finite-boundary` is the supported finite
Cartier/Chern calculation. It has no completed diagonal arrow or whole-system
limit characterization.

`def-sfb-diagonal-trace-root-projection-equation` and
`def-sfb-diagonal-trace-supported-boundary-equation` are transparent mathematical
equations with irreducible wrappers and explicitly shared category parameters.
They contain no assertion beyond the displayed composite equalities.

`def-sfb-diagonal-trace-finite-cartier-class` names the actual positive finite
class under exact scalar restriction.

`def-sfb-diagonal-trace-finite-root-normalization` names its existing finite
root endpoint equation.

`def-sfb-diagonal-trace-finite-cartier-normalization` names the identical finite
cycle clause of `IsDiagonalLimit`. These definitions share the expensive
endpoint calculations without adding any assumptions or proof holes.

The existing completed-supported-unit node is retained with its Lean module
attachment moved. Its change record is
`coord/changes/D4-completed-supported-unit-module.md`.

The existing limit-characterization node records the named finite-normalization
dependency. Its unchanged mathematical statement and Lean signature remain in
place; the definition-sharing change is recorded in
`coord/changes/D4-diagonal-limit-finite-normalization-sharing.md`.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 9, "left_out": 0, "own": {"Sheaf.Paper.DiagonalTowerTraceLimit": "df043ce8572a9b0551b2ab37773eb4f674bebc24", "Sheaf.Paper.DiagonalTraceCompletedSupportedUnit": "b79d981a2c3e8036ecc819df795625198e7aebf1", "Sheaf.Paper.DiagonalTraceExtPresentation": "a219ee6d13379df70adde9dc5c0fc47cbc441fa6", "Sheaf.Paper.DiagonalTraceFiniteBoundaryEquation": "7b92fc0d075ca4d23b6190dbcd328666b13fa054", "Sheaf.Paper.DiagonalTraceFiniteCartierChern": "d8cfa27726282abe78df8f14bf5bc3b3c017c7a2", "Sheaf.Paper.DiagonalTraceFiniteCartierChernStrict": "6f21484099727cccf40ad98629bb2c77d47a4c21", "Sheaf.Paper.DiagonalTraceFiniteCartierClass": "0b1c6b2e36fb5fc0b3bfc2571776d916eee87934", "Sheaf.Paper.DiagonalTraceFiniteCartierNormalization": "8fb1d29ed364b16a0a9e7356af34e619d2665138", "Sheaf.Paper.DiagonalTraceFiniteChernComposite": "f37cd2559c1e37a98ea44486059e96516122b985", "Sheaf.Paper.DiagonalTraceFiniteChernEquation": "c437cef72f5c75accdcea77c80f90d4c4f46c47f", "Sheaf.Paper.DiagonalTraceFiniteRootNormalization": "430f1510b25659c68e7d403b62599ffce6e37bbd", "Sheaf.Paper.DiagonalTraceNormalizedRootCone": "8e5dbbbe1296337efa36c57e78ba5e863497df29", "Sheaf.Paper.DiagonalTraceNormalizedRootIso": "c5cb9f3a0427b617f39d42f03e0172e9ae122f2f", "Sheaf.Paper.DiagonalTraceProjectionEquations": "4d0aec4b10fce78f79591129a019946d5c707569", "Sheaf.Paper.DiagonalTraceRootProjection": "e5786f92392ec9cd0de2d6fb44ca27a4e317c6eb", "Sheaf.Paper.DiagonalTraceRootTransport": "fba95ac384bdf5baf313f305116eb96330d837e4", "Sheaf.Paper.DiagonalTraceSupportedFiniteBoundary": "883c62550891ae03ed15f25bdd7fcc20b441be14", "Sheaf.Paper.DiagonalTraceSupportedSourceComparison": "022af64460109c6da21ec8183aef3f3d3c0c2d5b", "Sheaf.Paper.DiagonalTraceSupportedSourceConeNormalization": "03653855877c9f77e09160cd03c7ce5e7b5a6e1b"}, "own_failed": ["Sheaf.Paper.DiagonalTraceFiniteCartierNormalization", "Sheaf.Paper.DiagonalTraceFiniteChernEquation", "Sheaf.Paper.DiagonalTraceRootProjection", "Sheaf.Paper.DiagonalTraceSupportedSourceComparison", "Sheaf.Paper.DiagonalTowerTraceLimit", "Sheaf.Paper.DiagonalTraceFiniteBoundaryEquation", "Sheaf.Paper.DiagonalTraceSupportedFiniteBoundary", "Sheaf.Paper.DiagonalTraceFiniteCartierChernStrict", "Sheaf.Paper.DiagonalTraceFiniteCartierChern"], "results": {}, "time": "2026-10-28T05:04:16+0800", "transitive": 17, "version": 1}
```

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
