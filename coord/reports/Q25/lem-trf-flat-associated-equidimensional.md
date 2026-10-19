## Worker report

The item is stated in `lean/Sheaf/TraceFormula/FlatAssociatedEquidimensional.lean`.
The module supplies the reduced closure subscheme `closureSubscheme`, its inclusion and the
induced map `closureMap`; the fibre pullback module `fibreModule`; the stalkwise fibre
association predicate `fibreAssociated`; the relative assassin `relativeAssassin`; and the
pointwise stalk-flatness predicate `moduleFlatAt`. The theorem
`AlgebraicGeometry.flat_associated_equidimensional` has `sorry` as required at stage 2.

The binders render the node statement as follows. `f` and `[LocallyOfFiniteType f]` are the
locally finite-type scheme morphism. `F`, `[F.IsQuasicoherent]` and `[F.IsFiniteType]` are a sheaf of modules
together with Mathlib's quasi-coherence (Stacks 01BE) and finite-type (Stacks 01B5) predicates. `hy` says that `y` belongs to the relative assassin.
`closureSubscheme (f y)` is the reduced closure `T`, and `closureSubscheme y` is the reduced
closure `Y`; `closureMap f y` is the restricted map. `hflat` quantifies every fibre component
and its generic point and asserts stalk flatness over the original base. The first conclusion
says every such generic point lies in the relative assassin. The second chooses one `d : ℕ`
and says every component of every fibre has topological Krull dimension `d`. Empty fibres
contribute no components, exactly as in the source convention.

The construction uses the recorded Mathlib fibre (`Scheme.Hom.fiber`, `fiberι`), topological
`IsGenericPoint`, `irreducibleComponents`, and `topologicalKrullDim`; module pullback is the
recorded `Scheme.Modules.tensorPullback`. The stalk module is
`AlgebraicGeometry.RingedSpace.moduleStalkFunctor`, and flatness uses Mathlib `Module.Flat`
after restriction along `Scheme.Hom.stalkMap`.

## Dependency modules

None after the maintainer review. The delivery originally added a dependency module
`lean/Sheaf/AlgebraicGeometry/CoherentFiniteType.lean` and re-pointed the `lean` record of
`pqf-def-coherent` to it. That change was reverted by the reviewer (see the maintainer note below).

## Searches

The retained stage-1 searches were read and checked: LeanFinder, LeanSearch, Loogle, Mathlib
grep, project grep, whole-DAG grep, and blueprint search found no exact relative associated
point/equidimensionality theorem. Additional source searches covered `relativeAssassin`,
`annihilatorAssociatedPrimes`, `IsFlatOver`, `moduleStalkFunctor`, closure subschemes, and
finite-type sheaf predicates. Mathlib provides the component/fibre/topological primitives but
no theorem with Tag 0GSJ's conclusion. The source declaration search found no existing
`lem-trf-flat-associated-equidimensional` or corresponding theorem.

## Edge cases

I checked the empty-fibre convention, the zero module (which has no associated point), a field
base with an integral affine scheme (dimension zero), `A^1 → Spec(k[t])`, and `xy=t` over
`k[t]`. A module supported only on the closed fibre fails stalk flatness there, so it cannot
satisfy the hypothesis spuriously. The closure construction uses the reduced vanishing ideal,
so the closure is integral and has the intended underlying topological closure.

## Second reading by Q25

I reread the item JSON, all statement dependencies, the recorded declarations and their
signatures, and the Stacks Tags 0GSJ, 0GSI, 05AT, 02OJ and 02NJ cited by the node. Each
hypothesis and each conclusion is rendered by the theorem signature and the helper definitions
listed in its `lean.declarations`. The only interface repaired is the finite-type sheaf
predicate; no statement correction or dispute was needed.

## Maintainer review fix (2026-10-18)

The delivered change to `pqf-def-coherent` was wrong and is left out (`--revert-nodes pqf-def-coherent`).
It replaced that node's recorded declaration `AlgebraicGeometry.RingedSpace.IsCoherent` with a new
`Scheme.Modules.IsQuasiCoherentFiniteType`. The stated reason, that `IsCoherent` means finite
presentation, is false. In `WeilConjectures.AlgebraicGeometry.Coherent`, `IsCoherent` is
Stacks-coherent (finite type, and finite-type kernels of every `O_U^n -> F|_U`, Tag 01BV). The node
records that declaration for its coherent clause, and about 739 nodes cite it. The node's two other
clauses are Mathlib's `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`, as the
recorded module's docstring and the node's `reviewed_lean` note state. So the new conjunction was a
second definition of an existing notion (H4), and the record change took the coherent attachment
away from every citer. The item now takes `[F.IsQuasicoherent] [F.IsFiniteType]` directly. Nothing
else in the statement changed.

