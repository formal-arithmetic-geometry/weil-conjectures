## What changed

Replaced the hole in `WeilConjectures.PurCompactSupport.scalarPull_tensor_coefficient_coherence`
by the representative calculation and objectwise descent. The proof extracts the four existing
normalization equations for the canonical scalar and geometric tensorators. It combines them
using tensorator naturality, naturality of the computation counits, and naturality of the target
representative isomorphism. It cancels the source representative isomorphism and the tensor of
the composite computation counits on the two input representatives. No computation counit
at their total tensor is inverted. Flat-term K-flat resolutions and naturality then give the
unchanged statement at arbitrary derived inputs. A proved private categorical helper carries
out the formal diagram chase without unfolding the concrete sheaf constructions repeatedly.

Added two smaller obligations in new modules. `ScalarPullCoefficientComplexNormalization`
constructs the ordinary module and complex comparisons by the actual normalized adjunctions,
and states the single-complex computation-counit equation. It contains no tensor product.
`ScalarPullCoefficientTotalTensor` states the ordinary signed-total tensor square. It contains
no derived tensor, localization or derived adjunction. Both constructions retain arbitrary
coefficient maps, including nonflat quotients.

The ordinary statement reuses `AlgebraicGeometry.Scheme.proEtaleResolutionTotal`, the
existing signed-total bifunctor, rather than reconstructing its universe-sensitive instances.

The new complex comparison has an explicit composite-functor return type. Local
definitional normalization and a proved generic diagram chase keep the checking cost down.
All three sandbox modules compiled with `lcompile.py --all`; profiling options were then
removed for delivery.

All existing public signatures and imports are preserved. Only the assigned existing module,
its node, and the two new modules and nodes are changed.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurCompactSupport.scalarPull_tensor_coefficient_coherence`
(node `lem-sf-scalar-pull-tensor-coefficient-coherence`).

Added two named holes:

- `WeilConjectures.PurCompactSupport.scalarPull_complex_normalization`
  (`lem-sf-scalar-pull-coefficient-complex-normalization`).
- `WeilConjectures.PurCompactSupport.scalarPull_coefficient_total_tensor`
  (`lem-sf-scalar-pull-coefficient-total-tensor`).

This is a decomposition: one original hole closed and two strictly smaller holes added,
not a complete proof without outstanding dependencies. Neither new theorem repeats the
original equation on representative inputs. The actual derived tensor transport and descent
are proved in this delivery. The item itself has zero remaining holes.

## No longer needed

No existing public import was removed, and no module is withdrawn.
The proof does not use the equal-universe `Sheaf.Paper.RingedSquareTensorCompatibility`
(`lem-weil-pbc-ringed-square-tensor-compatibility`). The ordinary coefficient calculation
is isolated directly in the actual pro-etale universes instead.
The proof does not use the transformation-extension assertion of
`lem-weil-pbc-site-derived-tensor-descent` in
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
objectwise K-flat resolution
(`lem-pc-kflat-resolution`) and naturality suffice for descent.
These removals concern this node's proof route; no claim is made that either module is
unused elsewhere in the project.

## Where the brief, the DAG or earlier work was wrong

The stated general ringed-square dependency uses a common site-object and morphism universe
in `RingedTensorCorner`, whereas the actual pro-etale sites have object universe u+1 and
morphism universe u. Its hypothesis also requires a single-complex normalization for the
comparison; the concrete `scalarPull` definition does not expose that equation. The new
single-variable obligation isolates exactly this missing normalization. The tensor model,
coefficient data, comparison maps, and target statement are unchanged.

Small cases checked mathematically: identity changes and identity geometric maps give the
same unit insertions; zero complexes and zero coefficient rings cause no cancellation of a
noninvertible map; arbitrary nonflat quotient maps remain covered because only computation
counits on flat K-flat representatives are cancelled. The new ordinary total equation needs
no flatness assumption. The single-complex equation uses universal counits without assuming
that they are invertible.

## New nodes

`lem-sf-scalar-pull-coefficient-complex-normalization`: the normalization of the actual
derived adjunction comparison on one complex. Supporting ordinary comparison data are
constructed from the adjunction uniqueness API, without an existential data hole.

`lem-sf-scalar-pull-coefficient-total-tensor`: the ordinary cochain equation obtained from
balanced module tensors and the signed-total summand formula. Its source proof and edge
cases are recorded in its docstring and node.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
