## What changed

Reduced `AlgebraicGeometry.Etale.CoordinateTrace.contractions` without changing its
signature. Its first equation is proved by precomposing with the explicit isomorphism
`orderedProjectionIso.hom ≫ push.map comparison.inv`, rewriting its two Kunneth
factorizations, substituting `ht1`, and cancelling the projection/comparison maps.
The second equation specializes the new coefficient-self-symmetry contraction using
the even-line self-symmetry lemma.

Extracted all fourteen canonical helper constructions unchanged into
`Sheaf.AlgebraicGeometry.EtaleCoordinateTraceData`, publicly re-exported by the item,
so the independent proof-step modules can use the same maps without an import cycle.
Their names, signatures, bodies, and public visibility are preserved; blueprint tags
now name their owning definition node. Change record:
`coord/changes/etale-coordinate-trace-data.md`. `tools/downstream.py` reports zero
current Lean importers of the original module; unfinished DAG parents still use its
unchanged theorem, which is retained. No source-library file is modified.

## Proved and sorry left

This is a decomposition of the original one hole, not a complete mathematical proof.
Hole accounting: one original hole closed textually, three new holes added, zero holes
left in the item module; net closure is minus two. No mathematical pruning is claimed.
Closed the textual hole of
`AlgebraicGeometry.Etale.CoordinateTrace.contractions` using the new step interfaces.
The first-conjunct combining argument is explicit Lean, not an application of a
renamed copy of the whole theorem.

New remaining holes, each the whole proof of a public theorem in its own module:

- `AlgebraicGeometry.Etale.CoordinateTrace.coordinateKunnethFactorization`
  (`lem-sfb-etale-coordinate-kunneth-factorization`): the trace-free equality of the
  two canonical Kunneth routes, for arbitrary M and L.
- `AlgebraicGeometry.Etale.CoordinateTrace.evenLineSelfSymmetry`
  (`lem-sfb-etale-even-line-self-symmetry`): only the representative calculation for
  J[2d], for any commutative coefficient ring and integer d.
- `AlgebraicGeometry.Etale.CoordinateTrace.secondCoordinateContraction`
  (`lem-sfb-etale-second-coordinate-contraction`): the second equation for an arbitrary
  coefficient L with explicit identity-self-symmetry hypothesis; no J, d, t1, ht1,
  or first equation is present.

`AlgebraicGeometry.Etale.CoordinateTrace.projectionTraceNormalization` is proved from
naturality of the existing projection map and the existing tensor-unit projection
formula, through a private general-coefficient helper. All six modules compile through
`lcompile.py`; the final item compile completed without diagnostics in 20.8 seconds.
The first equation uses a proved private categorical cancellation helper, which keeps
the large derived functor expressions out of the isomorphism simplification. No
profiler settings, diagnostic placeholders, or temporary proof holes remain.

## No longer needed

Removed the item's proof imports `Sheaf.Paper.RingedKunnethFactorizations`,
`Sheaf.Paper.RingedProjectionTensorComposition`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.LineEvaluationInversePair`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`, and
`Sheaf.Paper.RingedExchangeTensorCoherence`. Also removed its unused public import
`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`. These statements remain genuine
proof dependencies of the split steps, so none is claimed mathematically pruned.
The original remaining public imports are re-exported through the data module.
No node or module is withdrawn, and the unit's projective-line route is retained.

The first-coordinate combining argument uses the native projection naturality and
unit theorem, so it does not need the entire ringed projection/composition theorem
as its normalization input. The ringed theorem is still needed by the second step.

## Where the brief, the DAG or earlier work was wrong

The proof plan correctly describes the mathematics, but its ringed tensor theorems
are stated for `SheafOfModules` over small ringed sites, whereas this item uses
ModuleCat-valued sheaves on the ordinary small etale categories. Substituting f,p1,p2
is not a direct Lean application: the constant-ring/module-sheaf equivalence,
universe transport, tensor representatives, adjunctions, square mates, and normalized
compositors must be identified. The first new step isolates that canonical-map
transport before any trace is applied. The native source library also has
`kunnethMap_eq_of_isPullback`, `tensorBaseChangeMap_eq_projectionMap`, and the
projection composition API. These give one factorization at a time; the new
trace-free step still requires comparing the two coordinate orders and their
specified direct-image compositors. They offer a native alternative to the
ringed transport for its next worker. No statement is disputed or weakened.

New statements were checked on identity f, zero trace, zero ring, empty schemes,
and arbitrary negative/zero/positive d. The first coordinate factorization has no
rank-one requirement; projection normalization has no properness requirement.
Even shifts give the sign (-1)^(4*d*d)=1. An odd shift of a nonzero line in odd
characteristic has self-symmetry -1, so the symmetry step genuinely needs parity.
The second step retains explicit self-symmetry, precisely the property needed when
interchanging the two kernel factors. No claim of local detection of arbitrary
derived maps is made.

## New nodes

`def-sfb-etale-coordinate-trace-data` owns the fourteen existing canonical helper
constructions, moved verbatim and publicly re-exported.

`lem-sfb-etale-coordinate-kunneth-factorization` isolates steps 1–2 of the original
plan in the actual etale interface, before composing a trace. It names the required
normalization and ringed Kunneth inputs.

`lem-sfb-etale-projection-trace-normalization` records the native projection mate's
naturality and right-unit cancellation; its Lean proof is complete.

`lem-sfb-etale-even-line-self-symmetry` isolates original step 4 as an equality of
canonical derived morphisms computed on an explicit flat K-flat one-term model.

`lem-sfb-etale-second-coordinate-contraction` groups original steps 5–6, leaving
the rank-one/parity calculation independent. Each statement carries its source and
complete proof in words. Searches of the whole blueprint, existing nodes and the
library found no duplicate specialized statement; LeanSearch, LeanFinder, Loogle
and Mathlib grep results were checked against their types.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
