## What changed

Proved `AlgebraicGeometry.Etale.derivedTensor_preservesDirectSums` using the existing
étale derived tensor--Hom adjunction and `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`.
The canonical derived tensor symmetry transfers the result to the flipped tensor functor.
Removed unused generic complex, Grothendieck, K-flat, and tensor-closed imports; the proof now
imports only the existing derived Hom and symmetry APIs. Updated the node proof and dependencies
to record this shorter route and pruned its obsolete tool approvals.

## Proved and sorry left

Closed the sole `sorry`,
`AlgebraicGeometry.Etale.derivedTensor_preservesDirectSums`. No `sorry`s remain and no new
statements were added.

## No longer needed

The proof no longer needs the planned termwise-complex argument or the nodes
`lem-pur-ringed-site-grothendieck-abelian`, `lem-kun-grothendieck-derived-coproducts`,
`lem-kun-flat-resolution-existence`, `lem-kun-derived-tensor-well-defined`,
`lem-pc-sheaf-modules-tensor-closed`, or `def-pc-tensor-complex-sheaves`; their imports were
removed. In full, the removed proof imports are:

- `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian`
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproducts`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`
- `Sheaf.Paper.EtaleFlatKFlatResolution`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`

The two obsolete `tool_uses` entries (ringed-site Grothendieckness and module-sheaf tensor
closedness) were removed. The replacement tool is the existing closed derived-category result
`lem-sfb-derived-monoidal-closed`, used through its already proved étale specialization in
`WeilConjectures.SixFunctors.Etale.Derived.Hom`. This is a generic tool, not a change to the
Künneth unit's route. No unit realization is bypassed.

The generic `def-weil-pbc-derived-categories` and `def-kun-derived-tensor` are already
provided by the public statement imports and need no proof use here.

## Where the brief, the DAG or earlier work was wrong

The original DAG route was unnecessarily low-level: the existing closed derived tensor API
already exposes the required left adjunction, so a direct termwise K-flat construction is
redundant. The statement itself is unchanged. The generic closedness node's current `lean`
attachment names a module absent from the checkout; the source's existing étale specialization
is present, compiles, and has no sorry axioms. No duplicate interface is introduced.

Validation: the final file compiles cleanly in 2.9 seconds through `lcompile.py`. An axiom
probe of this proof reports exactly `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx`. Both variable-preservation statements include every indexing type, hence the
empty indexing type, and impose no boundedness or finiteness hypothesis.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
