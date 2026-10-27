## What changed

Restored the quarantined `Sheaf.Paper.EtaleDerivedScalarTensor` from its current
archive and proved `AlgebraicGeometry.Etale.scalarTensorIso_existsUnique`.
All existing declaration signatures, public imports and definitions are preserved.
The only added imports are private proof dependencies. The final module compiles
cleanly in 49.2 seconds under the unchanged 60-second limit.

The proof first establishes the ordinary balancing isomorphism using the existing
sheafified-adjunction unit-projection theorem. It uses that isomorphism and the
acyclic K-flat tensor lemma to prove preservation of K-flat quasi-isomorphisms by
ordinary etale scalar extension. A private generic calculation constructs the
natural chosen-adjoint representative and applies
`Adjunction.isIso_cochainTranspose_of_kFlat` to it. The fixed tensorator followed
by the single-complex comparison provides a second counit, invertible when its
first complex is K-flat. The cochain K-flat derivability criterion makes both
candidates left derived functors of the same functor. Mathlib's
`Functor.leftDerivedUnique` and `Functor.leftDerived_ext` supply existence,
normalization on every complex, and uniqueness. Transport along the existing
`scalarTensorFunctor_eq` gives exactly the published endpoint.

The generic counit and comparison calculations are adapted from the existing
private proofs in `SupportedEtaleTensorOrigin`; that downstream module cannot
be imported because it imports this item. All the private helpers here are
proved. No public helper or new mathematical statement is introduced.

The node's proof route is updated to this argument. Its statement and statement
dependencies, the unit route, and its Lean attachment are unchanged.

## Proved and sorry left

Original holes: 1. Closed: 1. Added: 0. Remaining: 0.

Proved `AlgebraicGeometry.Etale.scalarTensorIso_existsUnique`
(node `lem-route-scalar-tensor-iso-exists-unique`). There are no split-off holes
and no remaining `sorry` declarations in the delivered module.

## No longer needed

No existing import is removed and no module is withdrawn. Two proposed proof
imports are unnecessary and are not added:

- `Sheaf.Paper.ScalarSheafTensorPullback`, node
  `lem-pur-scalar-sheaf-tensor-pullback`: only ordinary balancing is needed,
  supplied directly by the existing proved sheaf unit-projection API. The
  geometric pullback square is not used.
- `Sheaf.Paper.FiniteScalarRepresentativeIso`, node
  `lem-pur-finite-scalar-representative-invertible`: its recorded Lean theorem
  applies to pro-etale sheaves. The existing generic exact-right-adjoint K-flat
  representative theorem applies directly to the etale category instead.

These two nodes are removed from this node's proof dependencies and obsolete
tool approvals. They remain available for their other consumers; neither is
claimed to leave the global target closure. All category prerequisites, exact
restriction factorization, the fixed derived monoidal structure and unary
K-flat derived-functor calculus remain used.

## Where the brief, the DAG or earlier work was wrong

The item is absent from `lean/` because it was quarantined, not withdrawn.
Its row in `coord/rework.tsv` and archive were read before restoration. The
recorded earlier bad import of
`WeilConjectures.SixFunctors.ProEtale.ScalarExtension` is now resolved: the
archived item compiled against the current server dependencies without edits.

As the stage-1 reader already noted, the finite scalar representative theorem
recorded in the DAG is pro-etale only. The generic
`Adjunction.isIso_cochainTranspose_of_kFlat` proves the required etale instance
and avoids a dependency cycle through the supported-origin module. No statement
was changed or weakened, and no target or shared definition was edited.

Edge cases were checked in the argument: neither ring nor the scheme is assumed
nonempty or nonzero; the identity coefficient map and the map to the zero ring
are covered; no flatness of B over A is used. The tensor comparison is inverted
only on K-flat first arguments. Normalization on arbitrary complexes comes from
the derived-functor counit equation, so no invalid cancellation on a non-K-flat
complex occurs.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
