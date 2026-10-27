## What changed

Proved `AlgebraicGeometry.Etale.compactInternalAdjunctionExchange` from the canonical
upstream right-coefficient projection/exchange equality. The proof cancels the invertible
compact exchange, tensor comparisons and pullback-square comparison, then takes mates
through the ordinary, tensor--Hom and exceptional adjunctions.

Added two completely proved support modules:

- `Sheaf.AlgebraicGeometry.CompactHomMonoidalCompatibility`: the general mate calculation
  for abstract lax monoidal functors and compatible compact projection squares.
- `Sheaf.AlgebraicGeometry.CompactInternalAdjunctionMateIdentification`: its specialization
  identifying the ordinary, internal-Hom and exceptional maps with their canonical
  definitions.

The item adds proof-only imports of
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange` and
`Sheaf.AlgebraicGeometry.CompactInternalAdjunctionMateIdentification`. The latter imports
`CompactHomMonoidalCompatibility` only for its proof. Public imports of the new modules
supply the declarations used in their signatures. Every existing public declaration,
definition body and public import in the item is preserved.

Profiling located expensive definitional conversions of the derived tensor--Hom
adjunction and concrete pullback functors. Keeping the functors abstract during mate
rewrites and matching the canonical isomorphism-component expressions reduced those
costs. The complete single-file proof still took 97 seconds, so the two proved parts
were moved into support modules, as allowed by the current worker brief, step 3a.
No shared definition or existing module other than this item was changed.

Validation: remote `lcompile.py --all` compiled all three modules in dependency order
with exit code 0 and no warnings. Static comparison confirmed preservation of the
original definition, equality API and theorem signature; all DAG proof-dependency
lists agree with their proof steps.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Etale.compactInternalAdjunctionExchange`
(node `lem-asd-compact-internal-exchange`).

Also proved the new support declarations
`AlgebraicGeometry.Etale.compactHomMonoidalCompatibility` and
`AlgebraicGeometry.Etale.compactInternalAdjunctionExchangeOfMateCompatibility`.

Original holes closed: 1 of 1. Holes remaining in the item: 0.
Holes added anywhere in the delivery: 0. Split-off unproved statements: 0.
All private helpers have complete proofs. No data definition, axiom or arbitrary
choice from an unproved existence statement was introduced.

## No longer needed

Removed the item's proof-dependency edge to `lem-asd-compact-projection-exchange`.
Its coefficient-first symmetry conversion, in
`Sheaf.AlgebraicGeometry.CompactProjectionExchange`, is unnecessary: the compact internal
adjunction is conjugate to the right-coefficient projection map, and the exact upstream
right-coefficient projection/exchange equality is already proved. The item uses that
upstream declaration directly. The DAG now records this route and both proved support
nodes.

No existing import was removed, no module was withdrawn, and no adopted-source
declaration was removed or weakened. No whole module is claimed pruned from the targets'
import closure. The blueprint unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement required correction. The coefficient-change compatibility
already in `TensorHom` fixes one scheme morphism, whereas this item compares `f` and
`f'`. The underlying mate/conjugation identity applies to the required different
source and target categories; the first support module proves this specialization.

The older `coord/brief-stage3.md` prohibition on splitting for timing conflicts with
step 3a of the current worker brief. Followed the current explicit instruction after
profiling and optimizing the expensive conversions. Both extracted parts are proved;
no obligation has been renamed or deferred.

## New nodes

`lem-asd-compact-hom-mate-compatibility` realizes the proved general projection/mate
calculation in `CompactHomMonoidalCompatibility`. Its source is the blueprint's final
compact-adjunction compatibility argument and the adopted general mate calculus.
The hypotheses express the compatible left-adjoint projection squares; the conclusion
is their right-adjoint compatibility. The argument uses only adjunction identities,
including for zero complexes and empty schemes.

`lem-asd-compact-hom-mate-identification` realizes the proved canonical specialization
in `CompactInternalAdjunctionMateIdentification`. It identifies the maps produced by
the preceding calculation with ordinary base change, internal-Hom pullback comparison,
precomposition by inverse compact exchange, and its exceptional mate. The main item
supplies the projection compatibility from the upstream theorem. There are no change
records because no existing statement, definition or public interface was changed.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
