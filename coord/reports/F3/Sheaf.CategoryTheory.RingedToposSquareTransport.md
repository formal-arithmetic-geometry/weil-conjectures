## What changed

Proved `CategoryTheory.ringedTopos_squareTransport` with its entire original
signature unchanged. The proof follows all three steps of the existing plan:
transport the two rings, lift the bottom structural map by full faithfulness,
and construct the compatible additive module direct images.

Added four fully proved support modules: `RingedToposRingData` separates the
geometric/ring fields from their module lift without changing the original
`RingedToposMorphism`; `AdjunctionRingOperations` proves the counit equations for
terminal and binary operations; `RingedToposEquivalenceRingTransport` transports
one ring sheaf with its canonical structural isomorphism; `RingedToposRingSquare`
constructs the bottom ring map and proves the commutative-square equation.

Added the fully proved `SheafOfModules.ringData_inducedModules` theorem to the
unclaimed `GeometricModuleConstruction` module to reuse its concrete private
module operations. Every original declaration in that module is unchanged.
The new result proves additivity and the exact generalized-element scalar-action
identity needed by the unchanged ringed-topos interface. The record is
`coord/changes/ringed-topos-induced-module-direct-image.md`.

The transported rings use the existing finite-product ring functor and the
explicit sectionwise reconstruction theorem. Their five operation equations
specify the ring structures on the fixed underlying sheaves. The module functor
is the existing concrete image functor, with restriction of scalars along the
adjunct of the structural map. No data are selected from unspecified existence.
The constructions use finite-product and pointwise equations, valid also for
empty sites and the zero ring.

All six delivered modules compile without warnings through `lcompile.py --all`;
the final square theorem takes 8.8 seconds and the longest file 34 seconds.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.ringedTopos_squareTransport`
(node `lem-weil-pbc-ringed-topos-square-transport`).

Holes closed: 1. Holes added: 0. No `sorry` remains in any delivered module.
This is a proof, not a decomposition. In particular the single-ring transport,
bottom ring map, ring reflection lemmas, counit operation lemmas, and the induced
module construction (including additivity and `module_linear`) are all proved.

## No longer needed

Removed the parent proof import `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`
and its dependency `lem-weil-pbc-sheaf-algebraic-structures-objects`: the aggregate
existence statement does not expose the operation equations needed here. The
proof instead uses the concrete ring operations and the existing, more specific
`WeilConjectures.CategoryTheory.SheafRingObjectReconstruction` theorem
`sheafRingObject_sectionwise_reconstruction`. The removed aggregate is not needed
by this proof; no claim is made about other target paths.

Removed both duplicate direct imports of
`WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor` from the
parent. Its theorem and node `lem-weil-pbc-finite-product-ring-functor` remain
needed in the single-ring transport module and are not pruned from the route.

Removed the parent's direct proof import `Sheaf.CategoryTheory.RingedSiteModules`.
Its definitions and node `def-weil-sheaf-of-modules-category` remain required by
the unchanged interface, transitively imported via `RingedToposMorphism` and the
module construction. Removed the unnecessary `Mathlib.CategoryTheory.Equivalence` import from the
new ring-square helper, whose statements only need natural isomorphisms and
full faithfulness, already available from the ring-data interface. No module
is withdrawn. The unit route is unchanged.

A source-import closure comparison for this item finds the following thirteen
project modules no longer needed by this route. This is pruning from the item,
not a claim that no other target imports them. The node names are their current
Lean attachments; no DAG node is deleted.

| module no longer imported by this item | node |
| --- | --- |
| `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects` | `lem-weil-pbc-sheaf-algebraic-structures-objects` |
| `WeilConjectures.CategoryTheory.SheafAbelianObjectsBijective` | `lem-weil-pbc-sheaf-abelian-objects-bijective` |
| `WeilConjectures.CategoryTheory.SheafAbelianObjectsInjective` | `lem-weil-pbc-sheaf-abelian-objects-bijective-injective` |
| `WeilConjectures.CategoryTheory.SheafAbelianObjectsSurjective` | `lem-weil-pbc-sheaf-abelian-objects-bijective-surjective` |
| `WeilConjectures.CategoryTheory.SheafRingObjectsBijective` | `lem-weil-pbc-sheaf-ring-objects-bijective` |
| `WeilConjectures.CategoryTheory.SheafRingObjectsInjective` | `lem-weil-pbc-sheaf-ring-objects-injective` |
| `WeilConjectures.CategoryTheory.SheafRingObjectsSurjective` | `lem-weil-pbc-sheaf-ring-objects-surjective` |
| `WeilConjectures.CategoryTheory.SheavesAbelianForward` | `lem-weil-pbc-sheaf-abelian-forward` |
| `WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian` | `lem-weil-pbc-sheaf-algebraic-structures-abelian-component` |
| `WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects` | No separate Lean attachment |
| `WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRing` | `lem-weil-pbc-sheaf-algebraic-structures-ring-component` |
| `WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore` | `lem-weil-pbc-sheaf-algebraic-structures-ring-core` |
| `WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingMorphism` | `lem-weil-pbc-sheaf-algebraic-structures-ring-morphism` |

## Where the brief, the DAG or earlier work was wrong

The plan is mathematically correct. Its description of the induced module
construction as a single step conceals the additivity and adjunction
scalar-action calculations. These are now fully formalized using the existing
module-operation construction. The broad ring/sheaf correspondence statement was
not the shortest usable interface; explicit sectionwise reconstruction supplies
the required operation equations. No statement is disputed or weakened, and no
target signature or interpretation changes.

## New nodes

`def-weil-pbc-ringed-topos-ring-data`: the exact geometric/ring fields of the
original interface, their module-lift record and assembly, and faithful
reflection of ring operations. Implemented and proved in
`Sheaf.CategoryTheory.RingedToposRingData`.

`lem-weil-pbc-adjunction-ring-operations`: counit compatibility with constants
and product operations. Proved from naturality and projection equations in
`Sheaf.CategoryTheory.AdjunctionRingOperations`.

`lem-weil-pbc-ringed-topos-equivalence-ring-transport`: one-ring transport with
specified direct/inverse image, canonical structural map and its invertibility.
Fully proved in `Sheaf.CategoryTheory.RingedToposEquivalenceRingTransport`.

`lem-weil-pbc-ringed-topos-ring-square`: construct the lifted bottom ring map,
prove its ring identities by faithful reflection, and prove the square equation.
Fully implemented in `Sheaf.CategoryTheory.RingedToposRingSquare`.

`lem-weil-pbc-ringed-topos-induced-modules`: concrete additive module direct
image with the exact Hom-adjunction action identity. Fully proved as
`SheafOfModules.ringData_inducedModules` in the existing module
`Sheaf.CategoryTheory.GeometricModuleConstruction`. Its change record is
`coord/changes/ringed-topos-induced-module-direct-image.md`.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
