# WeilConjectures.PointQuotientTower proof context

## Reason

Fill five existing theorem holes using the published canonical reduction and pullback
constructions. The proof adds fully proved private helpers, private additive instances,
and local elaboration commands. These commands are recorded because the interface gate
can conservatively classify them as changes outside theorem bodies. No existing public
statement, definition, instance body, visibility or public import is changed.

## Old

The existing module-level elaboration commands were:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointQuotientTower
```

The six public theorem statements are unchanged. All six originally had `by sorry` bodies.

## New

The original commands remain. Local irreducibility keeps the completed coefficient
objects, scalar-reduction witnesses, standard localization, unit, transition, and exact
derived functor constructions folded. No existing global attribute or instance body is changed.
The augmentation proof locally excludes `CategoryTheory.catToReflQuiver` to select
canonical category morphisms and enables `backward.isDefEq.respectTransparency`.

The private additive instances prove additivity of the two existing level functors.
The private source-transition candidate is built directly in each degree with the
existing `unrestrictedModuleStep`, using its naturality for the chain and natural
transformation equations. This avoids an expensive kernel comparison between
composite mapped-complex functors. The private transition helpers identify the
selected transitions with their normalized constructions and prove naturality for
arbitrary module maps. Private
presentation equalities compare the reordered section functor and ordinary-reduction
wrappers; their proofs unfold only those wrapper definitions. A private coefficient
identity records that the finite transition sends the commutative-ring unit to the
commutative-ring unit. The augmentation proof checks compatibility with each strict transition on local
pure tensors before applying sections and `Functor.constComp`. Every helper is fully proved.

Proof-only imports expose the already proved construction helpers in
`Sheaf.Paper.IntegralOperationsWellDefined` and
`Sheaf.Paper.IntegralReductionTowerUnrestricted`. The former private imports of
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel` and
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage` are removed as redundant.
The public imports and existing construction bodies remain verbatim.

## Users

A source search finds no current direct Lean importer or textual qualified consumer
of this module. Its DAG parents with unfinished proofs continue to need the node;
this delivery withdraws nothing. No public declaration changes its interface or
mathematical meaning, so there is no consumer adaptation or target-statement repair.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PointQuotientTowerHomotopy | T1 | Five original proof bodies filled; original coherentSource hole retained. |

## Status

landed 20261026T071035-L-3793529 2026-10-26 (merge of deliver/T1/Sheaf.Paper.PointQuotientTowerHomotopy)
