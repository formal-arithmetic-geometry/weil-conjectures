## What changed

Proved `AlgebraicGeometry.comparisonPullbackExact` in
`Sheaf.Paper.ComparisonPullbackExact`, without changing either existing declaration's
signature or the definition of `comparisonConstantRingMap`.

The constant-ring isomorphism comes from uniqueness of the composite constant-sheaf
and comparison adjunctions. Applying both hom-equivalences proves that its forward
map is the prescribed canonical map. Four proved private helpers construct the
sectionwise tensor contraction, its inverse, and the natural presheaf isomorphism.
Sheafification and its triangle identity give exactly the required formula.

The existing source library's comparison functor already has the additive,
finite-limit, finite-colimit and homology-preservation instances. These directly
supply exactness; Mathlib supplies the natural homology isomorphism and preservation
of quasi-isomorphisms. Mapping zero objects and the homology isomorphism prove the
final vanishing clause, with the original arbitrary integer bound.

Removed seven unused proof imports against the current source. Updated the node's proof, proof dependencies,
proof origin and obsolete tool-use entries to match this argument. The unit
`sk-def-sf-operations` has no realized proof steps to bypass. All existing public
imports remain unchanged.

Validation: the final pruned file compiled through `lcompile.py` with no warnings.
`#print axioms AlgebraicGeometry.comparisonPullbackExact` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. Delivery checks are recorded by
the delivery tools.

## Proved and sorry left

Closed: `AlgebraicGeometry.comparisonPullbackExact`
(blueprint: `lem-sf-comparison-pullback-exact`), the item's sole original sorry.

Holes closed: 1. Holes added: 0. Split-offs: 0. No sorry remains in the item or is
added elsewhere. This is a proof, not a decomposition.

## No longer needed

Removed proof imports and their corresponding proof dependencies/tool-use entries:

- `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`
  (`lem-weil-pbc-adjunction-lifts-group-ring-objects`): the ring-valued comparison
  adjunction is already constructed, so no lift through ring objects is needed.
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`
  (`lem-weil-pbc-sheaf-algebraic-structures-objects`): likewise no equivalence with
  algebraic objects is needed.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
  (`lem-weil-pbc-ringed-topoi-module-adjunction`): the displayed scalar extension
  is already defined; its underlying tensor comparison is constructed directly.
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
  (`lem-weil-pbc-site-pullback-abelian-exact`): the source library already proves
  exactness directly for the fixed-coefficient comparison functor.

Also removed `def-weil-derived-cohomology-sheaves` and
`def-weil-pbc-derived-categories` from proof dependencies: the complex conclusions
are Mathlib homology statements and follow directly from its homology API. These
remain statement dependencies; all existing public imports are preserved. The newer
proof imports generated from their updated Lean attachments are also unnecessary:

- `Sheaf.Paper.SfCommonStageWeilCohomology`: the conclusion concerns homology
  of ordinary complexes, without common-stage Weil coefficients.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the conclusion does
  not use torsion-cohomology subcategories of a derived category.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: no monoidal
  structure on cochain complexes is used. The needed scalar-extension API of
  `def-pur-sheaf-tensor-product` is retained through the existing public import
  of `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`.

No assertion is made that these modules cease to be needed by other parents.

## Where the brief, the DAG or earlier work was wrong

The original DAG planned a generic transport through ring objects and abelian
sheaves to obtain exactness. This is unnecessary for the actual fixed-coefficient
functor: `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs` already supplies
its exactness instances. The constant-sheaf calculation and explicit tensor
contraction still prove every clause of the unchanged statement.

No statement or definition repair was needed. No new nodes.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
