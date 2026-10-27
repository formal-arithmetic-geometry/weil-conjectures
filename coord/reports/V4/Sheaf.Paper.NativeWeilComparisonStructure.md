## What changed

Proved `AlgebraicGeometry.NativeWeilInduction.nativeWeil_comparison_structure` with
its statement unchanged. All helpers are private and proved in the assigned module.
The new proof imports are `Sheaf.Paper.NativeWeilProperNormalization`,
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`, and
`WeilConjectures.CategoryTheory.DerivedExactCompositionComparison`.

The proof computes the specified right-derived Frobenius exchange on its defining
units. A common model calculation then combines this equation, the existing proper
normalization, and the termwise transported structure. Equality of natural
transformations extends the calculation from K-injective models to all derived
objects. The exact open comparison satisfies the same calculation with its inverse
localization factors as units. Naturality pastes the open and proper equations.

No existing definition, signature, instance, attribute, or public import changes.
The unit's `realized` lists are empty and its route is preserved.
The original characteristic binder is retained although the categorical proof is
uniform in it; a scoped linter option documents this intentional unused binder.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.NativeWeilInduction.nativeWeil_comparison_structure`
(node `lem-sf-native-weil-comparison-structure`): one of one original holes.
No holes added or split off. Zero `sorry` remain in the delivered module.

Validation: `lcompile.py` compiled the delivered module cleanly in 23.0 seconds,
with no warnings. The delivery command performs the final packet and axiom checks.

## No longer needed

No original import was removed; the original module imported only the shared
comparison data. No module is withdrawn or claimed globally pruned.

Removed these direct proof dependencies from the assigned node:

- `lem-sf-native-weil-heart-properties` (`Sheaf.Paper.NativeWeilHeartProperties`):
  its large conjunction is unnecessary; the native framework already supplies the
  category instances needed for K-injective representatives.
- `lem-sf-fixed-pair-common-derived-resolution`
  (`Sheaf.CategoryTheory.FixedPairCommonDerivedResolution`): no resolution comparison
  is chosen; the canonical proper comparison's existing unit normalization suffices.
- `lem-derived-exact-equivalence-squares`
  (`Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares`): the proof computes the
  actual specified exchange from its defining canonical units rather than selecting
  compatible square data from an existence theorem.
- `lem-sf-kinjective-derived-map-computation`
  (`Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`): only natural transformations
  are compared. Their equality on K-injective representatives extends by naturality;
  no arbitrary derived morphism is represented by a chain map.

Retained the comparison data, native framework, and proper-normalization nodes.
The existing source-library declarations remain intact. These dependencies are
unnecessary for this proof, with no claim about their other consumers.

## Where the brief, the DAG or earlier work was wrong

The previous plan included more resolution machinery than the equation needs.
The specified comparison and exchange have enough canonical unit equations to
reduce the calculation directly to the termwise transported structure. In
particular, no additional common-resolution or derived-map theorem is needed.

The source's two defining paragraphs were read at the current blueprint path.
The proof uses the actual ambient unbounded derived categories and imposes no
boundedness, finite-type, or constructibility hypothesis. The model calculation
also applies to identity exchanges and zero objects; it uses no division by a
noninvertible derived unit, since cancellation occurs only on K-injective models
(or for the exact open functor).

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
