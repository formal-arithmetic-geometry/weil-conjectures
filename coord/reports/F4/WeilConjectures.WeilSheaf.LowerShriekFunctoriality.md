## What changed

Filled three theorem proofs in `WeilConjectures.WeilSheaf.LowerShriekFunctoriality`.
A proved private helper identifies open compact support with termwise extension by zero on
all bounded constructible native Weil complexes. Its degree-zero component proves the first
hole. The localization proof takes the degreewise native heart sequence to the derived
category and transports its triangle directly to the three existing Weil-complex values.
Composition uses a compatible compactification tower, the native tower calculation, and
model comparisons, then reflects the natural isomorphism through the fully faithful inclusion.

Added private proof imports of `NativeBasicComparisons`, `NativeOpenProperInterchange`,
`NativeCompatibleTowerCalculation`, `NativeCompactificationModelComparison`,
`CompactifiableCompatibleTower`, `NativeImmersionHeartLocalization`, the existing native
`Localization` module, and Mathlib's derived short-exact-sequence triangle module.
Updated the open-comparison, native-localization, and composition DAG proofs to describe the
actual route. Three further proved private helpers construct the ambient localization
triangle, instantiate that construction on native Weil sheaves, and transport it into the
full subcategory. Local instance priorities follow the existing native localization module's
coefficient-instance convention.
Existing public signatures, public imports, attributes, docstrings, and definition bodies are
preserved. No other module is adapted and no definition or statement repair is made.

The complete module compiled through the required `lcompile.py` in 13.8 seconds, with kernel
checking. Diagnostic options, checkpoints, and traces have been removed. The final source is
also checked by the delivery command's compile and preflight.

The argument covers empty open or closed parts without a case exclusion. It chooses an
arbitrary complex representative of K, with an explicit representative isomorphism; it never
requires a bounded representative. The coefficient categories remain the actual native
fixed-pair-before-deriving categories throughout.

## Proved and sorry left

Closed 3 of the item's original 4 holes:

- `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion`
  (`lem-sf-weil-open-immersion-compact-image-extension-by-zero`).
- `AlgebraicGeometry.WeilComplex.exists_distTriang_openClosed`
  (`lem-sf-native-weil-open-closed-triangle`, also attached to
  `lem-sf-weil-open-closed-triangle-exists`).
- `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_comp_iso`
  (`lem-sf-native-weil-shriek-composition`).

The existing proved `exists_distTriang_derivedLowerShriek_openClosed` now uses the completed
localization and composition proofs. Both original proper-comparison definitions are untouched.

One inherited hole is left unchanged:
`AlgebraicGeometry.WeilComplex.nonempty_upperStar_derivedLowerShriek_iso`
(the current `prop-functor-package` Lean attachment).
Added holes: zero. Split-off statements: zero. All four private helpers have complete proof bodies; none contains a `sorry`.
This is a partial delivery, not a decomposition or a claim of final axiom closure.

## No longer needed

No original import is removed, no Lean declaration is withdrawn, and no whole module is
claimed globally pruned. All eight added imports are used by the completed proofs.

For `lem-sf-weil-open-immersion-compact-image-extension-by-zero`, removed the separate proof
edges to `lem-sf-native-weil-open-exact-constructible` and `def-sfb-right-derived-functor`.
The existing extension exactness instances and Mathlib's single-object factorization suffice;
the native derived identity comparison supplies the identity step. The corresponding unused
planned imports are `Sheaf.AlgebraicGeometry.NativeWeilOpenExactConstructible` and
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`.
These modules can still be needed by other consumers.

For `lem-sf-native-weil-open-closed-triangle`, removed the separate proof edges to
`lem-weil-pbc-exact-functor-complex-cohomology`,
`lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-immersion-base-change-lft`, `lem-sfb-finite-type-composition-base-change`,
`def-weil-compactifications-refinements`, `def-weil-finite-type-morphism`,
`def-weil-open-immersion`, `def-weil-closed-immersion`, and `def-weil-proper-morphism`.
The first is unnecessary because the transported vertices already have their object-property
proofs from the restricted operations. The geometric hypotheses of the private open helper
use the existing compactification API, including `quasiCompact_openImmersion`, so the old
separate Noetherian argument is unnecessary. The geometric interfaces remain available through
the framework and are still used in other proofs; these removals are local DAG edge pruning.

For `lem-sf-native-weil-shriek-composition`, removed the separate proof edge to
`lem-sf-native-weil-shriek-triangulated`. Both sides are already the existing restricted
functors, identified in the ambient category by the model comparisons. Fully faithful
whiskering reflects the resulting natural isomorphism directly; there is no new
bounded-constructibility check. This is also local edge pruning, not withdrawal of the node.

## Where the brief, the DAG or earlier work was wrong

No statement was changed or disputed. The native localization plan's extra cohomology and
Noetherian checks can be omitted by transporting the triangle to the already constructed
bounded constructible values and using the compactification's quasi-compactness theorem.

For the remaining base-change hole, the source proper-base-change declaration
`WeilComplex.nonempty_upperStar_derivedLowerStar_iso_of_isProper` supplies only an objectwise
`Nonempty` isomorphism, not a natural isomorphism or a statement about a prescribed exchange.
Choosing those objectwise isomorphisms does not establish naturality. The current
`prop-functor-package` proof dependencies concern the larger coefficient-stage package, and
cannot simply be applied as a natural comparison on these native derived Weil categories.
The fourth hole and its current attachment are left unchanged for subsequent work.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
