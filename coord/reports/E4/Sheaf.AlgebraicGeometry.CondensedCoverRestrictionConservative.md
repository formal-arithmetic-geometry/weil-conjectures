## What changed

Restored `lean/Sheaf/AlgebraicGeometry/CondensedCoverRestrictionConservative.lean` from the
quarantine path recorded in `coord/rework.tsv`, and replaced its one `sorry` by a complete
proof. A proved private helper shows joint conservativity on coefficient module objects:
extension along `condensedPullbackHom` is naturally inverse scalar restriction, so forgetting
modules reduces to the existing `upperStarIsoLocalizationRestriction` and
`isIso_of_isIso_localizationRestriction`. The existing natural exact-functor homology
comparison and `DerivedCategory.isIso_iff` lift this to the unbounded derived category.
The zero-detection clause follows by applying conservativity to `K ⟶ 0`.

The theorem signature, its original docstring, the node's `lean` attachment, statement and
statement dependencies are unchanged. The node's proof, proof dependencies and origin now
follow the Lean proof. There are no new declarations with postponed proofs or data choices.
The import-interface restoration/pruning record is
`coord/changes/E4-condensed-cover-restoration.md`.

Validation: the actual module compiles remotely with the minimal imports. A scratch copy
with `#print axioms AlgebraicGeometry.ProEtale.condensed_cover_restriction_conservative`
compiles and reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
No boundedness or coefficient finiteness is used. Empty covering families require no choice
of a member: the underived cover-local criterion handles the empty-scheme case.

## Proved and sorry left

Closed the archived hole in
`AlgebraicGeometry.ProEtale.condensed_cover_restriction_conservative`
(node `lem-zl-condensed-cover-restriction-conservative`): 1 of 1 holes proved.
The new private helper `AlgebraicGeometry.ProEtale.isIso_of_condensed_cover` is proved.
Remaining holes in the item: zero. Holes added anywhere: zero. Split-off statements: zero.
The public theorem depends on no postponed proof, as confirmed by its axiom list.

## No longer needed

Removed these unused direct imports:

- `Sheaf.CategoryTheory.RingedSiteModules` (public): the actual statement uses `Mod`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` (public): coefficients are arbitrary
  condensed ring objects, and the source coefficient comparison is already invertible.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization` (public): the proved source
  `upperStarIsoLocalizationRestriction` supplies the required comparison directly.
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction` (public): neither its
  normalized Kan-index data nor its constant-module comparison is required.
- `Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties`: the source cover-local criterion
  already proves the covering-sieve argument.
- `Mathlib.CategoryTheory.Sites.LocalProperties`: accessed through the proved source criterion.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`: the proved source derived
  cohomology comparison already carries out the descent.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: reexported by the exact-functor API.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: reexported by the statement import.

The proof no longer invokes the separate nodes
`lem-weil-proetale-weakly-etale-localization`,
`lem-sfb-proetale-object-inverse-image-restriction`,
`det-pe-topos-functoriality-site`, `def-weil-pbc-proetale-operations`, or
`def-weil-sheaf-of-modules-category` as proof dependencies. Their statement dependencies
remain intact where originally specified; this is not a withdrawal. Removed both obsolete
`tool_uses` approvals, for the object-inverse-image and site-properties nodes. The module-object
pullback, scalar-extension-along-isomorphism and module-object-category nodes describe the
adopted APIs actually used instead. No unit statement or unit proof step is bypassed.

A source-import closure comparison finds no module eliminated from this item's transitive
closure: the removed direct imports are already reached through retained imports. Thus this
packet claims one genuine hole closure and direct-import cleanup, not any globally pruned
module or an archived module withdrawal.

## Where the brief, the DAG or earlier work was wrong

The live module's absence is a recorded quarantine rollback, not evidence that the result is
unused. Its archive is restored with the same public theorem and mathematical statement.
The original six-step plan is mathematically sound but repeats infrastructure already proved
in the adopted library: scalar transport, local detection on a cover, reflection by the
module forgetful functor, and the natural derived cohomology comparison. Reusing those
results closes the theorem without splitting any new hole. The source HRS Lemma 4.5 proof
asserts conservativity on a w-contractible affine cover; the general family form here is
justified by the existing arbitrary-cover sheaf criterion. No disputed statement was found.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
