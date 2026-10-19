## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleDerivedPullback_identity` with its full
original signature and all normalization formulas. Private helpers compute the
ring comparison by adjunction conjugacy, identify the canonical coefficient map,
and construct the natural module comparison from the existing uniquely normalized
module identity result. The scalar-extension comparison supplies both tensor
formulas. Mathlib maps it termwise to complexes and descends it through localization.

Added the proof-only import
`Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison` for its existing
`moduleId_exists`; no public interface, definition, or target statement changed.
Updated the original DAG node to record this dependency and the actual proof.
The full module compiled cleanly through `lcompile.py` in 54.3 seconds, with no
warnings. The declaration diff confirms that existing signatures are unchanged.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.proEtaleDerivedPullback_identity`.
No sorry remains in the delivered module; no holes or public lemmas were added.
The existing dependency `ProEtaleTensorComparison.moduleId_exists` supplies its
uniquely unit-normalized module comparison. Other existing dependencies retain
their own proof obligations; they are not new holes in this delivery.

## No longer needed

Removed redundant proof-only imports `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
and `Sheaf.CategoryTheory.RingedSiteModules`: the used definitions are already
publicly imported by the retained scalar-extension and inverse-image modules.
Their nodes remain needed; no original DAG dependency is bypassed. The inherited
public imports preserve the existing reexports. No new split nodes are needed:
the algebraic-component and localization drafts from the interrupted work were
never delivered and have been removed from the sandbox.

## Where the brief, the DAG or earlier work was wrong

The original route works, using the existing module identity normalization API
rather than rebuilding module inverse image section by section. The interrupted
report describing two unresolved component theorems was obsolete. No statement
repair or change record is needed. Zero rings and empty schemes remain included:
the proof assumes neither nontriviality nor nonemptiness.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
