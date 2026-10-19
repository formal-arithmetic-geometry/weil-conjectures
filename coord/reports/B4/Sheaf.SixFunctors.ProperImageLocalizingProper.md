## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.proper_image_localizing_proper`
without changing any existing signature or definition. The proof follows the first
step of `det-proper-image-localizing-proper`: intersect the source localizing closure
with the inverse image of the target closure, check its triangulated, replete and
coproduct closure properties using precisely the supplied hypotheses, and apply
minimality. The standard full-subcategory lift is triangulated and preserves sums.

The fully proved private helpers establish the closure properties of the defining
intersection, functoriality of that closure, and the size reduction for coproducts.
For the last helper, the nonzero summands inject into the endomorphisms of the
coproduct by their projection/inclusion idempotents. Shrink this support to the
Hom universe, use preservation there, and insert the zero summands back. This
handles every existing larger coproduct, including the empty family.

Added proof-only imports `Mathlib.CategoryTheory.Limits.FullSubcategory` and
`Sheaf.CategoryTheory.GrothendieckDerivedCoproducts`. The latter's proved
`CategoryTheory.derived_hasCoproducts` supplies ambient coproducts at the Hom
universe. Colimits in the module category and their size conversion are supplied
explicitly to avoid divergent typeclass search. All public declarations, docstrings,
and the unit's proof route are unchanged. The node's first proof step and its
dependency list now record the generic coproduct tool and the support argument;
the coefficient steps are unchanged.

## Proved and sorry left

Closed 1 of the original 2 holes:
`AlgebraicGeometry.ProEtale.CondensedRing.proper_image_localizing_proper`.

The one original hole left is
`AlgebraicGeometry.ProEtale.CondensedRing.proper_image_localizing_proper_coefficients`
(node `det-proper-image-localizing-proper`). Its statement, docstring and whole
`by sorry` proof are unchanged. It still needs the finite, rational and integral
coefficient arguments of steps 2--4 of that node, including their coefficient
identifications and the conversion of cofan comparisons to colimit preservation.
No holes were added and no obligations were split off.

Validation: the delivered module compiled cleanly using `lcompile.py` (5.9 seconds).
The delivery dry run also checks the declarations and their axioms.

## No longer needed

None. No dependency node or module is bypassed. All ten proof-dependency imports
removed by the retained attempt have been restored for the unchanged open coefficient
theorem; no original import is removed in this delivery. The original imports continue to
supply the definitions, ambient exactness, and the planned coefficient theorem,
which remains open. The two added imports are used by the proved restriction.

## Where the brief, the DAG or earlier work was wrong

The retained attempt did not compile: its support reindexing rewrote an equality
before exposing the selected cofan leg, and its inclusion argument requested
ambient coproduct instances not in scope. The repaired proof explicitly changes
the selected leg, applies the inverse-equivalence equation there, and supplies
ambient coproducts from the proved generic theorem. The original report incorrectly
said that no imports were added; the exact additions are listed above. There is no
statement correction, definition repair, or consumer adaptation.

The administrative change record is
`coord/changes/B4-proper-localizing-private-helper-scope.md`; it documents the
extra private-helper universe names and local scoped openings flagged by preflight.
No definition, existing signature, or consumer changes.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
