## What changed

Proved `AlgebraicGeometry.ProEtale.isIso_app_of_constructibleFiniteTor` in
`Sheaf.Paper.ConstructibleLocalizingDetermination`, with its signature unchanged.
The proof maps the upstream isomorphism locus into the ambient category, checks
that it is localizing, and applies the defining minimality intersection.
Two fully proved private helpers extend coproduct preservation across universes.
They reproduce the existing private small-support proofs from
`Sheaf.Paper.UnboundedLocalizingPullback` (also recorded as
`lem-exc-coproduct-preservation-universe-extension` on private upstream helpers).
The source-library boundary is preserved: no adopted source file is changed.
Updated the item's proof description and dependency list to follow this proof.

Private proof imports now use
`WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators`,
`Mathlib.CategoryTheory.Limits.FullSubcategory`, and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`.
All existing public imports, statements, and instances are unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.isIso_app_of_constructibleFiniteTor`
(node `sk-lem-sf-determination`).
Added zero holes; zero holes remain in the item. No statements were split off.
The private helpers `coproduct_small_support` and `preservesCoproducts_of_small`
are fully proved. Server single-file compilation passed without warnings in 20.4 seconds.
The delivery preflight performs the required axiom checks.

## No longer needed

Removed the private import
`Sheaf.CategoryTheory.Triangulated.LocalizingIsoLocus` and the item's dependency
on `det-sf-determination-localizing`. The existing upstream isoLocus instances
already provide its triangulated and replete structure, and Mathlib's
`isIso_app_coconePt_of_preservesColimit` directly proves the needed closure for
each existing coproduct. This avoids imposing the generic theorem's global
coproduct-existence assumptions on the larger indexing universe.
The unit's shifts/cones/sums/minimality route is preserved. No declaration or
module is withdrawn; this pruning claim concerns this item's dependency only.
No public import was removed. The other original dependencies remain in use.

## Where the brief, the DAG or earlier work was wrong

The generic dependency's Lean statement supplies internal minimality only;
it does not directly conclude generation for a restricted functor domain from
ambient generation. The explicit image-of-locus argument supplies that bridge.
Furthermore, the localizing intersection uses indices in `Type (u+2)` while the
functors are assumed to preserve coproducts only for `Type (u+1)`. The proved
small-support argument handles this distinction, including empty coproducts
and families consisting entirely of zero objects. No hypothesis was added.
Admissibility is retained in the signature, though this categorical proof
works for every coefficient ring with the stated structures.
The existing unit record describes an older thick-generation snapshot; the
current node and main-20261015 proof prescribe the localizing argument followed here.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
