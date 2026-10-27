## What changed

Proved `WeilConjectures.CanonicalOpenRestriction.finiteRestrictionMate_isIso` in
`Sheaf.Paper.OrdinaryOpenFiniteRestrictionMate`, without changing any public signature,
definition, attribute, or public import. Added only private proved helpers and the proof import
`Mathlib.CategoryTheory.Sites.CoverLifting`.

The proof uses the subterminal open object to prove that both open-adjunction units are
isomorphisms. The right triangle makes the integral counit invertible after restriction.
Sectionwise scalar extension and the natural slice/sheafification comparison preserve that
restricted isomorphism. Each factor in `finiteRestrictionMate_app` is consequently invertible.
The coefficient-equivalence units and inverse equivalence are retained throughout.

Updated the item's DAG proof, proof dependencies and proof origin to describe this argument.
The unit route is preserved. All helpers are proved; no new public declaration or node is added.
The argument includes the empty open, zero modules, and the level indexed by zero, and keeps
site and coefficient universes independent.

Validation: the final module compiled cleanly through `lcompile.py` in 18.6 seconds, below the
60-second limit. Source inspection confirms zero `sorry` tokens and lines at most 100 columns.
No consumer adaptations are needed because every public interface is unchanged.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.CanonicalOpenRestriction.finiteRestrictionMate_isIso`
(node `lem-sf-ordinary-open-finite-restriction-mate-invertible`).
No holes remain in the item. Zero holes were added or split off elsewhere.

## No longer needed

No original import was removed. Removed the planned proof dependency
`lem-sfb-localized-site-tensor-restriction`, whose module is
`Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`.
The proof uses Mathlib's slice/sheafification comparison directly and does not require this
tensor-restriction theorem or its module. This is a dependency removal for this item's route;
it does not claim that other parents of that node are unnecessary.

The tensor generator identity, coefficient projection square, an identification with a
separately constructed tensor comparison, and the underived scalar-adjunction unit formula
are also unnecessary for this invertibility proof. The scalar-adjunction module remains
needed for its specified scalar-extension object and morphism identifications.

## Where the brief, the DAG or earlier work was wrong

The original plan was unnecessarily strong for proving invertibility: it reconstructed a
normalized comparison and identified its transpose on generators. Subterminality and the
right triangle suffice once scalar extension is shown to preserve maps that are isomorphisms
on the slice. No mathematical statement was false or changed, and no further copy of the
obligation was split off.

The normalized localized adjunction is used as a general tool from
`lem-pur-site-restriction-module-adjunction-exact`; it is the same concrete adjunction used in
the operation definitions. The Mathlib searches logged in `searches.jsonl` found the mate
formulas and sheafification interfaces but no theorem directly proving this concrete mate
invertible.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
