## What changed

Proved `SheafOfModules.derivedScalarExtension_counitShift` in
`Sheaf.Algebra.Homology.DerivedScalarExtensionCounitShift`, preserving its signature.
The proof constructs the coherent shift from the supplied universal counit, proves
uniqueness by the universal property after postcomposition with the shift equivalence,
and proves exactness with this same shift using the K-flat resolving class,
essential constancy, the source-triangle theorem and localization of triangles.
The ordinary functor in the independent-universe cochain model is identified with E
by its prescribed object and map equalities. Only its stated quasi-isomorphism
preservation clause is used; no data is defined by choosing an unproved witness.
Retained the proof-only import `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
from the current shared module.
Updated the node proof and dependencies to describe the actual argument.
The public-import removals are recorded in
`coord/changes/derived-scalar-extension-counit-shift-imports.md`.
The refreshed downstream scan finds two direct private importers and 357 downstream
modules. No module uses this theorem yet; neither direct importer needs an
adaptation after the import pruning. The change record lists all downstream
modules and their current holders.

Validation: the current dry run compiled the item and passed preflight (2026-10-19). A separate
lcompile.py --all check compiled the retained item and both unchanged direct
importers together successfully (0.0, 0.0 and 1.4 seconds), confirming that the
public-import pruning needs no consumer edits.
Its theorem signature is textually unchanged; the delivered Lean contains no sorry
or forbidden declarations and every line is at most 100 characters.

Resume validation (2026-10-19): the retained Lean proof compiled again through
`deliver3.py --no-push`, but its preflight subprocess timed out after 900 seconds.
The required retry is waiting for shared worktree capacity. Both direct importers
remain byte-for-byte identical to the previously compiled consumer copies. The
357-module consumer table records the earlier snapshot; the shared library has
continued to grow, and a new full `tools/downstream.py` scan is still pending.

## Proved and sorry left

Closed 1 of 1 original holes:
`SheafOfModules.derivedScalarExtension_counitShift`
(node `lem-sbc-derived-scalar-extension-counit-shift`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered module.
This proves the item from existing declared dependencies, including the existing
`SheafOfModules.nonempty_derivedChangeOfRingsCochainModel` theorem; it does not
claim that all transitive dependencies are sorry-free.

## No longer needed

Removed these imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`: none of its
  auxiliary tensor-functor declarations is needed. E is already additive by hypothesis.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the general-site ringed module and
  topology interfaces already supply the notions used in the unchanged signature.
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`: the supplied
  IsLeftDerivedFunctor instance already gives the Kan universal property. Essential
  constancy is obtained directly from the resolving class; there is no need to
  construct a second universal pair or use an unspecified exact shift structure.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: its tensor
  constructions are not used directly; the cochain model supplies K-flat invariance.
- `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated`: redundant with the public
  derived-category imports, which supply the same canonical triangulation instances.

The direct proof dependency `def-pur-sheaf-tensor-product` and its top-level
tool-use entry were also removed:
the prescribed ordinary functor and its additive instance already provide the
termwise construction, and its K-flat invariance comes from the change-of-rings
model. It remains a statement dependency identifying the scalar extension.
The direct proof dependency `lem-pur-left-derived-from-kflat-class` and its
corresponding tool-use entry were removed. It remains a statement dependency
explaining the meaning of the supplied left-derived pair. No claim is made that
these modules are unused by the rest of the library. No blueprint unit is bypassed;
`sk-rem-rest` has no realized statement or proof steps.

## Where the brief, the DAG or earlier work was wrong

The original item publicly imported the older change-of-rings theorem, whose source
and target localization universes coincide. The current node attachment is
`DerivedChangeOfRingsCochainModel`; its preservation clause works with the separate
wR and wS of this item, so the proof imports that current interface explicitly.
The resolving-class existence theorem need not be reapplied to supply a universal
pair, since the unchanged statement already assumes the given pair is universal.
No mathematical statement, definition, target, or consumer signature was changed.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
