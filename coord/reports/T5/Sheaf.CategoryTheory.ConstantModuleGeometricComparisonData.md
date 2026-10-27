## What changed

Proved `CategoryTheory.constant_scalar_geometric_adjunctions_ofUniverses` in
`Sheaf.CategoryTheory.ConstantModuleGeometricComparisonData`, retaining its full
signature, definitions and public imports. The five private scalar helpers adapt
the existing small-site scalar argument to independent object and morphism
universes and the landed `RingedToposMorphismOfUniverses` interface. The proof
constructs the linear direct-image comparison and uses the constant-ring
restriction equivalences to obtain the required adjunction comparisons.

Repair of return `765d418bde3`: removed the copied private `adjunctionSquare`
proof. Exported the existing theorem in the unclaimed module
`Sheaf.CategoryTheory.ConstantScalarGeometricAdjunctions`, with its statement
and proof unchanged and a source docstring. The item already publicly imports
that module; both calls now reuse its theorem. Attached the exported helper to
that module's existing node. The item's node records this reuse and its proof
dependencies. Change record: `coord/changes/T5-adjunction-square-export.md`.

The source is Stacks `sites.tex`,
`proposition-functoriality-algebraic-structures-topoi`, case (6), and the
adjunction discussion in `categories.tex`; the existing mate argument uses
Mathlib `Adjunction/Mates.lean`. No unit step is bypassed. The general
constant-ring module equivalence is used as a categorical tool, as in the
existing small-site proof.

## Proved and sorry left

Closed the original one hole:
`CategoryTheory.constant_scalar_geometric_adjunctions_ofUniverses`
(node `def-sfb-constant-module-geometric-comparison-data`).
Zero holes remain in the item, zero holes are added, and zero statements are
split off. `CategoryTheory.adjunctionSquare` remains proved by its existing
complete proof. All five new private helpers are proved.

The exact two-file packet compiled cleanly through `lcompile.py --all`: 12.2 s
for `ConstantScalarGeometricAdjunctions`, 36.7 s for the item. Delivery preflight
checks the complete packet as well.
The categorical argument retains the zero ring, empty site, identity morphism
and localized-site cases, and independent site object and morphism universes.

## No longer needed

Removed unused private proof imports from the original item:
`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`,
`Mathlib.CategoryTheory.Sites.CoverLifting`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`, and
`Mathlib.CategoryTheory.Adjunction.Mates`.
Added only the private proof import
`Mathlib.CategoryTheory.Sites.CartesianMonoidal`.

The copied private `adjunctionSquare` and its entire proof are removed; both
uses resolve to the exported existing helper. No public import is removed, no
module is withdrawn and no declared dependency is pruned. The small-site
comparison theorem itself is not applied, since its site universe restriction
does not fit this declaration; its generic adjunction-square helper does fit.

## Where the brief, the DAG or earlier work was wrong

The returned packet unnecessarily copied `adjunctionSquare`, whose original
statement already has fully independent category universes. It is now reused
from its original module after the documented visibility repair.

The original definition node had no proof despite also owning this existential
helper theorem. Its proof now records the scalar comparison and the two
applications of the existing adjunction-square theorem. No mathematical
statement or definition correction and no new node is necessary.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
