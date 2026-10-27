## What changed

W7 proves the resolution-lift existence and homotopy uniqueness directly from the
K-injective Hom bijection, and writes the unit/naturality cancellation giving the normalized
derived coefficient equation. The same calculation constructs and proves the derived column
comparisons after exact element-site restriction. The statement of
`CategoryTheory.cech_coefficient_derived_comparison` is byte-identical to the library statement.

The unchanged 18 public constructions are extracted to
`Sheaf.CategoryTheory.CechCoefficientComparisonData`, which the original module publicly imports.
Their signatures and terms are byte-identical apart from blueprint links. This permits the
independent strict Čech construction to use the API without an import cycle. See
`coord/changes/cech-coefficient-comparison-data.md`.

The strict coefficient-map construction for arbitrary nonnegative complexes is stated in its
own module. It supplies precisely the underived component maps, augmentations and chain square,
homotopy invariance and refinements. It contains no right-derived comparison assertion.

## Proved and sorry left

The original module had one hole: `CategoryTheory.cech_coefficient_derived_comparison`.
Its written proof has zero `sorry`, combining the independent strict construction with proved
lift, uniqueness, exact-restriction and universal-property calculations. This is a decomposition,
not a net proof of the original hole.

One hole is added: `CategoryTheory.cech_coefficient_strict_maps`, node
`lem-sfb-cech-coefficient-strict-maps`. No definition has a hole. The extracted API has zero holes.
There are no axioms and no changes under `lean/WeilConjectures/`.

The first delivery preflight returned two missing LeanSearch records and the API structure
signature record. These metadata are corrected. Its axiom probe timed out at 60 seconds and
will run again during merge. No push occurred on that attempt.

The three delivery modules compile together with `lcompile.py --all`: the API in 32.1 seconds,
the strict statement in 7.6 seconds, and the derived proof in 59.0 seconds, with no warnings.
The temporary diagnostics are excluded from the packet. The unresolved strict construction
was attempted through the cochain and finite-total constructors; its remaining sectionwise
naturality and augmentation/refinement assembly are not submitted as partial proof bodies.
Holes closed: one upper declaration; holes added: one strictly separate lower declaration.
Thus the delivery's net hole reduction is zero.

## No longer needed

The public import `Sheaf.CategoryTheory.ExactSquareRightDerivedUnit` is removed. Neither the
theorem `CategoryTheory.Functor.exactSquare_rightDerived_unit` nor its proof dependency is used:
the main comparison is given with its unit equation, and the column comparison follows from the
K-injective right-derivability structure and the universal property of right derived functors.
The statement still mentions the canonical comparison described by that node; the statement
and statement dependencies stay unchanged.

The proof does not import `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses` or
use `prop-pur-kinjective-resolutions-exist`. The proved source-library
`SheafOfModules.isGrothendieckAbelian` and the existing Grothendieck K-injective instance suffice
for the actual small-site categories. Its obsolete top-level tool-use entry is removed.

The strict construction does not import the whole `DerivedCechImageTotalization` theorem or its
higher descent conclusions. No existing module is withdrawn or pruned from its other consumers.
The original public Mathlib and column-model imports remain available through the API module.

## Where the brief, the DAG or earlier work was wrong

The proof plan's exact-square theorem is stronger than the calculation needed when gamma and
its unit equation are already supplied. It is unnecessary as a proof dependency. For the slice
exactness step, a default structure field does not identify an arbitrary witness's pullback
with the actual elementModulePullback. The proof instead uses the existing adjunction of
`elementModuleExtension` with that actual functor, and the coherent model's other adjunction.

The resumed attempt's reference clock was reset externally: the recorded start changed from
1792750111.2554584 to 1792773673.936662 after the launcher's compile-queue pause. W7 did not edit
`.budget` or launcher tools and continues the same proof work. No delivery has been attempted
on the basis of elapsed time.

## New nodes

`def-sfb-cech-coefficient-comparison-data` attaches the unchanged public API moved to its own
module. It separates statements and definitions from the two independent proof modules.
The corresponding change record is `coord/changes/cech-coefficient-comparison-data.md`.

`lem-sfb-cech-coefficient-strict-maps` records the genuinely separate underived construction
from original proof steps 3, 5 (chain square), 6 and 7. Its statement applies to arbitrary
nonnegative complexes, not only injective resolutions. Its docstring gives the complete
section-restriction, finite-total, signed-homotopy and refinement argument. Edge checks:
identity scalars recover the usual functorial Čech maps; zero complexes give zero maps;
resolution degree zero has zero homotopy component into degree minus one; no cover epi or
injectivity hypothesis is used in this strict construction.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
