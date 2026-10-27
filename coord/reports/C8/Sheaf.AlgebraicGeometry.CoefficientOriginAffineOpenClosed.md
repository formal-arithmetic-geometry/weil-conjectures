## What changed

Replaced the hole in `Sheaf.AlgebraicGeometry.CoefficientOriginAffineOpenClosed` by
an argument from the canonical kernel sequence of the closed localization unit.
The original public theorem and its hypotheses are unchanged.

The extension-closure argument is implemented in Lean: use exact intrinsic comparison,
its invertible bounded-below derived unit from the existing injective-acyclicity
statement, lift the connecting morphism, compare distinguished triangles, and take
zeroth homology. Transfer this argument through the existing constant-scalar
equivalences. Only proof imports were added to the item.

Added `Sheaf.AlgebraicGeometry.CoefficientOriginClosedDirectImage` with a proved
closed-direct-image lemma. Pullback of an affine etale presentation along a closed
immersion remains affine and etale and preserves its limit. Its section cocone is the
section cocone of direct image. Existing coefficient comparison continuity and the
classical-module origin criterion then give the antecedent. This avoids introducing
a new closed direct-image comparison hole.

Added `Sheaf.AlgebraicGeometry.CoefficientOriginLocalizationKernel` for the remaining
geometric step: the closed localization unit is epic, and its kernel has etale origin
if the open restriction does. This lemma has no hypothesis on the closed restriction
and proves no middle-sheaf gluing assertion. Its object is the actual categorical
kernel of the specified adjunction unit; no object is chosen from a holed existence
statement. Its docstring and node give the complete scalar-linear localization proof.

The missing `CoefficientComparisonFixedPullback` dependency has been removed.
Use the public `coefficientModelFixedScalars_isEquivalence` from
`Sheaf.Paper.FiniteComparisonModelRealization`. New proved private helpers give
the constant-section unit equation, the direct-image square and its adjunction
mate, all in the full coefficient universe. A generic private helper constructs
the canonical fixed-module adjunction. The kernel lemma accepts an adjunction
between the fixed functors; different such units differ by an invertible target
map and have canonically isomorphic kernels. The item imports these helpers from
the new closed-direct-image module. No missing source has been recreated or
withdrawn, and no extra hole has been introduced for this transport.

Validation: all three modules compiled cleanly together through `lcompile.py --all`: the
closed-direct-image module in 19.2 seconds, localization-kernel module in 7.7 seconds,
and main module in 14.6 seconds. The original theorem signature is unchanged. The
DAG dependency lists agree with their proof steps. Delivery checks recompile the
final packet after removing an unused import from the kernel module.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.ProEtale.coefficientFixed_essImage_affine_openClosed`
(node `lem-pe-coefficient-origin-affine-open-closed`).

Added and proved:
`AlgebraicGeometry.ProEtale.coefficientFixed_closed_directImage_essImage`
(node `lem-pe-coefficient-origin-closed-direct-image`).

The item now has zero direct holes. The one new hole is
`AlgebraicGeometry.ProEtale.coefficientFixed_localization_kernel_origin`
(node `lem-pe-coefficient-origin-localization-kernel`).
This is a decomposition: one hole closed and one strictly smaller hole added,
not a claim of net hole reduction. All private helpers are proved.

## No longer needed

No original public import was removed and no module is withdrawn. The retained
proof import `Sheaf.AlgebraicGeometry.CoefficientComparisonFixedPullback` was
removed from both files: its scalar-transport role is now supplied by the public
scalar equivalence and the proved private adjunction square. Its node is no longer
a direct dependency of this argument. The trial proof import
`Mathlib.CategoryTheory.Abelian.ShortExact` was removed because the argument uses
`ShortComplex.ShortExact.map_of_exact`, already available from the exact-functor API.
The kernel module no longer imports `Mathlib.Algebra.Category.ModuleCat.AB`: its
signature uses an explicit kernel-existence instance and the declarations from its
original coefficient-site import.

The item no longer directly uses the original-universe declarations attached to
`prop-weil-pbc-comparison-direct-image` or `thm-weil-pbc-site-comparison`.
Closed direct image is handled by the coefficient continuity and classical-origin
criteria, and extension closure by coefficient exactness and injective acyclicity.
These nodes and their modules may still have other consumers; no global pruning
of them is claimed.

`lem-sf-proetale-open-closed-sequence` and
`lem-cbc-proetale-extension-zero-comparison` remain the geometric dependencies of
the new localization-kernel node. They are not pruned: their scalar-linear arguments
are exactly what remains to transport to the coefficient-sized model.

## Where the brief, the DAG or earlier work was wrong

The earlier packet imported private helpers from a source module that no longer
exists in the current shared tree. The initial delivery check reproduced that
failure. This revision uses the available public scalar equivalence and proves
the needed comparison square, preserving the missing node and its attachment.

The listed original geometric declarations have scheme universe u and module
universe u+1, whereas this item's module values live in max v (u+1). They cannot
simply be instantiated at these coefficients. This does not dispute their statements;
it explains the need for a coefficient-sized endpoint lemma.

The finite-ring derived-unit declaration attached to
`thm-weil-pbc-site-comparison` also does not supply this item's arbitrary ring
coefficient statement. The existing coefficient injective-acyclicity statement does,
via the proved derived-adjunction theorem; the extension proof uses it directly.

Edge cases checked mathematically: empty open (zero kernel), empty closed (unit to
zero with kernel F), zero coefficient ring, and closed immersions with full image
that are not scheme isomorphisms. The formulas use the same adjunction and kernel
in all cases and do not infer that a full-image closed immersion is an isomorphism.
The blueprint unit's open-closed localization and derived extension route is retained.

## New nodes

`lem-pe-coefficient-origin-closed-direct-image` records the proved closed endpoint,
with the continuity argument and the actual fixed-module direct image in its signature.

`lem-pe-coefficient-origin-localization-kernel` records the remaining open endpoint
and surjectivity of the closed localization unit, using Tags 09AH and 09AF. It is
strictly part of the old argument: no closed-restriction origin hypothesis, no origin
conclusion for F, and no shifted copy of the original gluing theorem.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
