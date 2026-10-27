## What changed

Implemented the proof of
`AlgebraicGeometry.AlgebraicSpace.existsUnique_section_and_eq_of_fpqc_cover`
without changing its statement. Its equality assertion is proved by representing the
equalizer using the diagonal, descending maps into that scheme, and descending the
identity equation. Its existence assertion is reduced to an étale local extension on
a singleton affine fpqc cover. The item proves the overlap equality after fpqc base
change, glues by the defining fppf sheaf condition, and verifies restriction to the
original affine cover. The final conversion from scheme pullback compatibility to
relative-site compatibility is explicit.

Added `Sheaf.AlgebraicGeometry.FpqcRelativeCriterion`, with a complete proof of the
relative affine criterion. It constructs the absolute presheaf of pairs consisting
of a structure map and a section, proves the relative/absolute gluing implications,
and applies Mathlib's absolute criterion. All definitions have explicit data and
proved functor laws; no witnesses are chosen from an unproved existence theorem.

Added `Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcLocalExtension` for the remaining
chart construction, precisely steps 3--5 of the original plan. This produces an
étale local solution, with its base-change equality, before any global sheaf gluing.
The statement is strictly a part of the original argument: it only concerns affine
singletons and concludes with a section on an auxiliary étale cover, without a
section on the original base or a uniqueness conclusion.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.AlgebraicSpace.existsUnique_section_and_eq_of_fpqc_cover`
(node `lem-a1-algebraic-space-fpqc-sheaf`) by a compiling decomposition.

Added one hole:
`AlgebraicGeometry.AlgebraicSpace.exists_etale_local_extension_of_affine_fpqc`
(node `lem-a1-algebraic-space-fpqc-etale-local-extension`). Its entire proof is
`by sorry`, in its own module, with the complete source argument in the docstring
and node. No other delivered declaration contains a hole.

Proved `AlgebraicGeometry.isSheaf_fpqc_over_of_affine`
(node `lem-a1-relative-fpqc-affine-criterion`) and every private helper. Thus the
item has zero holes left; the delivery closes one original hole and adds one
strictly smaller hole, net zero. This is a decomposition, not an unconditional
proof of the item.

Server compilation passed for all three modules (approximately 3.5 seconds for
the local extension statement, 3.8 seconds for the relative criterion, and 6.5 seconds
for the item). The delivery tool also performs its compilation and axiom checks.

The arguments permit empty families: the total-presheaf reduction uses the sheaf
condition and representable uniqueness without choosing a covering index. Identity
and repeated covering arrows are also permitted. No separatedness or finiteness
condition on the algebraic space has been added.

## No longer needed

Removed the item's direct proof imports of
`WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`,
`WeilConjectures.AlgebraicGeometry.FpqcDescentEtale`,
`Sheaf.AlgebraicGeometry.SeparatedLqfFpqcDescent`, and
`Sheaf.SecPurity.QcMapAffineEtaleNeighbourhood`.
These belong to the split chart construction and are imported by its new module;
they remain needed. No node or module is claimed pruned from the targets' closure.
The item's public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The existing absolute affine criterion did require
the relative-site argument already described in the node: this is now proved,
including the gluing of the base structure map. The original numbered chart steps
remain the proof plan of the single residual theorem. The unit and chapter routes
are unchanged. No existing shared definition, signature, instance, attribute, or
public import is changed; no consumer adaptations or change records are needed.

Searches used LeanFinder for algebraic-space fpqc descent, Loogle for relative
sheaf conditions and the absolute affine criterion, LeanSearch for the relative
criterion and the étale local extension, and source searches in Mathlib and both
library roots. Mathlib supplies the absolute criterion and subcanonical fpqc
representable descent; it does not supply the relative criterion or the chart
extension. Checked the nearby representable étale fppf local-lifting node: it
lifts a section already on the base, so it does not descend the invariant section
on an fpqc cover and is not a replacement for the residual statement.

## New nodes

`lem-a1-relative-fpqc-affine-criterion`, in
`dag/nodes/sec-purity-real-sheaves/lem-a1-relative-fpqc-affine-criterion.json`,
is attached to the completely proved relative affine criterion. It expands the
relative-site reduction in the first paragraph of Stacks Tag 0APL using Tag 022H.

`lem-a1-algebraic-space-fpqc-etale-local-extension`, in
`dag/nodes/sec-purity-real-sheaves/lem-a1-algebraic-space-fpqc-etale-local-extension.json`,
is attached to the one remaining theorem. It records the chart selection, its
transport datum, effective scheme descent, and the invariant map to the affine
chart from Stacks Tag 0APL, stopping before the fppf gluing implemented in the item.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
