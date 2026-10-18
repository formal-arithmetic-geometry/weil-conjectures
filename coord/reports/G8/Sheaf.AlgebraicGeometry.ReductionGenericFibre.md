## What changed

Proved `AlgebraicGeometry.Scheme.Hom.reduction_generic_fibre` in
`Sheaf.AlgebraicGeometry.ReductionGenericFibre` without changing its signature or public imports.
Added four private, fully proved helpers: `reduced_fiber_ring`, `reduced_fiber_spec`,
`reduced_fiber_affine_base`, and `reduced_fiber_generic`.

The affine argument uses `Ideal.Fiber.algEquivQuotient`. At a minimal prime the maximal ideal
of the base localization consists of nilpotents; its image in the reduced localization of
the source is zero. Consequently the fibre ring is reduced. Affine source covers and an
affine neighbourhood of the base generic point extend the argument to arbitrary schemes.
The canonical fibre map of the reduction is a surjective closed immersion from a reduced
scheme. Factoring it through the target reduction gives a surjective closed immersion
into a reduced scheme, hence an isomorphism. Pullback identities prove both projection equations.

Added the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` for reducedness of the
nilradical subscheme and its universal factorization. Updated the existing DAG proof and
proof dependencies to this route, following Stacks 054Z. No statement, definition, visibility,
or consumer changed. The unit `sk-prop-sf-cbc` has no realized steps for this item to bypass.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Scheme.Hom.reduction_generic_fibre`
(node `lem-pur-reduction-generic-fibre`). No holes remain; no holes were added or split off.
All four private helpers are proved. The module compiles through `lcompile.py`.
`#print axioms AlgebraicGeometry.Scheme.Hom.reduction_generic_fibre` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The calculation allows zero localizations and empty fibres, arbitrary nilpotence exponents,
a nonreduced or reducible base, and no finite type, flatness, or noetherian hypotheses.

## No longer needed

Removed the direct imports `Mathlib.AlgebraicGeometry.Pullbacks`,
`Mathlib.RingTheory.Localization.BaseChange`, and
`Mathlib.RingTheory.LocalRing.ResidueField.Fiber`. The fibre and pullback APIs remain
available through `Mathlib.AlgebraicGeometry.Fiber`; the direct base-change localization
import is unnecessary because `Ideal.Fiber.algEquivQuotient` already supplies the ring formula.

Removed `lem-weil-pbc-localization-base-change` from this node's proof dependencies.
Its direct tensor-localization calculation is unnecessary for this proof.
The original steps computing the full kernel of reduction after localization and gluing
quotient identifications are replaced by the reduced-source calculation and the universal
property of reduction. All other original declared dependencies remain used. No separate
Sheaf or WeilConjectures module becomes globally unreachable just from this delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. The original five-step kernel calculation is valid
but longer than needed with the existing closed-immersion and reduction APIs. The proof
uses its stated minimal-prime and fibre-ring declarations and proves reducedness first,
then obtains the comparison through the universal property. No new nodes are needed.

Searches actually run: LeanFinder for reduction commuting with fibres at component generic
points (eight nearby facts, no match); Loogle for `"nilradical", "pullback"` (zero hits);
launcher grep for `reduction.*fiber|fiber.*reduction|nilradical.*pullback` (zero hits).
Local searches found and inspected the existing integral-base affine reduced-fibre proof
in `GenericFibreDominantField`; the present proof handles the more general hypotheses
using the minimal-prime localization calculation instead.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
