## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.proEtale_openSquareExchange`.
The exchange is constructed as the inverse of the specified derived open-adjunction
mate. Private transport calculations identify its ordinary mate with the canonical
fixed-coefficient pro-etale base-change map. Fully faithful open extension supplies
the invertible units. Mate calculus proves both ordinary identity laws and both
pasting laws, and exact localization carries these equations and the unit equation
to the unbounded intrinsic derived categories. The construction works for every
finite commutative coefficient ring and is specialized to the published finite
quotient in the original theorem.

All original public declarations, signatures, definitions and public imports are
preserved. The transport, mate and localization calculations are proved for abstract
categories before specializing them, to avoid repeated expansion of the intrinsic
realization functors during checking. Only private proof imports and proved private helpers are added. There are no
source-library edits or forced consumer adaptations.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.proEtale_openSquareExchange` (one original hole).
Added: none. Remaining in the item: zero. No split-off statements or modules.

Validation: the final complete module compiled cleanly on the project server in
37.7 seconds, with zero holes and no warnings. Its original public declarations,
definition bodies and public imports were compared verbatim with the shared source.
The private API separates the canonical derived mate isomorphism from its raw
localization presentation and performs the unit-map and canonical-map conversions
in abstract categories. Local reducibility annotations keep the ordinary functors
abstract during concrete coherence checking, while explicitly unfolding the two
adjunction-normalized open comparisons where needed. Delivery preflight checks
the module, its consumers, the node update and proof dependencies.

## No longer needed

Removed the original private proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionByZeroAdjunction`

The proof uses the existing fixed-coefficient base-change theorem rather than
reconstructing direct-image restriction on sections. Its exactness and adjunction
inputs already come from the unchanged public intrinsic operations imports.
Consequently the direct section computation, a new Hom-bijection uniqueness
argument, and the direct-image localization calculation in the old node plan
are not repeated here. This does not withdraw any upstream declaration or claim
that its own dependencies have become globally unnecessary.

The following old direct proof dependencies are replaced by existing library tools:

- `prop-weil-pbc-proetale-constant-exact`: exactness comes from the published intrinsic
  pullback instances, already imported by the unchanged public interface.
- `lem-weil-proetale-weakly-etale-localization`, `def-weil-proetale-inverse-image`,
  and `def-pc-fibre-product`: the proof reuses fixed-coefficient base change and
  pullback coherence, so it does not redo their section and fiber-product arguments.
- `lem-weil-extension-by-zero-adjunction`: the specified intrinsic adjunction is
  already constructed in the item from the existing fixed-coefficient adjunction.
- `lem-exc-proetale-open-unit`: the stronger existing fully faithful extension tool
  directly supplies invertibility of the transported units.
- `lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection`: mate-equivalence injectivity
  proves coherence directly, without introducing another natural Hom bijection.

Removed the obsolete top-level tool approvals for
`prop-weil-pbc-proetale-constant-exact`,
`lem-weil-proetale-weakly-etale-localization`,
`lem-weil-extension-by-zero-adjunction`, and `lem-exc-proetale-open-unit`.
The approval for `lem-weil-extension-by-zero-exact` is retained in its original order.
The Mathlib conjugation and unit-uniqueness nodes are retained because the proof
uses their API directly. Two redundant draft imports,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`
and `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`, were also removed;
their declarations are already public dependencies of the retained proof imports.

These are removals from this node's direct proof route. No complete module is
withdrawn, and no global pruning count is claimed for dependencies still needed
by the preserved upstream base-change theorem or other consumers.

## Where the brief, the DAG or earlier work was wrong

The old plan described a longer reconstruction of open-square base change.
The library already provides the canonical fixed-coefficient base-change map,
its invertibility, and its identification with the inverse mate of the pullback
square. Transporting that specified map supplies the shorter route without
changing the canonical comparison. Identity and pasting still require proofs
for the exact compositors and units in the item; the private mate and localization
calculations supply them. No false statement or definition repair was needed.
The `sk-d-weil-push` realized record has no numbered steps, and the auxiliary
open-closed-triangle unit has no nonempty realized step assignment at this node.
The canonical open-square tool is preserved. The route reuses the existing
sectionwise adjunction base-change theorem, then derives the same exact comparison;
it introduces no boundedness or stalk-detection assumption.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
