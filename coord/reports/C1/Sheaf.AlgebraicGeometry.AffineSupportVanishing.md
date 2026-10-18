## What changed

Proved `AlgebraicGeometry.affine_support_vanishing` with its signature and every public
import unchanged. Added two proved private helpers: `isTorsion_of_mono` and
`subsingleton_H_supportedIn_torsion`. The first inherits local annihilators along a
sectionwise injection; the second applies the affine dimension bound and finite-pushforward
comparison to each canonical support kernel. The main proof constructs the directed family,
uses the source local-section support theorem and directed-union cohomology surjectivity,
and transports Ext cohomology to the stated derived-section cohomology.

Reused the proved private restriction/factor helpers of
`Sheaf.AlgebraicGeometry.Sites.SupportedTorsionCohomologyBound`, and the scalar-map and
finite-union dimension helpers of `WeilConjectures.AlgebraicGeometry.Sites.SupportDimension`
via private `import all`. No imported file is changed. Updated the item's proof plan and
proof dependencies to reflect this implementation. The unit has no realized statement or
step here to bypass; the original closed-support/affine-bound/filtered-union route is retained.

Validation: the complete module compiled through `lcompile.py` in 8.3 seconds without
errors or warnings. The statement handles the empty scheme, zero sheaf, c=0, nonreduced
schemes, and torsion without a global exponent. No data definition or existing interface
changed. The delivery tool additionally performs its compile and axiom checks.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.affine_support_vanishing`
(node `lem-kun-affine-support-vanishing`). Added 0 holes; split off 0 obligations.
There are no remaining `sorry`s in any delivered Lean file. This is a proof from the
existing library declarations, rather than a decomposition into new assumptions.

## No longer needed

Removed direct private imports:

- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`
- `Mathlib.CategoryTheory.Sites.Abelian`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Sheaf.AlgebraicGeometry.SupportDimensionUnion`
- `Sheaf.AlgebraicGeometry.TorsionSheafCharacterizations`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`
- `WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine`
- `Sheaf.AlgebraicGeometry.Sites.SeparablyClosedPointCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension`

Removed direct proof dependencies:

- `lem-sc-support-dimension-union`
- `def-weil-pbc-inverse-image`
- `def-weil-pbc-direct-image`
- `lem-weil-pbc-etale-site-localization-open`
- `lem-weil-pbc-lft-affine-pairs`
- `lem-kun-cd-sep-closed-point`
- `def-kun-cd`
- `def-sc-etale-torsion-cd`

The source `exists_covering_supportedIn` supplies the local-section form of the support
union, so the separately stated `support_dimension_union` colimit theorem is unnecessary.
The source field cohomological bound supplies the needed vanishing directly, so the
separate numerical dimension-equality theorem and numerical dimension definition are
unnecessary. Affine-closed-complement finite-type instances replace the affine-pairs
criterion. The source closed-support equivalence uses open restriction directly, so no
explicit etale-site localization equivalence is needed. The generic support-kernel helpers
and affine bound supply the other removed direct imports transitively where needed; these
are import pruning, not claims that every corresponding concept disappears from the closure.

Removed obsolete top-level tool-use approvals for
`lem-sc-support-dimension-union`, `lem-kun-cd-sep-closed-point`,
`lem-weil-pbc-etale-site-localization-open`, and `lem-weil-pbc-lft-affine-pairs`.
No modules are withdrawn. No whole-closure pruning count is asserted.

## Where the brief, the DAG or earlier work was wrong

The original support-union and cohomological-dimension declarations are usable, but the
source library already has a shorter local-section support API, explicit-dimension affine
bound, field bound, and directed-union cohomology API. These avoid constructing an explicit
colimit diagram or converting a numerical cohomological dimension. The bounded-support
cohomology theorem requires a global exponent, so it cannot be applied to this arbitrary
torsion sheaf; only its proved generic restriction/factor helpers are reused. Torsion is
instead inherited through subobjects and inverse image, following the Stacks 0F0W proof.
Read `literature/stacks-project/etale-cohomology.tex`, `lemma-interlude-II`, lines 19916ff.
No statement repair, new node, or definition repair was needed.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
