## What changed

Completed the unchanged theorem
`AlgebraicGeometry.ProEtale.sp_completed_coefficient_regular_quotients` in
`Sheaf.Paper.CompletedCoefficientRegularQuotients`. All six public declaration
signatures and both public imports remain unchanged. All new helpers are private
and proved. No other Lean module is changed.

The proof uses the existing DVR arithmetic, completed scalar regularity,
projection divisibility, and normalized finite-quotient map uniqueness. A
set-theoretic section of each coefficient quotient, transported by constant
set sheafification, proves sectionwise surjectivity. This allows the ordinary
ring first isomorphism theorem followed by sheafification to construct the
normalized quotient isomorphisms. Transport of the finite reduction maps gives
all requested transitions and commutative squares. The existing node's proof,
proof dependencies and origin now describe this argument.

Private proof imports added: `Sheaf.Paper.CompletedIntegralFiniteQuotientHomExt`,
`Mathlib.Algebra.Category.Ring.FilteredColimits`,
`Mathlib.Algebra.Category.Ring.Colimits`, and
`Mathlib.CategoryTheory.Sites.LeftExact`. The small-model instance is local to
the surjectivity proof, with independent site and coefficient universes.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.sp_completed_coefficient_regular_quotients`
(node `lem-sp-completed-coefficient-regular-quotients`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered Lean file.
The final single-file lcompile.py check compiled cleanly in 25.4 seconds, with no warnings.
A text comparison also verified unchanged public definitions and theorem signature,
and import_direction.py accepted the added proof dependency.

## No longer needed

Removed proof imports
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal` and
`Mathlib.Topology.Algebra.Valued.LocallyCompact`.

The direct proof no longer needs these planned dependencies, and removes their
obsolete top-level tool approvals in the delivered node:

- `lem-weil-pbc-site-sheafification-sections-local`: replaced local representatives
  and gluing with sectionwise surjectivity of constant quotient maps and
  sheafification of the presheaf first isomorphism theorem.
- `lem-weil-valued-dvr-finite-quotients`: the specialized, already proved
  `Padic.finite_coefficientExtensionRing` supplies finite coefficient quotients.
- `det-prop-sfb-qlbar-colimit-x-integral-limit`: no additional comparison with
  pulled-back condensed coefficients is needed; the actual completed ring and
  normalized ell-tower comparison are already defined in the imported interface.
  Its module `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit` remains
  a public dependency of `SmoothPurityCoefficientTowers`; no global pruning of
  that module is claimed.

No module is withdrawn. All other planned dependencies remain used. The added
node dependency `lem-sp-completed-integral-finite-quotient-hom-ext` identifies
normalized projections; it is an existing, proved coefficient-ring tool in the
same unit, and introduces no new result or unit-route change.

## Where the brief, the DAG or earlier work was wrong

No statement correction was necessary. The DAG's local-lift argument is valid,
but there is a stronger available observation: constant quotient maps are
surjective on sections, because their underlying set maps split before constant
sheafification. The proof uses that shorter argument. At ell level n the matching
uniformizer index is `e * (n + 1) - 1`; positivity is proved before cancelling
this subtraction. The case n=0, ramified extensions, arbitrary characteristic of
T, and the empty scheme need no extra hypotheses. The unit's reconstruction
route is preserved.

Searches run with msearch.py: LeanFinder for inverse limits of constant DVR
quotient sheaves (only ordinary adic completion/quotient results); Loogle for
Ideal.Quotient equivalences (first-isomorphism and equality-of-ideal APIs); grep
for quotientKerEquivOfSurjective, isIso_iff_bijective and
sheafificationAdjunction. Read the actual signatures in the pinned Mathlib and
all stated proof dependencies. No existing theorem states this full package.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
