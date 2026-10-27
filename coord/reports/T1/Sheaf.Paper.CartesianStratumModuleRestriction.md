## What changed

Proved the complete Cartesian stratum module restriction theorem in its original module.
Constructed the module compositor as the mate of the canonical direct-image comparison,
proved its underlying normalization by transposing through the adjunctions, and composed
along pullback.condition. Naturality, both coefficient equations, local constancy and
finite geometric module stalks are proved. The theorem signature is unchanged verbatim.

The sheaf square is now packaged by a proved unique factorization; the public equation
proEtaleCartesianStratumSheafComparison_eq proves equality with its original definition.
Equality transport likewise has a proved unique value and constant-section normalization.
This avoids repeated kernel unfolding of the large explicit comparison. Two helper
signatures use definitionally equal functor-object notation. No core module was changed.
See coord/changes/cartesian-stratum-comparison-api.md for exact definitions and user checks.
The six public imports remain; added proof-only imports of the module compositor and
ring-sheaf-change adjunction (import all to use their proved private infrastructure).

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Scheme.proEtale_cartesianStratum_moduleRestriction
(node lem-sf-cartesian-stratum-module-restriction).
Zero holes added, zero split off, zero sorry left in the delivery. All support theorems
and data definitions are complete. The normalized-comparison split from the earlier
attempt was never delivered and has been removed from this packet.

The cleaned module compiles with no warnings at the project default limits. The final
delivery runs the independent compiler/preflight and axiom audit. No axiom, hollow data,
or kernel-checking workaround is introduced.

## No longer needed

Removed direct proof imports Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap,
Sheaf.CategoryTheory.SiteInverseImageTensor and
Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses. No module is withdrawn.
The proof no longer directly uses prop-weil-pbc-proetale-constant-ring-map,
lem-weil-pbc-left-exact-site-inverse-image-tensor or def-pur-sheaf-tensor-product:
it uses the already proved normalized adjunction/compositor APIs instead of reconstructing
scalar cancellation or tensor additivity. The corresponding first and third top-level
tool-use approvals are removed. Their transitive dependencies remain in the library.

## Where the brief, the DAG or earlier work was wrong

No statement dispute and no unit-route change. The previous packet left normalized
composition as a new hole; this session proved that argument and eliminated the split.
The original explicit equality transport was expensive when repeatedly projected in the
large conclusion. Packaging the uniquely specified comparison with proved equations
resolves that cost without changing its mathematical value. The two local-constancy
interfaces differ only by a True predicate on models. The construction works for arbitrary
s, but the original immersion hypothesis remains unchanged. Empty sources and the zero
ring require no extra assumptions. No adopted source-library declaration was changed.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
