## What changed

Proved `CategoryTheory.koszulFibreLinearDescent` by constructing the specified signed
product fibre, diagonal maps, unit and projection. The construction preserves chain
homotopies, quasi-isomorphisms, addition and the given coefficient action. Its localization
has the required derived-tensor tower, actual-projection Roos triangle and additive full
subcategory of objects with invertible unit. Existing public signatures and definitions
are unchanged. The public coefficient import now names its defining module
`ScalarLocalizationCoefficientActions` directly, following F2's relocation, instead of
loading `ScalarLocalizationDerivedHom` and its unrelated telescope proof. No adopted source-library module is modified.

Validation: the complete three-module sandbox compiles with zero errors and warnings.
The final main module took 49.4 seconds, within the 60-second limit. The resumed run's
initial timeout was repaired after profiling repeated instance/type elaboration:
private canonical instances are cached, the derived-category section variable is
scoped to the specification, quasi-isomorphism helpers and final theorem, and private
sheaf universes are explicit. The cached instances are disabled before the public
theorem signature. No proof or file was split to meet the limit.
Existing public definitions, statements and docstrings were compared with the current
source and remain unchanged. All three modules contain zero holes and obey the
100-character line limit. The fresh downstream check finds zero consumers of this item.
The delivery command performs the final compile, probes and preflight.

Two proved comparison lemmas isolate the transition-natural tensor-tower comparison and
the signed-coordinate derived-limit triangle. Both have their own modules and DAG nodes.

## Proved and sorry left

Closed the original hole in `CategoryTheory.koszulFibreLinearDescent` (one of one).
Added zero holes. No `sorry` remains in any delivered module.

Also proved `CategoryTheory.koszulTensorDerivedTower` and
`CochainComplex.derivedLimitTriangle_of_roos_coordinates`, with no split-off unfinished
statements. Existing imported theorem holes remain the dependencies supplied by this stage.

## No longer needed

The route does not need `lem-pur-additive-localization-descent` or its absent module
`Sheaf.CategoryTheory.AdditiveLocalizationDescent`: Mathlib's full homotopy quotient and
`Localization.functor_additive_iff` for `Qh` prove additivity directly.

The original direct dependency `lem-pc-bounded-above-flat-kflat-site` is replaced by the
existing `ringed_cech_koszul_dual_tower_isKFlat` result. Its generic bounded-flat theorem
remains a transitive dependency of that existing result, so this is not a claim to prune
its module from the targets' closure. The top-level approval for the unused direct
application is removed, preserving the order of the remaining approvals.

The original direct flat-sheaf definition dependency is not used to reprove Koszul
flatness: the existing finite-flat Koszul theorem is reused. Exact products preserve the
product quasi-isomorphism by the already proved adopted-source
`HomologicalComplex.quasiIso_limMap`; the derived-product theorem remains needed for the
actual-projection triangle through the new coordinate comparison. The former direct
`def-weil-abstract-derived-category` proof dependency is likewise used inside that
comparison, rather than as a separate top-level proof step; its statement dependency and
module remain in use.

Removed the unnecessarily broad public import
`Sheaf.CategoryTheory.ScalarLocalizationDerivedHom`, replacing it with the module that
now defines the same coefficient action, `ScalarLocalizationCoefficientActions`.
The item uses no derived-Hom comparison; no downstream Lean module needs adaptation.
This removes a dependency from this module, without claiming that the Hom-comparison
module is absent from every other target branch.

Removed the now-unused direct proof imports
`Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat` and
`WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore`; the needed
results are supplied through the reused Koszul theorem and the new coordinate theorem.
No existing module is withdrawn. No upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The advertised additive-localization node currently has no available source module. Its
mathematics is unnecessary for this proof because the more specific Mathlib route through
the homotopy quotient and the derived fraction localization supplies the conclusion.
The explicit transition-natural derived-tensor comparison and coordinate-to-cocone
comparison needed Lean proofs beyond the original dependency interfaces; both are proved
here. No mathematical statement correction is made, and the unit route is preserved.

## New nodes

`lem-sbc-koszul-tensor-derived-tower` realizes
`CategoryTheory.koszulTensorDerivedTower` in
`Sheaf.CategoryTheory.KoszulTensorDerivedTower`. A flat K-flat resolution of the variable
complex computes tensor naturally in the Koszul factor. Fixed K-flat tensor compares its
ordinary tensor tower to that of the original complex. The two natural comparisons give
the stipulated tower isomorphism. The empty list and arbitrary coefficients are allowed.

`lem-sbc-roos-coordinates-derived-limit` realizes
`CochainComplex.derivedLimitTriangle_of_roos_coordinates` in
`Sheaf.Algebra.Homology.RoosCoordinatesDerivedLimit`. The negative second coordinate and
first projection give a degreewise invertible map to the native mapping cocone. The
localized product cone is limiting under exact countable products. Transporting the native
distinguished triangle gives precisely the specified localized transitions and projections.

Change record: `coord/changes/X3-koszul-fibre-proof-context.md` records the new
proof-section commands, elaboration settings and private helper instances requested
by preflight. The consumer check finds zero downstream modules; no adaptation is
needed. The same record also documents the narrowed coefficient-action import.
Existing public statements and definitions are unchanged.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
