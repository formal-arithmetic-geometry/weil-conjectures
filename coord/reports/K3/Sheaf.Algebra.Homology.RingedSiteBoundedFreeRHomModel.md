## What changed

Proved `CategoryTheory.ringedSite_boundedFree_rhom_model` with its existing signature.
Its proof combines the existing K-injective computation of derived internal Hom with two
new, proved lemmas:

- `RingedSiteBoundedFreeRHomFiniteSupport`: restrict the product fan to the finite interval,
  construct coordinate inclusions by its universal property, and apply the finite-bicone
  product/coproduct theorem. The original signed differential formula is retained.
- `RingedSiteBoundedFreeRHomMapQuasiIso`: transfer exactness of finite-free internal Hom to
  retracts. For each homology degree, truncate the source far enough below that degree;
  the three relevant Hom terms are unchanged. Apply the existing bounded exact-term Hom
  comparison, then use bounded-below injective resolutions, naturality of the functorial
  K-injective replacement, and two-out-of-three for an arbitrary K-injective target.

Repair of return 9e5db492b5: removed the duplicate private
`CategoryTheory.shortExact_of_retract` from the comparison module. The original
`AlgebraicGeometry.Scheme.shortExact_of_retract` was private; exposed that existing theorem
in `Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom`, imported its module, and
used the qualified name. Its binders and proof are unchanged. This module is unclaimed;
no module held by another group is adapted. The one existing internal caller is unchanged.
The visibility change is recorded in `coord/changes/shortExactOfRetractVisibility.md`.

All new imports used only in proofs are ordinary imports. No existing definition,
universe binder, target statement, or mathematical statement changed.

Validation: all four delivered Lean modules compile without warnings through
`lcompile.py --all`. The exposed existing module compiled in 34.6 seconds, the
comparison module in 37.5 seconds, and the item in 23.5 seconds.
`tools/import_prune_check.py` passes for both the new comparison module and the
visibility change, including the exact duplicate-statement check behind the return.
`deliver3.py --no-push` returned OK: all delivered modules compile and pass preflight.
The delivery is classified CODEX for independent review of the nodes and visibility change.

## Proved and sorry left

Closed the one original hole in `CategoryTheory.ringedSite_boundedFree_rhom_model`.
Added zero holes; no `sorry` remains in any delivered Lean module.
The new declarations `CategoryTheory.ringedSite_boundedFree_rhom_finiteSupport` and
`CategoryTheory.ringedSite_boundedFree_rhom_map_quasiIso` are proved, with all private helpers
proved. These are proved components, not unfinished split-offs. The proof still uses existing
library declarations and inherits their dependencies; it does not claim to close those holes.

Edge cases checked in the argument: empty diagonal interval, zero-rank free sheaves,
zero terms of the source truncation, and a K-injective replacement unbounded below.

## No longer needed

Removed the duplicate generic retract helper (not a hole) and reused its existing
library implementation. No mathematical node is pruned by this reuse; the new ordinary
import of `StrictlyPerfectDerivedInternalHom` is required for its exposed helper.

Removed these proof imports from the item module:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Sheaf.CategoryTheory.DoubleComplexTotal`
- `Sheaf.Algebra.Homology.FirstQuadrantTotalComparison`
- `Sheaf.Algebra.Homology.QuasiIsoHomComplexMap`
- `Sheaf.Algebra.Homology.HomComplex`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`

The explicit double-complex construction `def-sp-double-complex-total` and the column
comparison `lem-sc-first-quadrant-total-column-comparison` are not used by this route.
Finite source truncation and the proved `lem-pc-bounded-exact-term-hom-quasi-iso` replace
those steps. This also removes the signed-totalization identification subproblem.

The old direct localization-lifting step `lem-weil-pbc-kinjective-hom-derived` is unnecessary:
the existing `derivedInternalHom_obj_iso` and naturality squares suffice. Its direct import
is removed, although the underlying K-injective theory remains available transitively.
The direct derived-object representative node
`lem-weil-pbc-dplus-injective-representative` is also unnecessary. We instead use the proved
source lemma `CochainComplex.KInjectiveResolution.exists_of_isStrictlyGE`, recorded under
`def-sp-kinjective-bridge`, which supplies an actual bounded-below resolution map.
The bounded-below injective existence, enough injectives, Hom-complex projections, internal
Hom, and `lem-pur-rhom-well-defined` are still needed in the new comparison module or
through the public imports of the existing derived-Hom API; they are not globally pruned.

The parent node's unused top-level tool approvals are withdrawn for
`lem-sp-grothendieck-enough-injectives`, `lem-weil-pbc-dplus-injective-representative`,
`lem-weil-pbc-kinjective-hom-derived`, `def-pur-sheaf-hom`,
`def-weil-sheaf-of-modules-category`, `def-sp-double-complex-total`,
`def-pur-hom-complex`, `lem-sc-first-quadrant-total-column-comparison`, and
`lem-pur-rhom-well-defined`. Necessary generic tools are declared on the new nodes.
No unit statement or realized unit step is bypassed or withdrawn.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated an existing private generic lemma. The repair makes
that existing lemma reusable and removes the duplicate, exactly as requested by the
landing return. No statement defect was found. The original plan supplies a valid but
longer route through an explicitly signed first-quadrant total complex. Finite source truncations let the existing
bounded exact-term Hom comparison prove the same assertion without constructing that complex.
A lower bound on the arbitrary K-injective target is not assumed: a separate naturality
argument extends the bounded-below comparison to that target.

## New nodes

`lem-weil-pbc-ringed-site-bounded-free-rhom-finite-support` records the proved finite-diagonal
product/coproduct calculation, including projections, differential, coordinate inclusions,
and the empty interval. Its module is
`Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomFiniteSupport`.

`lem-weil-pbc-ringed-site-bounded-free-rhom-quasi-iso` records the proved comparison into an
arbitrary K-injective target. Its proof uses finite-free exactness, retracts, finite truncation,
and the existing bounded Hom comparison. Its module is
`Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomMapQuasiIso`.

Both nodes have their statements, sources, Lean attachments, complete proof steps, and
three kinds of actual Mathlib searches. The parent node's proof and proof dependencies
follow the implemented route. The visibility change record is
`coord/changes/shortExactOfRetractVisibility.md`.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
