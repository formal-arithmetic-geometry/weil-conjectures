## What changed

Proved `AlgebraicGeometry.Scheme.finite_scalar_perfect_refinement` without changing its
statement, definitions, universe parameters or public imports. The construction takes a
finite affine refinement of the supplied pro-etale cover, orders the supplied bounds,
chooses attained finite extrema, restricts the supplied representing isomorphisms, and
transports the supplied degreewise splittings through normalized finite-free isomorphisms.

Added three proof helpers, each with its own module and DAG node:
`FiniteAffineProEtaleRefinement`, `ScalarPerfectFiniteFree`, and
`ScalarPerfectChartRestriction`. The latter two work with a coefficient universe
independent of both site universes. The restriction comparison uses the sheafification
adjunction and local bijectivity; the finite-free comparison uses its rank-one case and
preservation of finite products by additive functors. Exactness is used only for further
slice restriction, never for scalar extension. Updated the item node's proof and
dependencies to this implemented argument.

Validation: all four modules compiled together in import order through `lcompile.py`
(3.0s geometry, 30.0s restriction, 14.5s finite-free, 16.8s item). Removed the
remaining unused-section-variable warning before final delivery validation.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.finite_scalar_perfect_refinement`
(`lem-sfb-finite-scalar-perfect-refinement`).

Also proved the new helpers:
`AlgebraicGeometry.Scheme.finite_affine_proetale_refinement`,
`SheafOfModules.exists_scalarPerfectChartFiniteFreeIso`, and
`SheafOfModules.scalarPerfectChartRestrictionIso`.

Holes closed: 1. Holes added: 0. Sorries left in the delivery: none. No split-off
unproved statements. Existing stated additivity and locally bijective ring-unit
lemmas in `StrictPerfectCoefficientPackageOfUniverses` are used as intended by stage 3.

## No longer needed

Removed these proof imports from the item:

- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` (geometry is handled in the helper).
- `Sheaf.Algebra.Homology.SliceModuleSheafification`.
- `Sheaf.Algebra.Homology.SliceTensorNatural`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`.

This proof no longer depends on `lem-weil-pbc-slice-module-sheafification`,
`lem-weil-pbc-slice-tensor-natural`,
`lem-pur-site-restriction-module-adjunction-exact`, or
`lem-pc-sites-module-sheafification-tensor`. The new comparison proves exactly the
scalar-extension restriction needed here at independent universes, directly from
sheafification. Further restriction preserves finite colimits by its Mathlib
adjunction and finite limits by the forgetful presheaf comparison. The normalized
finite-free calculation uses the rank-one comparison and finite products.

The separate references `lem-pqf-finite-affine-cover-qc-open` and
`lem-weil-pbc-fpqc-covering-axioms` are unnecessary for this proof: the Mathlib
finite affine subcover and pro-etale precoverage binding APIs perform these steps;
the existing Mathlib leaf `sk-def-pe-site` records these ingredients. The Mathlib
weakly-etale stability leaf is retained by the geometric helper.

The old top-level `tool_uses` approvals are removed from the item's node because its
proof now uses the helpers and Mathlib directly. No module is withdrawn and no
upstream declaration is removed. These dependency removals concern this proof;
other consumers of the old general lemmas remain intact.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The existing
`Sheaf.AlgebraicGeometry.FiniteAffineProetaleRefinement` assumes local Noetherianity
and quasi-separatedness, so it cannot be applied to this item; the new geometric
lemma imposes neither condition. Several originally suggested general site lemmas
fix the site and module universes together, while this item deliberately allows a
larger independent coefficient universe. Their direct application therefore does
not typecheck here. The new helpers give the needed comparisons at the declared
universes. The finite interval argument can simply replace both supplied endpoints
by their minimum and maximum; it needs no separate zero-complex choice. Original
ranks, including those outside the interval, are preserved exactly as the theorem
requires. The old natural-language step 7 suggested taking rank zero outside the
interval; that need not equal a supplied splitting rank of the zero module, so the
implemented proof retains the supplied ranks instead.

Checked the geometric argument without quasi-separatedness or quasi-compactness of
individual covering members. The construction uses a finite affine cover of the
base before refining each pullback. Rank zero uses the empty product, and the
scalar comparison imposes no flatness assumption.

## New nodes

`lem-sfb-finite-affine-cover-refinement-general`: finite nonempty refinement of any
pro-etale cover of a nonempty quasi-compact scheme by affine opens of its members.
It implements the first two steps of the original plan using the Mathlib covering API.

`lem-sfb-scalar-perfect-chart-finite-free`: the normalized finite-free isomorphism,
including its pure-section coordinate formula and rank zero. It is proved through
rank one and the finite-product comparison.

`lem-sfb-scalar-perfect-chart-restriction`: natural compatibility of the actual
chart scalar-model functors with further slice restriction, at independent universes.
Its sheafification comparison is invertible by local bijectivity of both units.

No existing definition or statement was changed; no change record is needed.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
