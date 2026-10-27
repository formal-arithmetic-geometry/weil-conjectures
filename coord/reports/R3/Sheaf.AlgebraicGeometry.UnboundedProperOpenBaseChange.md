## What changed

Proved `AlgebraicGeometry.Etale.unboundedProperOpenBaseChange_of_normalization` with its
original signature and public imports. Representative normalization extends to a derived-unit
identity on every complex. The ordinary cube follows from support monicity, normalization
and mate pasting. The derived cube follows from the four unit equations and exact-functor
localization comparisons, cancelling an invertible derived unit on a K-injective model.

Repaired every duplicate reported for returned delivery c69f300ae5c:

- Removed the item's private `factorsh_hom`, `factorsh_inv`, `unitQ_homotopy`,
  `Qh_map_quotient`, `square_factors`, and `exchange_unit` proofs. Exposed the existing
  proved `exchange_unit` in `DerivedExchangeModuleTermwise` as `derivedExchangeUnitQ`
  and used it in both modules. Its five support helpers remain private and proved in
  their original module. Its required `ShortExactPullback` import becomes public.
- Removed the item's private `open_compare_mono`. Exposed the existing proved helper
  in `UnboundedProperOpenPasting` as `mono_openImmersionLowerShriekToLowerStar_app`,
  and imported and used that theorem. Its original internal caller uses the exposed name.

Only these three Lean modules are submitted. Both API owners were unclaimed when the
repair began. Their existing public signatures and definition bodies stay unchanged.
The existing owner nodes attach the exposed corollaries; the item node follows the actual
proof dependencies. No source-library module is changed.
Change record: `coord/changes/R3-proper-open-shared-normalization-api.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.unboundedProperOpenBaseChange_of_normalization`
(node `lem-amb-unbounded-proper-open-base-change`).
Zero `sorry` remain in the item; zero holes added; zero statements split off.
All three submitted modules contain zero `sorry`.
The two shared helper proofs were already proved and are reused, not counted as hole closures.
Validation: `lcompile.py --all` on the three submitted modules and the delivery preflight.

## No longer needed

The six copied exact-derived helpers and copied monicity proof are removed from the item.
The draft proof import `Sheaf.CategoryTheory.DerivedExactMate` is replaced by
`Sheaf.AlgebraicGeometry.DerivedExchangeModuleTermwise`; the generic factorization remains
an indirect dependency. The direct proof import of `ProperSupportSheafComposition` is
replaced by `UnboundedProperOpenPasting`, the owner of the reused monicity proof.
All original public imports remain. No complete module is withdrawn or claimed pruned.
The existing private monicity proofs in other library modules are unchanged.

The original compatible diagram of three separately chosen K-injective resolutions and
explicit Hom-bijection lifting step are unnecessary. Thus
`lem-weil-pbc-kinjective-hom-derived` is not a direct proof dependency: naturality of the
right-derived unit replaces those steps. The separate theorem
`lem-cbc-derived-extension-zero-base-change-underived-compatibility` and module
`Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChangeUnderivedCompatibility`
are not imported: the specified comparisons already satisfy the required identity in
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`.
Likewise `lem-weil-pbc-underived-exchange-module-linear` and
`Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear` are not directly used:
the ordinary cube is formed in the category of module sheaves. These are pruning choices
for this proof, not withdrawal of existing declarations or their dependencies.

## Where the brief, the DAG or earlier work was wrong

The returned packet copied existing private proofs. Those names cannot be imported.
The repair exposes the existing unit identity and monicity theorem in their original
modules, imports them, and leaves their proofs in place. No copied helper proof remains
in the item. The original compatible-resolution diagram is unnecessary: normalization
extends naturally, and the derived cube follows formally from the sheaf cube in Tag 0F7F.
No exchange is cancelled, inverse image is never assumed to preserve K-injectives,
and the unit route and item statement remain unchanged.

The retained earlier report records that the launcher reset `.budget.start` from
1792746468.7366037 to 1792774192.8920457 on resume. The worker did not change this metadata.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
