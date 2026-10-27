## What changed

Filled the four theorem proofs in `Sheaf.Paper.IntegralConstructibleLinear`.
Constructed the coefficient ring map to compatible completed sections from
`integralScalarConstant` and its prescribed finite residues. Restricted the existing
`SheafOfModules.homLinear` structure along that map. Identified the specified chain
and derived scalar endomorphisms with the center action used by Mathlib localization.
Proved uniqueness by equality of each Hom module's scalar multiplication. Transferred
integer-shift linearity from localization and through the faithful full-subcategory
inclusion. All existing public signatures, instance bodies and public imports stay unchanged.

Added private proof imports of
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule` and
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`.
All added helpers are private and proved. Updated the owning node's proof and
proof dependencies while preserving its active intrinsic-category Lean attachment
and the existing `SfIntegralConstructibleLinear` argument.

## Proved and sorry left

Closed 4 of 4 original holes, all associated with
`lem-weil-integral-constructible-linear`:

- `WeilConjectures.integralConstructible_linear`.
- `WeilConjectures.integralCoefficientLinear_existsUnique`.
- `WeilConjectures.integralCoefficientShift_linear`.
- `WeilConjectures.integralConstructibleShift_linear`.

No sorry remains in the delivered module. Added 0 holes; split off 0 statements.
The final lcompile.py single-file check passed in 9.5 seconds, without warnings.
All nine existing public declaration signatures and all public imports were checked unchanged.

## No longer needed

Removed these redundant private imports:

- `Sheaf.NumberTheory.Padics.AdicLimitFiniteModules`.
- `Mathlib.CategoryTheory.Limits.HasLimits`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `Sheaf.Paper.DerivedCompleteIntegralDetailed`.

The historical Step 1 dependency `lem-pod-adic-limit-finite-modules` is unnecessary
for this construction: a scalar has compatible constant residues without requiring
an identification of the valuation ring with the inverse limit. No whole module is
withdrawn, and this report makes no claim that other consumers cease needing those
modules or nodes. All four previous active proof dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The active node attachment now belongs to `Sheaf.Paper.SfIntegralConstructibleLinear`,
whose proved interface still depends on the legacy holes assigned here. The active
three-step node proof described their use rather than their proof. The delivery
prepends the actual construction and uniqueness argument and retains the intrinsic
steps and attachment. No statement repair is needed.

`Sheaf.Paper.RationalThickEvaluation` contains a proved parallel construction on
slice sites, but imports the assigned module, so it cannot be imported here. Its
private proof pattern was specialized locally, using the same existing Mathlib and
source-library lemmas. The construction uses the actual completed coefficient
sheaf throughout, including for the empty scheme; it does not assume a discrete
constant-sheaf identification, invertibility of the uniformizer, or finite Tor dimension.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
