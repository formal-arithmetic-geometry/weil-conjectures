# Derived tensor shift descent: private proof context

## Reason

The proof of `SheafOfModules.derived_tensor_shift_descent` constructs coherent
signed shifts by two applications of bifunctor localization, proves their exact
normalization, and deduces uniqueness and fixed-factor compatibility. The private
comparison APIs require local control of reduction of the quotient-shift instances.
The preflight conservatively classifies added context commands as an interface
change; this record documents their precise scope.

## Old

`Sheaf.Algebra.Homology.DerivedTensorShiftDescent` had the existing four public
definitions and one unfinished theorem, with `open CategoryTheory` and the original
site variables, universes, `autoImplicit`, and instance-size settings.

## New

The four public definition bodies, all five public signatures, and every public
import remain byte-identical. The original `open CategoryTheory` is preserved.
After the public definitions, a private proof section contains:

- `open CategoryTheory.Functor`, for proof notation such as `curry` and `uncurry`;
- `[local irreducible] SheafOfModules.monoidalCategory`, avoiding expansion of the
  constructed sheaf tensor while using its existing API;
- `[local semireducible] HasShift.quotient ObjectProperty.hasShift
  Quotient.functor_commShift ObjectProperty.commShiftι`, exposing the canonical
  quotient and subcategory shift equations;
- the section-local `backward.isDefEq.respectTransparency` option, with explicit
  declaration-local overrides, including `backward.isDefEq.respectTransparency.types`,
  for comparison conversions.

The nested `QuotientSquares` section introduces only generic private-helper variables
and the local notations `K₀`, `H₀`, and `q₀`. It closes before the subsequent helpers.
The outer private proof section also closes before the namespace ends. These opens,
notations, options and local attributes do not survive the section. No exported
instance, attribute, notation or public declaration is added. No public definition
is elaborated inside the added private context. The public theorem's original
signature is unchanged; its proof may use the proved private helpers.

The added imports are proof-only. Neither source-library files nor other Sheaf
modules are edited. The item's node changes only its proof description, proof
dependencies and proof origin. No target statement or definition meaning changes.

## Users

| Module | Holder | Effect |
| --- | --- | --- |
| `Sheaf.Algebra.Homology.DerivedTensorShiftDescent` | V2 | Fill its one theorem hole; add private proof helpers and scoped proof context. |
| `Sheaf.CategoryTheory.InternalInflationGradedCup` | unchanged consumer | Its existing proof-only import retains the same public API; no adaptation. |

A search of both library roots found the second row as the only direct importer.
It contains no explicit reference to the five assigned public declaration names.
No external module can refer to the new private helpers. The public definitions,
public imports and theorem signature were compared directly with the current source.
The complete proof compiled without warnings in 50.6 seconds, and the delivery
compile passed before preflight requested this context-command record.

## Status

landed 20261022T013506-L-3591887 2026-10-22 (merge of deliver/V2/Sheaf.Algebra.Homology.DerivedTensorShiftDescent)

Submitted for the independent stage-3 review. No consumer or source-library change
is requested.
