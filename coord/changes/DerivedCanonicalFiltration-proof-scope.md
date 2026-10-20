# DerivedCategory.exists_derivedCanonicalFiltration

## Reason

Record the proof-scoping commands detected as an interface change by preflight.
The sole existing theorem has exactly its original signature and visibility.
All added declarations are private, fully proved construction or proof helpers.
There are no new registrations, global instances, or public imports. The scoped
commands only control elaboration of individual helper declarations and the
existing theorem. No target statement or definition changes.

## Old

The original module has the following surrounding commands, with its one theorem
between the variable declarations and namespace end:

```lean
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open CochainComplex
namespace DerivedCategory
variable (R : Type u) [CommRing R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]
end DerivedCategory
```

Proof imports removed:

```lean
import Sheaf.Algebra.Homology.FilteredQuasiIsoFractions
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.CategoryTheory.Abelian.Filtration
```

## New

All the original surrounding commands remain. The following command prefixes
are added, each scoped to the immediately following declaration:

```lean
omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem filtered_ext

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem restrict_homotopy

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem common_bounds

set_option backward.defeqAttrib.useBackward true in
private theorem localization_comparisons

set_option linter.unusedVariables false in
theorem exists_derivedCanonicalFiltration
```

The existing theorem's full signature is unchanged verbatim. The `omit` prefixes
remove unused derived-category instances from private helper arguments. The
backward-defeq setting is local to the comparison helper. The linter setting
preserves the original public signature's binders, some used only implicitly.
All three removed imports are proof-only; the two definitions imports are
redundant through retained public imports. Filtered-target fractions are pruned
by the new source-localization argument. One proof-only import is added:

```lean
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Fractions
```

## Users

The downstream scan reports the following import consumers. A textual scan for
`DerivedCategory.exists_derivedCanonicalFiltration` finds no external use yet;
the item itself is the only textual occurrence. Every downstream module retains
its statements, definitions, imports, and elaboration interface: private helper
names and declaration-local settings are not exported. No consumer adaptation
is needed or included.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.DerivedCanonicalFiltration | D4 | proof and private helpers only; original signature unchanged |
| Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence | T6 | unaffected |
| Sheaf.Algebra.Homology.IntegralBoundedKunnethExact | R7 | unaffected |
| Sheaf.AlgebraicGeometry.ArbitrarySchemeUntensoredBaseChange | K3 | unaffected |
| Sheaf.AlgebraicGeometry.IntegralDerivedTensorBoundedTorsion | M9 | unaffected |
| Sheaf.AlgebraicGeometry.IntegralProperProjectionFormula | Q9 | unaffected |
| Sheaf.AlgebraicGeometry.KunnethMapAgrees | A3 | unaffected |
| Sheaf.AlgebraicGeometry.NormalGenericFibreVanishing | F4 | unaffected |
| Sheaf.AlgebraicGeometry.OpenProductExchange | B8 | unaffected |
| Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReduction | A9 | unaffected |
| Sheaf.AlgebraicGeometry.ProperKunnethGlobalSections | G7 | unaffected |
| Sheaf.AlgebraicGeometry.PunctualTensorBaseChange | G8 | unaffected |
| Sheaf.EtaleCohomology.KunnethOneProper | unclaimed | unaffected |
| Sheaf.Paper.KunBcKunnethCompat | T3 | unaffected |
| Sheaf.Targets.BaseChangeTowardsFields | F9 | unaffected |

## Status

landed 20261020T051126-L-1568534 2026-10-20 (merge of deliver/D4/Sheaf.Algebra.Homology.DerivedCanonicalFiltration)
