# CategoryTheory.internalHom_localization_comparison: proof command scope

## Reason

The stage-3 preflight requires a record for additional top-level variable, open
and attribute commands, even when they serve private proof helpers. The complete
proof needs monoidal notation, distinguished-triangle notation, a local additive
instance for tensor localization, and local control of expensive unfolding.
This record covers those commands in the item module. It changes no public
signature or definition and needs no consumer adaptation.

A first packet used `private instance localizationTensor_additive`. Private names
do not make instance registration local. That packet was not pushed. The repaired
packet uses a private proved theorem and `attribute [local instance]`, so the
additive registration is confined to this module's proof.

## Old

The existing common opening is verbatim:

```lean
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules

namespace CategoryTheory
```

There was no LocalizationHomProof namespace, no localizationTensor_additive
helper, and no additional local attribute commands. The original five public
definition bodies and public theorem signature are preserved verbatim in New.

## New

Additional opening and local registration commands:

```lean
open CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

attribute [local instance] isMonoidal_W_independentCoefficients
attribute [local irreducible] SheafOfModules.monoidalCategory
  derivedInternalHomOfUniverses
```

The private helper namespace introduces its own abstract categories and universes.
Its variables end with the namespace. The remaining variable commands preserve
the original item's site, coefficient and derived-category binders. `omit` and
`include` commands specify only private helper parameters. The following local
attributes control proof elaboration:

```lean
attribute [local irreducible] ScalarHomCancellation.cancellationRestrictSheafifyIso
  ScalarHomCancellation.cancellationRestrictSheafifyHom
attribute [local irreducible] localizationComplexScalar
attribute [local irreducible] localizationComplexLeg
attribute [local irreducible] localizationHomComplex
```

The additive interface is now explicitly local:

```lean
omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
private theorem localizationTensor_additive : (scalarLocalization R s).Additive :=
  (scalarLocalization_exact R s).1

attribute [local instance] localizationTensor_additive
```

The proof also uses local elaborator options
backward.isDefEq.respectTransparency = false,
backward.isDefEq.respectTransparency.types = false, and
backward.defeqAttrib.useBackward = true. None adds a global attribute or instance.
No public import, existing definition body, target statement, or definition changes.

## Users

Read-only `tools/downstream.py` found zero current Lean importers. Its declaration
usage checks found the six public names only in this module. This does not withdraw
any node: parents with unfinished proofs and the unit route are retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.InternalHomLocalizationComparison | G4 | Proof-only local commands and private helpers; all six public interfaces unchanged |

No other module is adapted. The theorem's mathematical statement and the meanings
of the five definitions remain identical, so no target statement review is reopened.

## Status

landed 20261021T130027-L-2495751 2026-10-21 (merge of deliver/G4/Sheaf.Algebra.Homology.InternalHomLocalizationComparison)
