# integralGeneralLfpHomInversion (proof context and new helper instances)

## Reason

The proof transports large coefficient functors through exact equivalences. Local
irreducibility keeps the existing derived-category and closed-structure constructions
abstract during elaboration. The two new coefficient modules fix the canonical small
Grothendieck-derived categories uniformly, exactly as the assigned module already does.
No public import or target meaning changes. The ring alias retains exactly its
value; its elaboration interface is changed as recorded below.

## Old

The assigned theorem body was `:= by sorry`. Its fifteen data values,
its public imports, and its theorem signature are retained byte for byte.
The ring declaration was:
```lean
abbrev ring := ModuleObjectRingedComparison.ring (Profinite.padicIntegersRingObj l E.1) X
```
The three helper modules did not exist. The coefficient map originally inferred its source from `sectionScalarMap`.

## New

```lean
def ring := ModuleObjectRingedComparison.ring (Profinite.padicIntegersRingObj l E.1) X
```
The value is unchanged. The coefficient map explicitly declares source `ring l E X`
and the same rational target; its body is unchanged. This preserves definitional
identity while avoiding eager expansion of the coefficient construction. Canonical
sheafification, monoidal, coefficient-multiplication, derived-category, additive and
scalar-tower-colimit instances are named once, each by its original `inferInstance`
construction. They add no assumptions and change no object or map.


The assigned module adds local irreducibility for
`HasDerivedCategory.ofIsGrothendieckAbelian`, `Functor.mapDerivedCategory`,
`InternalAbelianSheafModule.sectionModuleEquivalence`, `sectionRingSheaf`,
`sectionScalarMap`, `coefficientMap`, `leg`, `DerivedCategory.Q`,
`localizationHomResolutionIso`, `sheafCompose`, `monoidal_upperStarFromPoint`,
`laxBraided_upperStarFromPoint`, `ProEtale.upperStar`, `Profinite.continuousMapRingSheaf`, `localizationHomComparison`, `localizationHomRestrictedComparison`,
`CoefficientClosedStructure.tensor` and `CoefficientClosedStructure.evaluation`.
The proof also keeps `Mod.monoidalClosed`, `upperStarFromPoint`, `homComplexFunctor`,
`coefficientHomResolution`, `coefficientHomResolutionIso`, `CondensedRing.derivedHom`
and `scalarDerivedRestriction` abstract, together with `localizationHomComplex`. All attributes are local; importers inherit
none of them. The scalar helper additionally abstracts `Mod.extendScalars`, `Functor.leftDerivedFunctor` and
`Sheaf.monoidalCategory`. The scalar helper and assigned proof also abstract
`Localization.Monoidal.instMonoidalCategoryLocalizedMonoidal` and
`Localization.Monoidal.monoidalCategoryStruct`, the existing localization data
behind the sheaf tensor. Native module Grothendieck and colimit instances receive
local priority 2000, as in the existing sequential-continuity module.
The main file uses transparency-respecting elaboration after its scalar-data interface,
so categorical proofs do not unfold these constructions. Backward definition matching
is disabled after that interface except for the continuity transport. The telescope
presentation uses explicit cocone data and a separately proved mapped-leg recurrence;
this avoids repeatedly reconstructing dependent colimit data during elaboration.
The native colimit instances receive local priority 2000 in the assigned module too.
No reducibility status of a structure projection
is altered.

Each new coefficient module constructs a distinct named local instance, with body
`fun R ↦ HasDerivedCategory.ofIsGrothendieckAbelian (scalarModules J R)`, at
universes `{u + 1, u + 1, u + 2}`. These fix the existing small localization and
introduce no new hypothesis. They are local rather than private, so public theorem
signatures contain no private declaration. Their names are attached to their own nodes.
The generic telescope comparison introduces only theorem universe parameters. Its
normalized-comparison theorem chooses a bounded-below representative and uses full
restriction to identify the transported isomorphism with the unit-normalized map.
The generic interface avoids repeatedly unfolding the concrete sheaf constructions
during elaboration; both the transport and the identification are fully proved.

Private proof helpers are completely proved. The options only adjust elaboration,
instance search and the private-module style linter, following the existing continuity
module's proof context. Kernel checking is unchanged. No declaration in the adopted
source-library tree is edited.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | D5 | Ring alias becomes a definition with the same value; coefficient-map type explicit; theorem signature unchanged. |
| Sheaf.Paper.IntegralSectionScalarTelescope | D5, new | Canonical local instance and actual-coefficient telescope theorem. |
| Sheaf.Paper.IntegralSectionHomContinuity | D5, new | Canonical local instance and actual-coefficient continuity theorem. |
| Sheaf.Algebra.Homology.ScalarTelescopeHomComparison | D5, new | Generic proved comparison; no changed existing interface. |

`tools/downstream.py Sheaf.Paper.IntegralGeneralLfpHomInversion --uses
AlgebraicGeometry.ProEtale.IntegralHomInversion.integralGeneralLfpHomInversion`
reports zero downstream Lean modules and only the assigned module as a textual user.
Unfinished DAG parents remain users and the assigned item remains in place. None
requires adaptation because its whole original public interface is preserved.
The ring value and coefficient map are definitionally unchanged. The reader should
verify this alias-interface repair does not change the target meaning.

## Status

landed 20261026T001230-L-4177136 2026-10-26 (merge of deliver/D5/Sheaf.Paper.IntegralGeneralLfpHomInversion)
