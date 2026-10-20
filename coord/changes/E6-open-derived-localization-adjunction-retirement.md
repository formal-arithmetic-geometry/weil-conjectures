# AlgebraicGeometry.open_derived_localizations_and_adjunction

## Reason

Complete the retirement explicitly assigned by coord/retire-items.tsv, row for
Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction, under the human hand-off in
coord/changes/retire-sheaf-twins-20261020.md. M5's recent reviewed repair preserved the
full combined wrapper under a distinct name; it did not retire the module, so the queue
assigned it again. The current wrapper is already fully proved and has zero importers.
The six DAG parents already live upstream and use the separate proved components.

This withdrawal is justified by the upstream replacement argument and reconciled parent
proof records, not solely by zero Lean importers. No upstream declaration, signature,
attribute, public import, proof, or non-theorem body is changed. No target changes.

## Old

```lean
theorem open_derived_localizations_and_adjunction
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (U : X.Opens) :
    ∃ hD : HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)),
    letI := hD
    ∃ hO : ∀ W : U.toScheme.Opens, HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over W)),
    letI := hO
    ∃ (R : DerivedCategory
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
        schemeDerivedCategory X),
      Nonempty ((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R)
```

Module public import: WeilConjectures.AlgebraicGeometry.DerivedCategory.
Private imports: WeilConjectures.AlgebraicGeometry.OpenDerivedLocalizationAdjunction
and WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization.

## New

Withdraw the unused Sheaf wrapper via deleted.txt. Its complete mathematical assertion
is jointly realized by the existing upstream declarations below and the existing node
lem-pc-derived-open-localization-universe, whose declaration is
AlgebraicGeometry.nonempty_derivedOpenLocalization in
WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization.

```lean
theorem nonempty_hasDerivedCategory_openSubscheme
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    Nonempty (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))

theorem open_derived_localization_adjunction
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    ∃ (R : DerivedCategory
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
        schemeDerivedCategory X),
      Nonempty ((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R)
```

The primary attachment is the adjunction theorem, explicitly documented as realizing
only the adjunction clause. The declarations list also records the localization-transport
theorem; the family clause comes from the existing dependency, after installing hD.
This is a joint realization of the unchanged node, not an identification of the narrower
primary theorem with the old combined type. The full old signature was compiled in a
validation-only scratch file with exactly the original six-line assembly proof. Its
axioms and those of all three components are exactly propext, Classical.choice and
Quot.sound. No arbitrary data is taken from an unproved existence statement.

## Users

A scan of lean/ and quarantine/ and downstream.py finds zero current direct or transitive
Lean importers and no applications of the combined wrapper outside its own module.
The following are all six DAG parents, also the historical retirement consumers.
Their proofs already import the upstream API; no Lean consumer adaptation is required.
Only their proof descriptions are reconciled to document their actual component uses.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction | E6 | Withdraw unused combined wrapper; preserve full node by joint upstream realization. |
| WeilConjectures.AlgebraicGeometry.DerivedOpenHomScalarMayerVietoris | unclaimed; upstream source | Unchanged; already uses upstream component API. |
| WeilConjectures.AlgebraicGeometry.LocalizedOpenImageComplexComparisons | unclaimed; upstream source | Unchanged; already uses upstream component API. |
| WeilConjectures.AlgebraicGeometry.SupportedMapAffineAttachment | unclaimed; upstream source | Unchanged; already uses upstream component API. |
| WeilConjectures.AlgebraicGeometry.PerfectHomGap | unclaimed; upstream source | Unchanged; already uses upstream component API. |
| WeilConjectures.AlgebraicGeometry.SupportedMapAffineUnionGluing | unclaimed; upstream source | Unchanged; already uses upstream component API. |
| WeilConjectures.AlgebraicGeometry.OpenDerivedRestrictionComparison | unclaimed; upstream source | Unchanged; already uses upstream component API. |

DerivedOpenHomScalarMayerVietoris applies the upstream adjunction for each open.
LocalizedOpenImageComplexComparisons applies the transport theorem to obtain hD.
OpenDerivedRestrictionComparison applies transport, adjunction, and the existing
family-localization theorem separately. SupportedMapAffineAttachment and
SupportedMapAffineUnionGluing use upstream open_derived_localization_data, which
packages the same transport and family construction. PerfectHomGap retains its
upstream imports; it never calls the combined wrapper. Quarantined sources have no
import or call of the combined wrapper. All six parent dependency edges remain.
The unit sk-thm-picard-duality and its realized lists are unchanged.

## Status

landed 20261020T233126-L-897306 2026-10-20 (merge of deliver/E6/Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction)
