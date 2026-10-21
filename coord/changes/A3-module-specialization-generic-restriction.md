# AlgebraicGeometry.Etale.strictLocalSpecialization

## Reason

Restore the quarantined ModuleSpecializationAbelianIso item with its original statement
and complete proof. Its archived dependency SmoothProperPrimeSpecialization still uses
existsUnique_strictHenselizationStalkRestriction and publicly imports the withdrawn
Sheaf.AlgebraicGeometry.StrictHenselizationRestriction. That specialized API was retired
by the reviewed M2 generic section-cone delivery. The canonical upstream restriction
uses strictLocalization, a different scheme model, and cannot replace the small model
in these statements.

Use (strictLocalSectionCone s).existsUnique_restriction, whose component restriction
and predicate specialize to the former small-model definitions. The germ equations
uniquely determine the map, so changing the proof providing that unique restriction
preserves the chosen map. All terminal-section, geometric-germ and inverse-image-stalk
factors are preserved verbatim. The repaired definition is definitionally equal to
etaleStalkSpecialization, checked in a Lean probe. No hypothesis, universe, theorem
signature, target meaning or source-library declaration changes.

ModuleSpecializationAbelianIso is restored from its quarantine archive, not withdrawn.
Its retired derived-comparison import is replaced by the canonical upstream coefficient
comparison module defining the identical moduleAbelianForget abbreviation. Its private
strict-local germ proof uses the generic restriction and strictLocalNeighbourhoodSection.
Its small-model structural-map leg equation uses exists_strictHenselizationStructuralMap
rather than the unrelated canonical-model equation with the old short name.

SpecializationCospecializationArrows is an unclaimed dependency whose naturality proof
has the same stale API calls. Its proof is migrated to the generic restriction API;
all signatures, public imports and non-theorem bodies remain verbatim.

ProperLocallyAcyclicSpecialization also used rightDerivedLowerStarPlus in its public
statement but obtained the name only through a private proof import. The compiler
reported the hidden public name at line 300. Add its defining coherence module as
an explicit public import there and in SmoothProperPrimeSpecialization, whose public
statement uses the same name. This repairs visibility without changing a declaration.

## Old

SmoothProperPrimeSpecialization public import:

```lean
public import Sheaf.AlgebraicGeometry.StrictHenselizationRestriction
```

```lean
noncomputable def strictLocalSpecialization
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Scheme.pointSmallEtale s).sheafFiber.obj G ⟶
      (Scheme.pointSmallEtale (t ≫ Scheme.strictHenselizationStructuralMap s)).sheafFiber.obj
        G :=
  Classical.choose (existsUnique_strictHenselizationStalkRestriction s G) ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (Scheme.strictHenselizationScheme s))
        (Scheme.Etale.mk (𝟙 (Scheme.strictHenselizationScheme s)))
        Over.mkIdTerminal)).hom.app _ ≫
    (Scheme.pointSmallEtale t).toPresheafFiber
      (Scheme.Etale.mk (𝟙 (Scheme.strictHenselizationScheme s)))
      (Over.homMk t (by simp))
      ((upperStar AddCommGrpCat.{u + 1} (Scheme.strictHenselizationStructuralMap s)).obj G).obj ≫
    (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
      (Scheme.strictHenselizationStructuralMap s) t).hom.app G
```

Restored item's archived public import:

```lean
public import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
```

## New

SmoothProperPrimeSpecialization public import:

```lean
public import Sheaf.AlgebraicGeometry.StrictLocalSectionCone
```

```lean
noncomputable def strictLocalSpecialization
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Scheme.pointSmallEtale s).sheafFiber.obj G ⟶
      (Scheme.pointSmallEtale (t ≫ Scheme.strictHenselizationStructuralMap s)).sheafFiber.obj
        G :=
  Classical.choose ((strictLocalSectionCone s).existsUnique_restriction G) ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (Scheme.strictHenselizationScheme s))
        (Scheme.Etale.mk (𝟙 (Scheme.strictHenselizationScheme s)))
        Over.mkIdTerminal)).hom.app _ ≫
    (Scheme.pointSmallEtale t).toPresheafFiber
      (Scheme.Etale.mk (𝟙 (Scheme.strictHenselizationScheme s)))
      (Over.homMk t (by simp))
      ((upperStar AddCommGrpCat.{u + 1} (Scheme.strictHenselizationStructuralMap s)).obj G).obj ≫
    (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
      (Scheme.strictHenselizationStructuralMap s) t).hom.app G
```

Both SmoothProperPrimeSpecialization and ProperLocallyAcyclicSpecialization also gain:

```lean
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
```

Their original public imports other than the retired restriction import are unchanged.

Restored item's replacement public import:

```lean
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison
```

The item theorem's signature and all its declarations' docstrings are preserved.
The new coefficient import provides the same canonical definition already adopted
upstream; no forwarding declaration or new definition is introduced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso | A3 | Restore archived theorem unchanged; adapt private germ proof and imports to current APIs. |
| Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization | unclaimed | Repair the unique restriction used by strictLocalSpecialization; identical specialization map and prime-specialization theorem statement. |
| Sheaf.AlgebraicGeometry.SpecializationCospecializationArrows | unclaimed | Repair only the stale restriction calls in etaleStalkSpecialization_naturality and close its final definitional equality. |
| Sheaf.AlgebraicGeometry.SpecializationCospecializationCompatibility | unclaimed | Consumer check; no edit or change in meaning. |
| Sheaf.AlgebraicGeometry.StrictBaseFibreMapFactorization | unclaimed | Consumer check; no edit or change in meaning. |
| Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization | unclaimed | Add the explicit public coherence import needed by its existing public theorem statement; no declaration changes. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | unclaimed, quarantined | Archived direct consumer of the restored theorem and prime-specialization theorem; both signatures and maps preserved, no adaptation needed. |

Source-only downstream.py finds no live importers of the quarantined item or of
SmoothProperPrimeSpecialization. The archived parent above is found separately by rg
in quarantine/Sheaf. The four live transitive consumers of
SpecializationCospecializationArrows are listed above. None needs a statement change.
No target is exposed to a different mathematical definition: the restriction remains
the unique map with exactly the same affine pointed-neighbourhood germ equations.

## Status

landed 20261021T203400-L-3709051 2026-10-21 (merge of deliver/A3/Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso)
