# AlgebraicGeometry.Etale.strictLocalSpecialization

## Reason

Restore the quarantined stage-3 item listed in coord/rework.tsv. Its archived proof
already has zero holes, but compiling the archive fails because the retired
StrictHenselizationRestriction module no longer exports the small-model restriction,
strictHenselizationScheme or strictHenselizationStructuralMap. Its public theorem also
uses derived functors available only through private proof imports.

Replace the retired restriction import with StrictLocalSectionCone and use its
existsUnique_restriction theorem. This is the generic restriction characterized by
exactly the same pointed-neighbourhood germ equations for the same small strict-local
scheme. The old and new choices are therefore equal by uniqueness; all remaining
factors of the specialization map stay verbatim. Add the public defining coherence
import for rightDerivedLowerStarPlus and the derived-category interface.

This implements the repair already described in the landed change record
A3-module-specialization-generic-restriction.md, whose proposed edits are still absent
from this quarantined archive. No theorem signature, docstring, proof body, universe,
mathematical object or target meaning changes. No source-library file changes.

## Old

The live item path is absent. Archived public restriction import:

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

## New

Restore the complete archived module, replacing the restriction import with:

```lean
public import Sheaf.AlgebraicGeometry.StrictLocalSectionCone
```

Add:

```lean
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
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

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization | A4, this item | Restore the archive and repair the restriction API and public visibility. |
| Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso | A4, quarantined | Same specialization map and theorem signature; no adaptation is forced by this repair. Its archived stale restriction calls are a pre-existing independent restoration defect. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | unclaimed, quarantined | Same prime-specialization theorem and map; no adaptation needed. |

The downstream.py --allow-missing --uses check reports zero live consumers. Searches
of lean/ and quarantine/ find the two archived direct consumers listed above, and
both remain needed in the DAG. Their imports and uses have not been removed. The
module-comparison consumer's current claim is A4 (coord/claims); the curves consumer
has no current claim. All public declarations retain their signatures. The existing
proof's final exact hsp typechecks, verifying that the repaired map is definitionally
equal to etaleStalkSpecialization used by ProperLocallyAcyclicSpecialization.

## Status

landed 20261022T025314-L-1271095 2026-10-22 (merge of deliver/A4/Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization)
