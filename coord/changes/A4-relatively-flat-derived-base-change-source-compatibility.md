# AlgebraicGeometry.relativelyFlat_derivedBaseChange_complex

## Reason

Restore the quarantined module assigned in coord/rework.tsv (row dated 2026-10-20).
Its archive has zero sorry holes. Compiling the unchanged archive fails at its
public signature: IsAcyclicTensorKFlat and SingleComplexBaseChange.counit are only
privately imported. The compiler requests public imports of Sheaf.Algebra.Homology.KFlat
and WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition. The
adopted source library already proves the same public theorem. Redeclaring that name would duplicate the adopted theorem.

Restore the historical Sheaf module path as a public compatibility import of
WeilConjectures.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex, retaining
Sheaf.Algebra.Homology.KFlat for the legacy predicate used by its archived signature.
The quarantine archive is preserved. This is restoration, not withdrawal; the DAG
attachment, mathematical result, parent dependencies and unit route are preserved.
No source-library file is changed.

The complete archived and source theorem signatures are textually identical after
replacing IsAcyclicTensorKFlat with IsKFlatTensor. Those two definitions have the
same binders and body. A sandbox consumer reproducing the full archived signature
compiled by applying the adopted theorem to all its original arguments, including
the legacy K-flat hypothesis. Its axiom check and the adopted theorem's axiom check
both give only propext, Classical.choice and Quot.sound. This checks all hypotheses
and the exact canonical map, including the arbitrary choice of alpha, rather than
only the name or the conclusion shape. No edge-case restriction is added.

The node now records the actual source declaration and its signature verbatim.
Step 2's description is synchronized with the source criterion API, which no longer
requires a separate upper-bound argument. The upper bound is still a hypothesis of
this theorem and is used by the flat-complex stalk comparison in step 1. All existing
proof dependencies remain: the source proof uses the same four-step argument.
No target statement or definition is changed.

## Old

The module was absent from lean/; its preserved quarantine signature is:

```lean
theorem relativelyFlat_derivedBaseChange_complex
    {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (g : T ⟶ S)
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [@MonoidalPreadditive _ _ _ (SheafOfModules.monoidalCategory X.sheaf)]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (G.X i))
    (hqc : ∀ i : ℤ, (G.X i).IsQuasicoherent)
    (hflat : ∀ i : ℤ, Scheme.Modules.IsFlatOver (G.X i) f)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) P)
    (e : DerivedCategory.Q.obj P ≅ E)
    (α : E ⊗ DerivedCategory.Q.obj G ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P G
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) :
    IsIso ((derivedPullback g).map ((schemeDerivedDirectImage f).map α.hom) ≫
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P G
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map
        ((SingleComplexBaseChange.counit (pullback.fst f g)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj (CochainComplex.mapBifunctor P G
            (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf))))))
```

## New

The theorem is re-exported from the adopted source with this signature:

```lean
theorem relativelyFlat_derivedBaseChange_complex
    {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (g : T ⟶ S)
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [@MonoidalPreadditive _ _ _ (SheafOfModules.monoidalCategory X.sheaf)]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (G.X i))
    (hqc : ∀ i : ℤ, (G.X i).IsQuasicoherent)
    (hflat : ∀ i : ℤ, Scheme.Modules.IsFlatOver (G.X i) f)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (e : DerivedCategory.Q.obj P ≅ E)
    (α : E ⊗ DerivedCategory.Q.obj G ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P G
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) :
    IsIso ((derivedPullback g).map ((schemeDerivedDirectImage f).map α.hom) ≫
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P G
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map
        ((SingleComplexBaseChange.counit (pullback.fst f g)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj (CochainComplex.mapBifunctor P G
            (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf))))))
```

The restored module publicly imports the source theorem module and
Sheaf.Algebra.Homology.KFlat, and adds no declaration. The old public imports of
DerivedCategory, SchemeDerivedDirectImage, DerivedTensorStructure,
SchemeDerivedBaseChangeMap, the two morphism-property modules and
Cohomology.DirectImage remain public through the source theorem module. The three
old public Sheaf imports (DerivedPullback, DerivedPullbackTensorProduct and
SingleComplexBaseChangeStalkCondition) are now empty withdrawn modules; their actual
source counterparts are public imports of the source theorem module. The source
proof's four private dependency imports stay in that source module.

## Users

`tools/downstream.py` with --allow-missing and --uses reports zero live downstream
modules and zero live uses through the absent Sheaf path. Separate searches in lean/,
quarantine/Sheaf and dag/nodes identify the archived direct consumer and the existing
source consumers below. No archived consumer uses this item's private helpers via
import all. No consumer file is changed in this packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | A4 | Restore import path and re-export the existing theorem. |
| Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | quarantined; not adapted | Same theorem name and full archived signature; its parent dependency remains. |
| WeilConjectures.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | not adapted | Already imports the adopted source theorem; no change. |
| WeilConjectures.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta | not adapted | Already imports the adopted source theorem; no change. |
| WeilConjectures | not adapted | Already publicly imports the source theorem module; no change. |

The parent node lem-pc-relatively-flat-tensor-base-change-iso continues to cite
lem-pc-rf-base-change-complex. No parent dependency is removed. The quarantined
consumer has its own rework assignment and is not claimed to be repaired here.
No forced adaptations are included.

## Status

landed 20261022T021024-L-162401 2026-10-22 (merge of deliver/A4/Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex)
