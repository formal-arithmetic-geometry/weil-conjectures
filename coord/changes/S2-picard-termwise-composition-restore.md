# AlgebraicGeometry.Scheme.picardTermwiseSingleMap_composition

## Reason

Restore the quarantined module while repairing its compatibility with the current
`irreducible_def derivedPullback`. The previous local irreducibility attribute is now
rejected. Reuse the existing, proved fixed-counit API to avoid repeated kernel checking of
large existential witness predicates. This changes only proof code, private helpers, and
local proof commands. Public imports, signatures, definitions and target meanings are
unchanged; no target semantic review is reopened.

## Old

The public theorem signature is:

```lean
theorem picardTermwiseSingleMap_composition
    {W T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
    (ht : i ≫ t = t') (M : W.Modules) :
    let : (Modules.tensorPullback i).Additive :=
      (Classical.choose (Modules.exists_tensorPullbackAdjunction i)).left_adjoint_additive
    let u := (CochainComplex.singleFunctor
      (SheafOfModules.{v} (moduleRings T'.toRingedSpace)) 0).mapIso
        ((Modules.tensorPullbackCompositionIso i t t' ht).app M) ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (Modules.tensorPullback i) (.up ℤ) 0).app ((Modules.tensorPullback t).obj M)).symm
    let c := (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) i t ≪≫
        eqToIso (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)
    c.hom.app ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj M) ≫
        picardTermwiseSingleMap t' M ≫ DerivedCategory.Q.map u.hom =
      (derivedPullback i).map (picardTermwiseSingleMap t M) ≫
        (picardTermwiseCounit i).app ((CochainComplex.singleFunctor
          (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj
            ((Modules.tensorPullback t).obj M))
```

The archive locally declares `derivedPullback` irreducible and constructs private aliases
`pinnedCounit` and `pinnedComposition` by repeating the nested choices from
`exists_derivedPullbackComposition`. Its private `counit_composition` proves the generic
left-derived factorization directly.

## New

The public theorem signature is identical:

```lean
theorem picardTermwiseSingleMap_composition
    {W T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
    (ht : i ≫ t = t') (M : W.Modules) :
    let : (Modules.tensorPullback i).Additive :=
      (Classical.choose (Modules.exists_tensorPullbackAdjunction i)).left_adjoint_additive
    let u := (CochainComplex.singleFunctor
      (SheafOfModules.{v} (moduleRings T'.toRingedSpace)) 0).mapIso
        ((Modules.tensorPullbackCompositionIso i t t' ht).app M) ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (Modules.tensorPullback i) (.up ℤ) 0).app ((Modules.tensorPullback t).obj M)).symm
    let c := (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) i t ≪≫
        eqToIso (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)
    c.hom.app ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj M) ≫
        picardTermwiseSingleMap t' M ≫ DerivedCategory.Q.map u.hom =
      (derivedPullback i).map (picardTermwiseSingleMap t M) ≫
        (picardTermwiseCounit i).app ((CochainComplex.singleFunctor
          (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj
            ((Modules.tensorPullback t).obj M))
```

Remove only `derivedPullback` from the existing local irreducibility command. A proof-only
import supplies `perfectHomTensorCounit_comp`, `perfectHomTensorCounit`,
`perfectHomComposition`, and the fixed tensor-comparison definitions and equations.
They name the exact old choices. The three duplicate private helpers are removed.
All remaining private helpers are fully proved. The public `picardTermwiseSingleMap`
definition body and both public imports remain verbatim.

## Users

`tools/downstream.py` reports the item as unknown because it is currently quarantined.
Source searches find the following direct archived importers. Their public declarations
and the underlying public map construction are unchanged, so no adaptation is required.
No other module is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardTermwiseSingleMapComposition | S2 | Restored and repaired proof only. |
| Sheaf.AlgebraicGeometry.PicardTermwiseSourceCoherence | unclaimed | Same signature and map definition; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap | unclaimed | Same signature and map definition; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleOpenTensorCoefficientCoherence | unclaimed | Same signature and map definition; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenSingleCoefficientTransport | unclaimed | Same signature and map definition; no adaptation. |

All further users likewise see the original public interface.

## Status

landed 20261020T235624-L-1196993 2026-10-20 (merge of deliver/S2/Sheaf.AlgebraicGeometry.PicardTermwiseSingleMapComposition)

The theorem-scoped `cleanup.letToHave false` retains shared local comparison data,
avoiding repeated optional cleanup traversal of nested choices. Kernel checking and
delivery checks remain enabled. The repaired source compiled in 46.6 seconds.
