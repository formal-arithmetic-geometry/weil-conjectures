# AlgebraicGeometry.SingleComplexBaseChange.openRestricted_counit_compatibility_aux

## Reason

Retire the quarantined Sheaf copy under the human's Hand-off in
`coord/changes/retire-sheaf-twins-20261020.md`. The rework failure was the
redundant local irreducibility command for the now-irreducible
`derivedPullback`. Removing that command makes the complete quarantine text
identical to the official twin after its copyright header.

## Old

Module: `Sheaf.AlgebraicGeometry.OpenRestrictedCounitFactorizationAux`.
Source archive:
`quarantine/Sheaf/AlgebraicGeometry/OpenRestrictedCounitFactorizationAux.lean`.
The DAG node's `lean` attachment names the missing Sheaf module. Its statement:

```lean
theorem openRestricted_counit_compatibility_aux
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (derivedPullback (pullback.snd g' U.ι)).map (openRestrictionRepresentativeIso U.ι P).hom ≫
        openRestrictedCompositionMap g' U (DerivedCategory.Q.obj P) ≫
        (derivedPullback (pullback.fst g' U.ι)).map
          ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      (counit (pullback.snd g' U.ι)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (openRestrictedTensorDerivedIso g' U P).inv
```

The quarantine also contains the now-redundant proof-local command:

```lean
attribute [local irreducible] derivedPullback
```

## New

Module: `WeilConjectures.AlgebraicGeometry.OpenRestrictedCounitFactorizationAux`.
The DAG node's `lean` attachment now names the existing official declaration
at `lean/WeilConjectures/AlgebraicGeometry/OpenRestrictedCounitFactorizationAux.lean`.
Its statement is unchanged:

```lean
theorem openRestricted_counit_compatibility_aux
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (derivedPullback (pullback.snd g' U.ι)).map (openRestrictionRepresentativeIso U.ι P).hom ≫
        openRestrictedCompositionMap g' U (DerivedCategory.Q.obj P) ≫
        (derivedPullback (pullback.fst g' U.ι)).map
          ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      (counit (pullback.snd g' U.ι)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (openRestrictedTensorDerivedIso g' U P).inv
```

The official twin omits the redundant local command. Its proof and all other
declarations match the repaired quarantine source exactly. The source archive
is preserved; the final packet lists the Sheaf path in `deleted.txt`, using
the delivery tool's supported quarantined-withdrawal mode. The tool writes
the normal empty withdrawn module; no declaration is lost from the official
library. No upstream source or target statement is changed.

Fresh `lcompile.py` checks: importing the official auxiliary and printing
its theorem's axioms succeeds in 1.9 seconds; the full current official
consumer source, including its axiom check, compiles in 6.2 seconds. Both
report exactly `propext`, `Classical.choice`, and `Quot.sound`. Actual holes
are zero, with none closed or added. Additional restored-source verification
is recorded in `report.md`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OpenRestrictedCounitFactorizationAux | Q9 | Withdrawn in favor of its existing official twin. |
| Sheaf.AlgebraicGeometry.OpenRestrictedCounitFactorization | absent | No source remains to adapt; official counterpart already uses the twin. |
| WeilConjectures.AlgebraicGeometry.OpenRestrictedCounitFactorization | unchanged | Full source and axiom check freshly compiled; no edit required. |

No current Lean source, including quarantined consumers, imports the Sheaf
auxiliary. No DAG parent cites the auxiliary node; its proof dependencies,
mathematical statement, and unit route stay unchanged. Only its Lean
attachment moves to the official declaration.

## Status

landed 20261020T151228-L-2650465 2026-10-20 (merge of deliver/Q9/Sheaf.AlgebraicGeometry.OpenRestrictedCounitFactorizationAux)
