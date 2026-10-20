# AlgebraicGeometry.Scheme.universalLowest_fiber_ranks

## Reason

Restore the quarantined module assigned by coord/rework.tsv. Its recorded failure was
an environment collision on AlgebraicGeometry.derivedPullback caused by the obsolete
Sheaf.AlgebraicGeometry.DerivedPullbackComposition proof import. That module was
retired by the B2 source-construction migration; the node for the composition theorem
now points to WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition.

After redirecting this import, the compiler reported a universe constraint u + 1 = u
at the zero-global-sections step (line 166). Pin evaluation and scalar restriction to
the coefficient universe u already used by derivedFiberCohomology. This prevents
instance inference from selecting an incompatible AddCommGrpCat universe.

## Old

The source is preserved at
quarantine/Sheaf/AlgebraicGeometry/UniversalLowestFiberRanks.lean.
The theorem signature, reproduced here, is unchanged by this repair:

```lean
theorem universalLowest_fiber_ranks
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (S : Scheme.{u})
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (E : schemeDerivedCategory S) (hE : IsPerfect S E) (a b : ℤ)
    (hamp : ∀ F : SheafOfModules.{u} (moduleRings S.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes S E F i)
    (r : ℕ) (T : Scheme.{u}) (h : T ⟶ S)
    (hres : ∀ t : T,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (T.residueField t)).toRingedSpace)) a).obj
            ((derivedPullback (T.fromSpecResidueField t ≫ h)).obj E)) r) :
    ∀ t : T, (∀ i : ℤ, i < a → derivedFiberBetti S E i (h t) = 0) ∧
      derivedFiberBetti S E a (h t) = r
```

The old proof import was:

```lean
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
```

The old zero-object transport used:

```lean
      (ModuleCat.restrictScalars (ΓSpecIso (S.residueField (h t))).inv.hom).map_isZero
        ((SheafOfModules.evaluation
```

## New

Restore the same theorem signature above and its complete archived proof, with:

```lean
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
```

and the explicit universe annotations:

```lean
      (ModuleCat.restrictScalars.{u, u, u} (ΓSpecIso (S.residueField (h t))).inv.hom).map_isZero
        ((SheafOfModules.evaluation.{u}
```

All public imports, signatures, declaration names, attributes, options and docstrings
remain identical to the archive. No definition changes; no target meaning changes.
There were zero direct sorry holes in the archive and there are zero in the restoration.
The lcompile.py check passed in 17.8 seconds with no warnings.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.UniversalLowestFiberRanks | T3 | Restore and repair the proof import and universe inference. |
| Sheaf.AlgebraicGeometry.PerfectUniversalLowestZeroModel | unclaimed; quarantined | Existing invocation and signature remain valid; no adaptation forced. |

The downstream.py command reports unknown module because the assigned source is
quarantined. A search of lean/ and quarantine/ finds exactly the parent above, which
calls universalLowest_fiber_ranks with the unchanged arguments and uses both returned
rank clauses. That parent also retains obsolete pullback imports; these are its own
recorded rework issues, not caused by this restoration. It is not changed here.
No live Lean consumer needs adaptation. The existing DAG node
lem-sc-universal-lowest-fiber-ranks, its Lean attachment, and all its statement and
proof dependencies are preserved. The proof uses every declared proof dependency.
The unit route is unchanged; the archived source is not withdrawn or overwritten.

## Status

landed 20261020T174854-L-813377 2026-10-20 (merge of deliver/T3/Sheaf.AlgebraicGeometry.UniversalLowestFiberRanks)
