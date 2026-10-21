# AlgebraicGeometry.Scheme.pseudoCoherent_jump_loci

## Reason

The rework row for `Sheaf.AlgebraicGeometry.PerfectJumpLoci` records removal of its
live source path after a cluster restore, and points to
`quarantine/Sheaf/AlgebraicGeometry/PerfectJumpLoci.lean`. Restore that complete
proved module verbatim, preserving all interfaces and the DAG attachment. This
repairs an absent source module; it changes no definition or theorem statement.

## Old

The live path `lean/Sheaf/AlgebraicGeometry/PerfectJumpLoci.lean` is absent.
The quarantined module has the following existing signature, with a complete proof:

```lean
theorem pseudoCoherent_jump_loci (X : Scheme.{uX})
    [HasDerivedCategory.{wX} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{wX} (SheafOfModules.{uX}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : IsPseudoCoherent X E) (i : ℤ) :
    (∀ (Y : Scheme.{uX})
      [HasDerivedCategory.{wX} (SheafOfModules.{uX} (moduleRings Y.toRingedSpace))]
      [∀ y : Y, HasDerivedCategory.{wX} (SheafOfModules.{uX}
        (moduleRings (Spec (Y.residueField y)).toRingedSpace))]
      (g : Y ⟶ X) (y : Y),
        derivedFiberBetti Y ((derivedPullback g).obj E) i y = derivedFiberBetti X E i (g y)) ∧
      UpperSemicontinuous (derivedFiberBetti X E i) ∧
      ∀ r : ℕ, Topology.IsLocallyConstructible {x : X | derivedFiberBetti X E i x = r}
```

## New

Restore the archived source byte for byte to the live path. Its signature remains:

```lean
theorem pseudoCoherent_jump_loci (X : Scheme.{uX})
    [HasDerivedCategory.{wX} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{wX} (SheafOfModules.{uX}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : IsPseudoCoherent X E) (i : ℤ) :
    (∀ (Y : Scheme.{uX})
      [HasDerivedCategory.{wX} (SheafOfModules.{uX} (moduleRings Y.toRingedSpace))]
      [∀ y : Y, HasDerivedCategory.{wX} (SheafOfModules.{uX}
        (moduleRings (Spec (Y.residueField y)).toRingedSpace))]
      (g : Y ⟶ X) (y : Y),
        derivedFiberBetti Y ((derivedPullback g).obj E) i y = derivedFiberBetti X E i (g y)) ∧
      UpperSemicontinuous (derivedFiberBetti X E i) ∧
      ∀ r : ℕ, Topology.IsLocallyConstructible {x : X | derivedFiberBetti X E i x = r}
```

The full proof, imports, attributes, visibility and docstrings are identical.

## Users

There are no live Lean imports of the absent module. Reading the quarantine tree
finds these two direct consumers, whose theorem applications retain exactly the
same signature. They are not modified by this restoration. DAG parents and the
unit record remain unchanged. No target meaning is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectJumpLoci | J2 | Restore the proved archived module. |
| Sheaf.AlgebraicGeometry.PerfectLowestRankBoundOpen | quarantined | Same theorem and conclusions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | quarantined | Same theorem and conclusions; no adaptation. |

The three current local-model and base-change dependency sources carried in the
sandbox are unchanged compile inputs, not adaptations or interface changes.

## Status

landed 20261021T002143-L-1492422 2026-10-21 (merge of deliver/J2/Sheaf.AlgebraicGeometry.PerfectJumpLoci)
