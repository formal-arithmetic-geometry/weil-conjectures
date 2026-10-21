# AlgebraicGeometry.perfect_generator_pullback_compat

## Reason

Restore the quarantined assigned module after the upstream synchronization. The archived
file fails compilation: its public signature cannot see `derivedPullback`, because
`Sheaf.AlgebraicGeometry.DerivedPullback` is now withdrawn. Importing the adopted
source supplies that definition; the adopted generator theorem also already owns the
name `AlgebraicGeometry.perfect_generator_pullback` and has a stronger conclusion.

Publicly re-export the adopted theorem and provide the original signature under the
new name `AlgebraicGeometry.perfect_generator_pullback_compat`. This preserves the
original mathematical assertion without colliding with the source declaration.
The adopted theorem has an additional family of localizations on opens of X'; the
proved theorem `nonempty_derivedOpenLocalization` supplies it from the existing
ambient localization hypothesis. Project away the adopted theorem's additional
perfectness conclusion. No mathematical hypothesis is added or removed.

The DAG attachment names the compatibility theorem; its module, file, statement,
statement dependencies and unit realization are preserved. Its Lean signature record
changes only the declaration name. The proof retains its existing mathematical
inputs, now used by the adopted source proof, and records the two additional inputs
for the compatibility argument: preservation of perfectness and open localization.
The quarantine archive is preserved and no deleted.txt is supplied.

## Old

```lean
theorem perfect_generator_pullback {X X' : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X'.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (g : X' ⟶ X) [IsAffineHom g] (M : schemeDerivedQCohCategory X)
    (hperfect : Scheme.IsPerfect X M.obj)
    (hgen : ∀ E : schemeDerivedQCohCategory X,
      IsZero E.obj ↔ ∀ n : ℤ, Subsingleton (M.obj⟦n⟧ ⟶ E.obj)) :
    schemeDerivedQCohProperty X' ((derivedPullback g).obj M.obj) ∧
      ∀ E : schemeDerivedQCohCategory X',
        IsZero E.obj ↔ ∀ n : ℤ,
          Subsingleton (((derivedPullback g).obj M.obj)⟦n⟧ ⟶ E.obj)
```

The archived public imports were `Sheaf.AlgebraicGeometry.DerivedPullback`,
`WeilConjectures.AlgebraicGeometry.PerfectComplex`, and
`Mathlib.AlgebraicGeometry.Morphisms.Affine`.

## New

Publicly re-export `WeilConjectures.AlgebraicGeometry.PerfectGeneratorPullback`.
It exports all three canonical statement dependencies. Privately import
`WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization` for the proof.
The adopted source declaration remains verbatim, including all its imports.
Add the following exact-signature compatibility statement with a complete proof:

```lean
theorem perfect_generator_pullback_compat {X X' : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X'.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (g : X' ⟶ X) [IsAffineHom g] (M : schemeDerivedQCohCategory X)
    (hperfect : Scheme.IsPerfect X M.obj)
    (hgen : ∀ E : schemeDerivedQCohCategory X,
      IsZero E.obj ↔ ∀ n : ℤ, Subsingleton (M.obj⟦n⟧ ⟶ E.obj)) :
    schemeDerivedQCohProperty X' ((derivedPullback g).obj M.obj) ∧
      ∀ E : schemeDerivedQCohCategory X',
        IsZero E.obj ↔ ∀ n : ℤ,
          Subsingleton (((derivedPullback g).obj M.obj)⟦n⟧ ⟶ E.obj)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectGeneratorPullback | Z5 (assigned rework) | Restored interface with the canonical stronger theorem and a proved compatibility statement; zero holes. |
| WeilConjectures.AlgebraicGeometry.AffinePullbackPerfectDetectsIso | unclaimed in repository | Sole DAG parent and sole code caller of the old name. Already imports the adopted source and obtains its three conjuncts. No adaptation or signature change. |
| WeilConjectures.AlgebraicGeometry.SupportedPerfectGenerator | unclaimed in repository | Docstring reference only; no adaptation. |

`tools/downstream.py Sheaf.AlgebraicGeometry.PerfectGeneratorPullback --uses
perfect_generator_pullback` reports unknown module because it is quarantined.
Searching both lean/ and quarantine/ finds no direct importers of the Sheaf module;
the only theorem call is the source parent above. Searching every node's stmt_deps,
proof_deps and proof-step uses finds exactly that DAG parent. Its dependencies stay.
The unit `sk-thm-picard-duality` and every target statement remain unchanged.
A server-compiled probe imports the restored interface together with the source
consumer and checks the adopted, compatibility and consumer declarations together.
Another probe checks the exact archived assertion. Both generator theorems use only
propext, Classical.choice and Quot.sound. No definition, data construction or
source-library file is changed.

## Status

landed 20261021T174258-L-3778996 2026-10-21 (merge of deliver/Z5/Sheaf.AlgebraicGeometry.PerfectGeneratorPullback)

2026-10-22: renewed server compilation and import-cycle checks for return C-8879e.
The reviewed restoration and zero-hole proof are retained; `deliver3.py` rebuilds the
packet on current `sheaf-dag`. The unrelated quarantined module named in the previous
landing failure is not part of this packet and is neither edited nor withdrawn.
