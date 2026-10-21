# AlgebraicGeometry.Scheme.picard_derived_fibre_residue_model_data restoration

## Reason

Restore the assigned quarantined module from the exact archive named by
`coord/rework.tsv`. Its archived proof has zero holes but does not compile against
the published library: the private `restrict_model_local` declaration reports
`failed to solve universe constraint ?u.117 + 1 =?= v`, trying to unify
`Category.{?u.117 + 1, v + 1} AddCommGrpCat` with
`Category.{v, v + 1} AddCommGrpCat`. The later calls consequently report an
unknown `restrict_model_local`.

Specify `SheafOfModules.overFunctor.{v}` in that helper's domain, codomain and
local functor. This fixes the coefficient-module universe without changing any
public declaration. The restored file compiles cleanly in 29.5 seconds.

Remove the unused proof import `Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel`:
the proof takes its local representatives from `IsPerfect` itself, and requires
neither finite-free residue ranks nor minimal models. Update the existing node's
proof and proof dependencies to describe this actual route. Simplify primality
of the evaluation kernel by Mathlib's `RingHom.ker_isPrime`, since evaluation has
residue-field codomain.

All public import lines and the complete public theorem signature are
byte-identical to the quarantine archive. No definition, public instance,
attribute, target signature or adopted source-library file changes. No target
statement requires a new definition review. The quarantine archive and existing
Lean attachment are preserved.

## Old

The live source is absent; its preserved source is
`quarantine/Sheaf/AlgebraicGeometry/PicardDerivedFibreResidueModelData.lean`.
The helper signature is:

```lean
private theorem restrict_model_local
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (X : Scheme.{v}) (U V : X.Opens) (h : V ≤ U)
    (E : schemeDerivedCategory X)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (e : (SheafOfModules.overFunctor
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K) :
    Nonempty ((SheafOfModules.overFunctor
      (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj
        (((SheafOfModules.overMap
          (moduleRings X.toRingedSpace) (homOfLE h)).mapHomologicalComplex (.up ℤ)).obj K))
```

Its local restriction functor is:

```lean
  let G := SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U
```

The header also has this unused proof import:

```lean
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel
```

Primality is proved by identifying the evaluation kernel with the prime of the
affine scheme associated to the marked point.

## New

Restore `lean/Sheaf/AlgebraicGeometry/PicardDerivedFibreResidueModelData.lean`,
with the helper signature:

```lean
private theorem restrict_model_local
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (X : Scheme.{v}) (U V : X.Opens) (h : V ≤ U)
    (E : schemeDerivedCategory X)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (e : (SheafOfModules.overFunctor.{v}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K) :
    Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj
        (((SheafOfModules.overMap
          (moduleRings X.toRingedSpace) (homOfLE h)).mapHomologicalComplex (.up ℤ)).obj K))
```

Use this same explicit coefficient universe in its local functor:

```lean
  let G := SheafOfModules.overFunctor.{v} (moduleRings X.toRingedSpace) U
```

Omit the unused finite-free residue-model proof import and use:

```lean
  have hp : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
```

The source and finite family of target complexes, all representing isomorphisms,
and the public theorem signature remain the archived construction.

## Users

`tools/downstream.py` with `--allow-missing --uses
picard_derived_fibre_residue_model_data` reports zero live consumers. A separate
source import scan of `lean/` and `quarantine/`, with live sources overriding
archives, finds the following 20 transitive consumers, including two direct
archived importers. Only `PicardDerivedFibreResidueBridge` calls the theorem;
`PicardDerivedFibreResidueBridgeCore` merely imports its module. Their statements
and meanings are preserved by the unchanged public signature and imports.
No consumer is adapted or restored by this delivery. Both direct archived
consumers are tested in a separate scratch sandbox: the unchanged core compiles
in 29.9 seconds and the bridge compiles with profiling in 49.2 seconds after its
first check reached 60 seconds. The profile attributes 28 seconds to kernel
checking and approximately 10 seconds to its two large theorem applications.
A final unprofiled bridge retry also reached 60 seconds, so its performance
concern remains separate from this root repair. The successful profiled check
checks the same declaration and original proof. The delivery contains no
consumer edit.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreNaturality | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridge | unclaimed in shared snapshot | Direct archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridgeCore | unclaimed in shared snapshot | Direct archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparison | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonSource | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonTargets | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison | unclaimed in shared snapshot | Transitive archived consumer; identical theorem interface and meaning; no adaptation. |

## Status

landed 20261021T225202-L-3790730 2026-10-21 (merge of deliver/N4/Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueModelData)
