# AlgebraicGeometry.relativelyFlat_tensor_baseChange_iso

## Reason

Restore the quarantined module assigned in coord/rework.tsv. The archive is preserved.
The unchanged archive fails to compile: CochainComplex.isKFlat_pullback is unknown,
and the public statement cannot access derivedPullback or Scheme.Modules.tensorPullback.
Its old Sheaf imports DerivedPullback, SingleComplexBaseChangeStalkCondition,
DerivedPullbackTensorProduct and KFlatPullback are withdrawn empty modules.

The adopted source module already proves the exact archived theorem. Restore the
historical Sheaf import path as a public compatibility re-export of that source module.
This supplies the existing proof and its public statement dependencies together, without
redeclaring the theorem or restoring the incompatible duplicate dependency cluster.
Import-direction checking permits this import. No source-library file is changed.

The archived and source theorem signatures are textually identical. A separate consumer
reproduces the entire archived signature and applies the adopted theorem with every
original argument. The ordinary termwise pullback of G, arbitrary unbounded E, universe
parameters, both derived-category assumptions, and all morphism hypotheses stay intact.
No extra flatness of g, properness, nonemptiness, or absolute K-flatness of G is imposed.
The source proof uses the same K-flat model, relatively flat base-change comparison,
termwise tensor comparison and K-flat pullback counit as the five existing DAG steps.
All proof dependencies and parent dependencies remain; the node's Lean attachment now
names the actual source declaration. No target statement or definition changes.

## Old

The module is absent from lean/. Its preserved quarantine signature is:

```lean
theorem relativelyFlat_tensor_baseChange_iso
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (g : T ⟶ S) (E : schemeDerivedCategory X)
    (hE : schemeDerivedQCohProperty X E) (G : CochainComplex X.Modules ℤ)
    (hGb : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (G.X n))
    (hGqc : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hGflat : ∀ n : ℤ, (G.X n).IsFlatOver f) :
    Nonempty ((derivedPullback g).obj
        ((schemeDerivedDirectImage f).obj (E ⊗ DerivedCategory.Q.obj G)) ≅
      (schemeDerivedDirectImage (pullback.snd f g)).obj
        ((derivedPullback (pullback.fst f g)).obj E ⊗
          DerivedCategory.Q.obj
            (((Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomologicalComplex
              (.up ℤ)).obj G)))
```

## New

The restored module publicly imports
WeilConjectures.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso, which exports
this identical theorem signature:

```lean
theorem relativelyFlat_tensor_baseChange_iso
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (g : T ⟶ S) (E : schemeDerivedCategory X)
    (hE : schemeDerivedQCohProperty X E) (G : CochainComplex X.Modules ℤ)
    (hGb : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (G.X n))
    (hGqc : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hGflat : ∀ n : ℤ, (G.X n).IsFlatOver f) :
    Nonempty ((derivedPullback g).obj
        ((schemeDerivedDirectImage f).obj (E ⊗ DerivedCategory.Q.obj G)) ≅
      (schemeDerivedDirectImage (pullback.snd f g)).obj
        ((derivedPullback (pullback.fst f g)).obj E ⊗
          DerivedCategory.Q.obj
            (((Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomologicalComplex
              (.up ℤ)).obj G)))
```

No new declaration is introduced. All original nonempty public statement imports are
public imports of the source theorem module. The archive's two public Sheaf paths are
empty; their source counterparts are public imports of the source theorem module.
The archive's five proof imports need not be direct imports of the compatibility shim;
the source proof retains the corresponding five source imports.

## Users

`tools/downstream.py` with --allow-missing and --uses reports zero live downstream
modules or uses through the absent Sheaf path. Searches in lean/ and quarantine/ find
the archived direct consumer below. Running downstream.py on the adopted source module
reports the three source downstream modules listed here. None requires adaptation;
no consumer uses the archived private helper through import all.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | D3 | Restore path as a public re-export. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | quarantined | Same theorem name and exact signature; its own rework remains separate. |
| WeilConjectures.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | unclaimed | Existing source declaration and complete proof unchanged. |
| WeilConjectures.AlgebraicGeometry.CartesianTensorDataComparison | unclaimed | Already imports the source theorem; unchanged. |
| WeilConjectures.AlgebraicGeometry.ProperSupportAffineTensorRestriction | unclaimed | Source downstream importer; unchanged. |
| WeilConjectures | unclaimed | Already exports the source module; unchanged. |

The DAG parents lem-pc-proper-support-perfect-direct-image and
lem-pc-cartesian-tensor-data-comparison retain this node and all their dependencies.
The unit route is unchanged. This packet restores a result; it withdraws no module.
No forced adaptations are included.

## Status

landed 20261022T032518-L-2034226 2026-10-22 (merge of deliver/D3/Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso)
