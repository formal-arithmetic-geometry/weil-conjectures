# AlgebraicGeometry.rhom_supported_quasiCoherent_support_part

## Reason

Retire the duplicate Sheaf module under the human's 2026-10-20 retirement instruction
and its row in coord/retire-items.tsv. The assigned item already has zero holes.
The adopted upstream theorem proves the same support-preservation result by the same
zero-complex and open-restriction argument. The upstream signature only makes the
universe of SheafOfModules.overFunctor explicit; the old signature infers that universe
from the sheaf of rings on X. No definition, hypothesis, conclusion or target changes.

## Old

Module: Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentSupportPart.

```lean
theorem rhom_supported_quasiCoherent_support_part
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L : schemeDerivedCategory X)
    (T : Set X) (hT : IsClosed T)
    (hzero : ∀ n : ℤ,
      IsZero ((SheafOfModules.overFunctor (moduleRings X.toRingedSpace)
        ⟨Tᶜ, hT.isOpen_compl⟩).obj ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj L))) :
    ∀ n : ℤ,
      IsZero ((SheafOfModules.overFunctor (moduleRings X.toRingedSpace)
        ⟨Tᶜ, hT.isOpen_compl⟩).obj ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
            ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
              X.toRingedSpace.sheaf).obj (op K, L))))
```

## New

Module: WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentSupportPart.
The existing adopted source file remains unchanged.

```lean
theorem rhom_supported_quasiCoherent_support_part
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L : schemeDerivedCategory X)
    (T : Set X) (hT : IsClosed T)
    (hzero : ∀ n : ℤ,
      IsZero ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        ⟨Tᶜ, hT.isOpen_compl⟩).obj ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj L))) :
    ∀ n : ℤ,
      IsZero ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        ⟨Tᶜ, hT.isOpen_compl⟩).obj ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
            ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
              X.toRingedSpace.sheaf).obj (op K, L))))
```

The consumer replaces its plain import of the former module with a plain import of
this upstream module. Its theorem statement and proof remain verbatim. The node's
Lean attachment follows the upstream declaration; its proof and dependencies stay.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent | unclaimed in shared snapshot | One proof import replaced; unchanged theorem compiles against upstream. |

The item itself is withdrawn using deleted.txt. No other Lean file imports the retired
module. The DAG parents still cite the same node, now attached to the upstream theorem.
No quarantined source refers to the old module in the current rework records.

## Status

landed 20261020T221308-L-4169983 2026-10-20 (merge of deliver/P8/Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentSupportPart)
