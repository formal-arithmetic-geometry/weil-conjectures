# AlgebraicGeometry.exterior_dual_local_frames

## Reason

Retire the duplicate Sheaf module as assigned by coord/retire-items.tsv.
The official theorem is fully proved, but its exterior constructions are named
exteriorPower and wedge. The one remaining consumer retains its existing statement
in terms of exteriorSheaf and exteriorSheafSection. Transport the official theorem
through the proved equality of the two exterior presheaves, then keep its existing
coordinate determinant argument. No upstream file, definition, or target changes.

## Old

In Sheaf.AlgebraicGeometry.DeterminantDualLocalFrames:

```lean
theorem exterior_dual_local_frames (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (U : X.Opens) (r : ℕ)
    (e : M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r)))
    (V : X.Opens) (g : V ⟶ U) :
    ∃ (a : Module.Basis (Fin r) (X.presheaf.obj (op V)) (M.val.obj (op V)))
      (φ : Fin r → (Scheme.Modules.dual M).val.obj (op V))
      (b : Module.Basis (Set.powersetCard (Fin r) n) (X.presheaf.obj (op V))
        ((Scheme.Modules.exteriorSheaf (Scheme.Modules.dual M) n).val.obj (op V)))
      (d : Module.Basis (Set.powersetCard (Fin r) n) (X.presheaf.obj (op V))
        ((Scheme.Modules.exteriorSheaf M n).val.obj (op V)))
      (c : (Scheme.Modules.dual (Scheme.Modules.exteriorSheaf M n)).val.obj (op V) ≃ₗ[
        X.presheaf.obj (op V)] Module.Dual (X.presheaf.obj (op V))
          ((Scheme.Modules.exteriorSheaf M n).val.obj (op V))),
      (∀ (j : Fin r) (x : M.val.obj (op V)),
        (φ j).app (op (Over.mk (𝟙 V))) x = a.coord j x) ∧
      (∀ s, b s = Scheme.Modules.exteriorSheafSection (Scheme.Modules.dual M) n V
        (φ ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) ∧
      (∀ s, d s = Scheme.Modules.exteriorSheafSection M n V
        (a ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) ∧
      (∀ (ψ : (Scheme.Modules.dual (Scheme.Modules.exteriorSheaf M n)).val.obj (op V))
        (x : (Scheme.Modules.exteriorSheaf M n).val.obj (op V)),
        c ψ x = ψ.app (op (Over.mk (𝟙 V))) x)
```

## New

The copy is withdrawn using deleted.txt. The node points to the existing official
theorem in WeilConjectures.AlgebraicGeometry.DeterminantDualLocalFrames:

```lean
theorem exterior_dual_local_frames (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (U : X.Opens) (r : ℕ)
    (e : M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r)))
    (V : X.Opens) (g : V ⟶ U) :
    ∃ (a : Module.Basis (Fin r) (X.presheaf.obj (op V)) (M.val.obj (op V)))
      (φ : Fin r → (Scheme.Modules.dual M).val.obj (op V))
      (b : Module.Basis (Set.powersetCard (Fin r) n) (X.presheaf.obj (op V))
        ((Scheme.Modules.exteriorPower (Scheme.Modules.dual M) n).val.obj (op V)))
      (d : Module.Basis (Set.powersetCard (Fin r) n) (X.presheaf.obj (op V))
        ((Scheme.Modules.exteriorPower M n).val.obj (op V)))
      (c : (Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val.obj (op V) ≃ₗ[
        X.presheaf.obj (op V)] Module.Dual (X.presheaf.obj (op V))
          ((Scheme.Modules.exteriorPower M n).val.obj (op V))),
      (∀ (j : Fin r) (x : M.val.obj (op V)),
        (φ j).app (op (Over.mk (𝟙 V))) x = a.coord j x) ∧
      (∀ s, b s = wedge (M := (Scheme.Modules.dual M)) (r := n) (U := V)
        (φ ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) ∧
      (∀ s, d s = wedge (M := M) (r := n) (U := V)
        (a ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) ∧
      (∀ (ψ : (Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val.obj (op V))
        (x : (Scheme.Modules.exteriorPower M n).val.obj (op V)),
        c ψ x = ψ.app (op (Over.mk (𝟙 V))) x)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DeterminantDualLocalFrames | U4 assignment | Withdraw the duplicate module and attach its node to the official theorem. |
| Sheaf.AlgebraicGeometry.DeterminantDualPairingLocal | unclaimed | Replace the private frame import by the official module and the proved presheaf equality; transport its existential frame data, retaining the signature and determinant proof. |

The downstream.py direct-import and declaration-use scans list this consumer only
(apart from the item itself). Its public imports, statement, and visibility stay
unchanged. Equality of the actual presheaves identifies their sheafifications and
wedge sections, including degree zero, degree above the rank, zero rings, and empty
opens. The mathematical meaning of the statement is unchanged. There is no forced
adaptation of a held module and no definition change requiring a target rereview.
The official frame theorem itself no longer needs the two legacy comparison nodes;
the consumer needs the presheaf comparison for its compatibility transport.

## Status

landed 20261020T163316-L-3729203 2026-10-20 (merge of deliver/U4/Sheaf.AlgebraicGeometry.DeterminantDualLocalFrames)
