# AlgebraicGeometry.Scheme.Modules.exteriorTensor_local_pairing

## Reason

Retire the duplicate Sheaf module under the human-approved retirement policy recorded in
coord/changes/retire-sheaf-twins-20261020.md. The queue and coord/retire-items.tsv classify
this item as retire, with one consumer. The upstream theorem uses exteriorPower and wedge;
the old consumer uses exteriorSheaf and exteriorSheafSection. These are the sheafifications
of canonically isomorphic presheaves: their object modules coincide, and uniqueness of
the old restriction map identifies the two restriction maps.

## Old

The withdrawn module lean/Sheaf/AlgebraicGeometry/Modules/ExteriorTensorLocalPairing.lean
provided this theorem:

```lean
theorem exteriorTensor_local_pairing {X : Scheme.{v}} {A B C : X.Modules}
    (f : A ⟶ B) (r n s : ℕ) (hr : n = r + s) (U : X.Opens)
    (t : ∀ W : X.Opens, W ≤ U →
      C.val.obj (op W) →ₗ[X.presheaf.obj (op W)] B.val.obj (op W))
    (ht : ∀ (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) b,
      B.val.map (homOfLE hZW).op (t W hW b) =
        t Z (hZW.trans hW) (C.val.map (homOfLE hZW).op b)) :
    ∃ d : ∀ W : X.Opens, W ≤ U →
      (exteriorSheaf A r ⊗ exteriorSheaf C s).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] (exteriorSheaf B n).val.obj (op W),
      (∀ W hW (a : Fin r → A.val.obj (op W)) (b : Fin s → C.val.obj (op W)),
        d W hW (tmulSection (exteriorSheafSection A r W a)
          (exteriorSheafSection C s W b)) =
        exteriorSheafSection B n W
          (fun i ↦ Fin.append (fun j ↦ f.val.app (op W) (a j))
            (fun j ↦ t W hW (b j)) (Fin.cast hr i))) ∧
      (∀ (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) y,
        (exteriorSheaf B n).val.map (homOfLE hZW).op (d W hW y) =
          d Z (hZW.trans hW)
            ((exteriorSheaf A r ⊗ exteriorSheaf C s).val.map (homOfLE hZW).op y))
```

## New

The duplicate module is withdrawn through deleted.txt. The node points to the theorem in
WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorLocalPairing:

```lean
theorem exteriorTensor_local_pairing {X : Scheme.{v}} {A B C : X.Modules}
    (f : A ⟶ B) (r n s : ℕ) (hr : n = r + s) (U : X.Opens)
    (t : ∀ W : X.Opens, W ≤ U →
      C.val.obj (op W) →ₗ[X.presheaf.obj (op W)] B.val.obj (op W))
    (ht : ∀ (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) b,
      B.val.map (homOfLE hZW).op (t W hW b) =
        t Z (hZW.trans hW) (C.val.map (homOfLE hZW).op b)) :
    ∃ d : ∀ W : X.Opens, W ≤ U →
      (exteriorPower A r ⊗ exteriorPower C s).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] (exteriorPower B n).val.obj (op W),
      (∀ W hW (a : Fin r → A.val.obj (op W)) (b : Fin s → C.val.obj (op W)),
        d W hW (tmulSection (wedge (M := A) (r := r) (U := W) a)
          (wedge (M := C) (r := s) (U := W) b)) =
        wedge (M := B) (r := n) (U := W)
          (fun i ↦ Fin.append (fun j ↦ f.val.app (op W) (a j))
            (fun j ↦ t W hW (b j)) (Fin.cast hr i))) ∧
      (∀ (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) y,
        (exteriorPower B n).val.map (homOfLE hZW).op (d W hW y) =
          d Z (hZW.trans hW)
            ((exteriorPower A r ⊗ exteriorPower C s).val.map (homOfLE hZW).op y))
```

The sole consumer imports the upstream module. The private exteriorPresheafComparison
identifies the presheaves by uniqueness of restrictions on pure wedges. Its sheafification
exteriorComparison preserves wedge sections in both directions, by naturality of the unit.
The proved private exteriorPairing_transport composes the upstream pairing with the
tensor of the source comparison maps and the target inverse, proving the wedge formula
and naturality by equality composition. determinant_split_linear_maps_exists applies it;
its existing signature, including all old exteriorSheaf types, stays verbatim. References
to the ordinary exteriorPower namespace are qualified with _root_ to avoid the new sheaf
exteriorPower definition shadowing that namespace.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearMaps | unclaimed | Replace its private pairing import; construct the canonical comparison isomorphisms and transport the upstream theorem. No existing public signature or definition changes. |

No upstream file is edited. No target statement or definition changes. The comparison
uses uniqueness for every degree and works for degree zero, empty opens and zero rings.

## Status

landed 20261020T144301-L-2261394 2026-10-20 (merge of deliver/Q6/Sheaf.AlgebraicGeometry.Modules.ExteriorTensorLocalPairing)
