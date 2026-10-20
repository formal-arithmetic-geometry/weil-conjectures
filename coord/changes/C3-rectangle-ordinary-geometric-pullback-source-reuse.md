# AlgebraicGeometry.rectangle_ordinary_geometric_pullback

## Reason

The rework archive imports the withdrawn Sheaf derived-pullback-composition copy.
B5 already restored and proved the Sheaf theorem, but the adopted source library now
also contains the exact same public theorem. Keeping two modules that declare this
same name risks a duplicate-declaration import error. Reuse the fully proved source
attachment and withdraw only the redundant Sheaf module.

The upstream and current Sheaf theorem signatures are byte-for-byte identical, as
is the existing node's `lean.statement`. A Lean check applying the upstream theorem
to the entire unchanged Sheaf signature compiled. `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound` for the upstream theorem.

The node retains its statement, statement dependencies, proof steps, and proof
dependencies. Only its Lean attachment and proof provenance change. This is a
replacement by an existing complete proof, not a deletion of the mathematics or
a weakening of a target. The source library is unchanged. The quarantine archive
is preserved.

## Old

Module: `Sheaf.AlgebraicGeometry.RectangleOrdinaryGeometricPullback`.

```lean
theorem rectangle_ordinary_geometric_pullback
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S T : Scheme.{u}}
    (f : X ⟶ Y) (g : S ⟶ Y) (h : T ⟶ S)
    (k : pullback (pullback.snd f g) h ⟶ pullback f (h ≫ g))
    (hk₁ : k ≫ pullback.fst f (h ≫ g) =
      pullback.fst (pullback.snd f g) h ≫ pullback.fst f g)
    (hk₂ : k ≫ pullback.snd f (h ≫ g) = pullback.snd (pullback.snd f g) h) :
    let U := qcPullback (pullback.fst f (h ≫ g))
    let L := qcPullback k
    let V := qcPullback (pullback.fst f g) ⋙
      qcPullback (pullback.fst (pullback.snd f g) h)
    ∃ (s : U ⋙ L ≅ V),
      L.IsEquivalence ∧
      (∀ E : schemeDerivedQCohCategory X,
        (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.map
            (s.hom.app E) =
          (let comp := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
            (Classical.choose_spec exists_derivedPullbackComposition)))
           (comp k (pullback.fst f (h ≫ g))).hom.app E.obj ≫
             eqToHom (congrArg (fun v ↦ (derivedPullback v).obj E.obj) hk₁) ≫
             (comp (pullback.fst (pullback.snd f g) h)
               (pullback.fst f g)).inv.app E.obj))
```

## New

The Sheaf module is withdrawn via `deleted.txt`. The delivery tool leaves a module
stub with no declarations. The existing node is attached to
`WeilConjectures.AlgebraicGeometry.RectangleOrdinaryGeometricPullback`, which already
contains this exact declaration:

```lean
theorem rectangle_ordinary_geometric_pullback
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S T : Scheme.{u}}
    (f : X ⟶ Y) (g : S ⟶ Y) (h : T ⟶ S)
    (k : pullback (pullback.snd f g) h ⟶ pullback f (h ≫ g))
    (hk₁ : k ≫ pullback.fst f (h ≫ g) =
      pullback.fst (pullback.snd f g) h ≫ pullback.fst f g)
    (hk₂ : k ≫ pullback.snd f (h ≫ g) = pullback.snd (pullback.snd f g) h) :
    let U := qcPullback (pullback.fst f (h ≫ g))
    let L := qcPullback k
    let V := qcPullback (pullback.fst f g) ⋙
      qcPullback (pullback.fst (pullback.snd f g) h)
    ∃ (s : U ⋙ L ≅ V),
      L.IsEquivalence ∧
      (∀ E : schemeDerivedQCohCategory X,
        (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.map
            (s.hom.app E) =
          (let comp := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
            (Classical.choose_spec exists_derivedPullbackComposition)))
           (comp k (pullback.fst f (h ≫ g))).hom.app E.obj ≫
             eqToHom (congrArg (fun v ↦ (derivedPullback v).obj E.obj) hk₁) ≫
             (comp (pullback.fst (pullback.snd f g) h)
               (pullback.fst f g)).inv.app E.obj))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| (none importing the Sheaf copy) | — | `tools/downstream.py` finds zero downstream modules; a full textual scan of live and quarantined Lean sources finds no import of the Sheaf module. |
| WeilConjectures.AlgebraicGeometry.RectangleOrdinaryGeometricComparisons | unchanged; not adapted | The sole mathematical DAG parent already imports the upstream module and applies the same theorem at line 96. Its statement and proof remain valid without adaptation. |

The only direct mathematical DAG parent is
`lem-sc-rectangle-ordinary-geometric-comparisons`, whose existing Lean attachment is
`WeilConjectures.AlgebraicGeometry.RectangleOrdinaryGeometricComparisons`.
Its step 1 and `proof_deps` keep `lem-sc-rectangle-ordinary-geometric-pullback`, now
reattached to the upstream proof. No other node cites the item in `stmt_deps`,
`proof_deps`, or a proof step's `uses`. No unit's `realized` field directly attaches
this node. The unit and chapter routes are therefore preserved.

No quarantined consumer imports the withdrawn Sheaf module. The historical
quarantine copy of the item is archival, remains in place, and is superseded by the
source attachment rather than restored as another duplicate declaration.

## Status

landed 20261020T221102-L-4142143 2026-10-20 (merge of deliver/C3/Sheaf.AlgebraicGeometry.RectangleOrdinaryGeometricPullback)
