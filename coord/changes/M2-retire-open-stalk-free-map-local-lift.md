# AlgebraicGeometry.Scheme.exists_open_stalk_free_map_local_lifts

## Reason

The assigned module is listed in coord/retire-items.tsv. It contains zero holes and
has an existing source twin with a stronger canonical-comparison interface.
Withdraw only the duplicate Sheaf module and migrate its sole remaining direct consumer.
The source module and every source-library declaration, proof and import remain unchanged.

## Old

The Sheaf module existentially packages a comparison family:

```lean
theorem exists_open_stalk_free_map_local_lifts
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U) :
    ∃ e : ∀ (W : X.Opens) (hxW : x ∈ W) (hWU : W ≤ U),
      SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hWU) ⋙
        openModuleStalkFunctor X W ⟨x, hxW⟩ ≅ openModuleStalkFunctor X U ⟨x, hxU⟩,
      ∀ (m : ℕ) (N : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (t : (openModuleStalkFunctor X U ⟨x, hxU⟩).obj
          (SheafOfModules.free
            (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))) ⟶
          (openModuleStalkFunctor X U ⟨x, hxU⟩).obj N),
        ∃ (V : X.Opens) (_hxV : x ∈ V) (_hVU : V ≤ U),
          ∀ (W : X.Opens) (hxW : x ∈ W) (_hWV : W ≤ V) (hWU : W ≤ U),
            let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
              (homOfLE hWU)
            ∃ g : R.obj (SheafOfModules.free
                (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))) ⟶
                R.obj N,
              (openModuleStalkFunctor X W ⟨x, hxW⟩).map g =
                (e W hxW hWU).hom.app _ ≫ t ≫ (e W hxW hWU).inv.app N
```

## New

The node points to the already proved source theorem in
WeilConjectures.AlgebraicGeometry.OpenStalkFreeMapLocalLift:

```lean
theorem exists_open_stalk_free_map_local_lifts
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U) :
    ∀ (m : ℕ) (N : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (t : (openModuleStalkFunctor X U ⟨x, hxU⟩).obj
        (SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))) ⟶
        (openModuleStalkFunctor X U ⟨x, hxU⟩).obj N),
      ∃ (V : X.Opens) (_hxV : x ∈ V) (_hVU : V ≤ U),
        ∀ (W : X.Opens) (hxW : x ∈ W) (_hWV : W ≤ V) (hWU : W ≤ U),
          let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE hWU)
          ∃ g : R.obj (SheafOfModules.free
              (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))) ⟶
              R.obj N,
            (openModuleStalkFunctor X W ⟨x, hxW⟩).map g =
              (openModuleStalkRestrictionComparison X U W hWU x hxU hxW).hom.app _ ≫ t ≫
                (openModuleStalkRestrictionComparison X U W hWU x hxU hxW).inv.app N
```

The source theorem has identical schemes, opens, point, universe, rank, target sheaf,
stalk maps, restriction functors and neighbourhood quantifiers. It fixes the comparison
family to openModuleStalkRestrictionComparison. This explicit family is independent of
m, N and t, so choosing it proves the node's original existential assertion unchanged.
No hypothesis or conclusion of the mathematical node is changed. In particular m=0,
equal opens, arbitrary N, and non-affine U are still allowed; x in U excludes empty U.

The original source proof was read in full: one-neighbourhood lifting gives V, a, k;
restriction transport gives c and d on each W; naturality and cancellation give the
prescribed stalk formula for c.inv followed by restriction of k followed by c.hom.
The same two proof dependencies remain recorded on the node. No unit is bypassed.
The node's lean.statement is the source signature verbatim, with a note explaining
why this stronger realization proves its unchanged mathematical statement.

Withdraw lean/Sheaf/AlgebraicGeometry/OpenStalkFreeMapLocalLift.lean using deleted.txt.
In PerfectOpenStalkDegreewiseLift, change the private import to the source twin,
replace the obtain of the existential e/he pair by the explicit canonical family e
and the source theorem he. The consumer's public signature, attributes, visibility,
public imports, and the rest of its finite-support assembly proof are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.OpenStalkFreeMapLocalLift | M2 (assigned retirement) | Duplicate withdrawn; node attached to existing stronger source theorem. |
| Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseLift | unclaimed | Sole direct importer; private import and comparison-family proof glue adapted. |
| Sheaf.AlgebraicGeometry.PerfectOpenStalkChainMapLift | unclaimed | Indirect importer; unchanged consumer interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectOpenStalkDerivedHomDescent | unclaimed | Indirect importer; unchanged consumer interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift | unclaimed | Indirect importer; unchanged consumer interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectStalkQuasiIsoDetection | unclaimed | Indirect importer; unchanged consumer interface, no adaptation. |

These are the modules listed by tools/downstream.py with --uses for the declaration,
plus the withdrawn item. The actual declaration caller outside the item is only
PerfectOpenStalkDegreewiseLift. The inventory's FiniteProjectiveOpenStalkMapsLift
Sheaf consumer is already absent; its live source counterpart imports the source twin.
No live or quarantined module besides the adapted consumer imports the withdrawn module.
DAG parents keep the same mathematical dependency, now realized by the source theorem.
All downstream theorem statements and target meanings stay unchanged.

An import-only migration was compiled and failed at original line 69:
`Tactic rcases failed ... is not an inductive datatype`, because the source theorem
starts with forall m N t rather than an existential comparison package. The three
replacement proof lines supply exactly that missing family. The adapted file compiles
with lcompile.py in 5.0 seconds, with no warning. No other module needs adaptation.
No proof or data construction was replaced by a hole, and no new declaration was added.

## Status

landed 20261020T160758-L-3407501 2026-10-20 (merge of deliver/M2/Sheaf.AlgebraicGeometry.OpenStalkFreeMapLocalLift)
