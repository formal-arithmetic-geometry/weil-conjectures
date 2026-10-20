# AlgebraicGeometry.Scheme.exists_openStalk_restriction_transport

## Reason

The assigned queue row is a retirement item. The Sheaf copy has no holes and duplicates
an upstream theorem with a stronger, canonical-comparison API. Keep the source theorem
and migrate the only remaining direct Sheaf importer.

## Old

In Sheaf.AlgebraicGeometry.OpenStalkRestrictionTransport:

```lean
theorem exists_openStalk_restriction_transport
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U) :
    ∃ e : ∀ (W : X.Opens) (hxW : x ∈ W) (hWU : W ≤ U),
      SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hWU) ⋙
        openModuleStalkFunctor X W ⟨x, hxW⟩ ≅ openModuleStalkFunctor X U ⟨x, hxU⟩,
      ∀ (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U)
        (a : SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hVU) ⋙
          openModuleStalkFunctor X V ⟨x, hxV⟩ ≅ openModuleStalkFunctor X U ⟨x, hxU⟩)
        (W : X.Opens) (hxW : x ∈ W) (hWV : W ≤ V) (hWU : W ≤ U),
        let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hVU)
        let Q := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hWV)
        let P := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hWU)
        ∃ (c : R ⋙ Q ≅ P)
          (d : Q ⋙ openModuleStalkFunctor X W ⟨x, hxW⟩ ≅
            openModuleStalkFunctor X V ⟨x, hxV⟩),
          ∀ M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U),
            (openModuleStalkFunctor X W ⟨x, hxW⟩).map (c.hom.app M) ≫
                (e W hxW hWU).hom.app M =
              d.hom.app (R.obj M) ≫ a.hom.app M
```

## New

The node points to the existing theorem in
WeilConjectures.AlgebraicGeometry.OpenStalkRestrictionTransport:

```lean
theorem exists_openStalk_restriction_transport
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U) :
    ∀ (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U)
      (a : SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hVU) ⋙
        openModuleStalkFunctor X V ⟨x, hxV⟩ ≅ openModuleStalkFunctor X U ⟨x, hxU⟩)
      (W : X.Opens) (hxW : x ∈ W) (hWV : W ≤ V) (hWU : W ≤ U),
      let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU)
      let Q := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWV)
      let P := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU)
      ∃ (c : R ⋙ Q ≅ P)
        (d : Q ⋙ openModuleStalkFunctor X W ⟨x, hxW⟩ ≅
          openModuleStalkFunctor X V ⟨x, hxV⟩),
        (∀ M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U),
          c.hom.app M = 𝟙 _) ∧
        ∀ M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U),
          (openModuleStalkFunctor X W ⟨x, hxW⟩).map (c.hom.app M) ≫
              (openModuleStalkRestrictionComparison X U W hWU x hxU hxW).hom.app M =
            d.hom.app (R.obj M) ≫ a.hom.app M
```

The source uses exactly the same schemes, opens, point, universes, scalar rings,
restriction functors and arbitrary comparison a. It fixes e_W to the explicitly
constructed openModuleStalkRestrictionComparison and adds the identity-component
property of c. Thus the old existential assertion follows by choosing this family
before any module or map and forgetting the extra property. Equal opens remain allowed.
The consumer still proves its original existential statement, with unchanged binders.

Withdraw the Sheaf copy via deleted.txt. In OpenStalkFreeMapLocalLift replace its
private import by the source twin, supply the canonical comparison family explicitly,
and unpack the source's additional conjunction. Its private categorical calculation,
public signature, attributes and public imports stay unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.OpenStalkFreeMapLocalLift | unclaimed | Only direct importer; private import and comparison-family proof glue adapted. |
| Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseLift | unclaimed | Indirect importer; local-lift interface unchanged. |
| Sheaf.AlgebraicGeometry.PerfectOpenStalkChainMapLift | unclaimed | Indirect importer; local-lift interface unchanged. |
| Sheaf.AlgebraicGeometry.PerfectOpenStalkDerivedHomDescent | unclaimed | Indirect importer; local-lift interface unchanged. |
| Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift | unclaimed | Indirect importer; local-lift interface unchanged. |
| Sheaf.AlgebraicGeometry.PerfectStalkQuasiIsoDetection | unclaimed | Indirect importer; local-lift interface unchanged. |

The retirement inventory's second consumer, OpenStalkFreeMapOneLift, is already
retired: its current source counterpart imports the source transport theorem.
No live or quarantined Lean module besides the listed direct importer imports the
withdrawn module. DAG parents continue to cite the same node, whose Lean attachment
now names the source theorem; no node or mathematical dependency is withdrawn.
No WeilConjectures file or Challenge statement changes.

## Status

landed 20261020T151229-L-2650899 2026-10-20 (merge of deliver/S2/Sheaf.AlgebraicGeometry.OpenStalkRestrictionTransport)
