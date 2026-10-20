# AlgebraicGeometry.Scheme.Modules.coherentExtUniverseEquiv

## Reason

The normalized comparison proof needs the fixed module/abelian comparison's
naturality and degree-zero normalization. Applying it by unfolding the entire
common-resolution construction repeatedly exceeded the single-file compile limit.
The repair exposes proved component and naturality APIs, and represents the
underlying additive module group by the existing forgetful functor.

The module was unclaimed when this repair began. No adopted source-library file
is changed. Definitions used by targets change, so target semantic review reopens
under AGENTS.md section 4.

## Interface explanation

`coherentModuleGroup` previously used `AddCommGrpCat.of` on module cohomology's
carrier. It now applies `forget₂ (ModuleCat R) AddCommGrpCat` to the same module
cohomology object. Both have exactly the same carrier and additive group.

`coherentExtUniverseEquiv` previously composed the small presentation's
`Ext.homAddEquiv` with the inverse large presentation's `Ext.homAddEquiv`, using
one standard derived category. Its underlying equivalence is now Mathlib's
`Ext.chgUniv`. The proved `coherentExtUniverseEquiv_hom` states that it represents
the identical morphism in any derived-category presentation. Since
`Ext.homAddEquiv` is injective, this identifies the new map with the old map.
Additivity follows from the same identity. This changes the implementation, not
the represented Ext class. The proved postcomposition and sheaf-naturality APIs
preserve this identification.

`moduleAbelianCohomologyLarge` retains its original defining composite: the
component of `moduleCohomologyExtResolutionNatIso` followed by this canonical
universe change. `moduleAbelianCohomologyLarge_component` evaluates it without
unfolding the resolution, and `moduleAbelianCohomologyLarge_naturality` combines
the resolution naturality square with universe-transport naturality.

Module-sheaf binders are written `X.Modules`, the existing abbreviation for
`SheafOfModules X.ringCatSheaf`. Their types, hypotheses and universes are unchanged.
Public imports select the adopted source owner as recorded separately.
No target statement is changed.

The migration away from the duplicate Sheaf owner is recorded separately in
`qcoherent-section-comparison-component.md`.

## Old

```lean
def coherentModuleGroup (X : Scheme.{u})
    (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F)

def coherentExtUniverseEquiv {A : Type u₀} [Category.{v₀} A] [Abelian A]
    [HasExt.{v} A] [HasExt.{w} A] (M N : A) (q : ℕ) :
    Abelian.Ext.{v} M N q ≃+ Abelian.Ext.{w} M N q :=
  letI := HasDerivedCategory.standard A
  (Abelian.Ext.homAddEquiv.{max u₀ v₀, v}).trans
    (Abelian.Ext.homAddEquiv.{max u₀ v₀, w}).symm

def moduleAbelianCohomologyLarge (X : Scheme.{u})
    (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) :
    coherentModuleGroup X F q ≃+ CoherentEtale.Source X F q :=
  ((moduleCohomologyExtResolutionNatIso X q).app F).addCommGroupIsoToAddEquiv.trans
    (@coherentExtUniverseEquiv
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      inferInstance inferInstance (comparisonHasExt X) (HasExt.standard _) _ _ q)
```

## New

```lean
def coherentModuleGroup (X : Scheme.{u})
    (F : X.Modules) (q : ℕ) : AddCommGrpCat.{u} :=
  (forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    AddCommGrpCat.{u}).obj ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F)

def coherentExtUniverseEquiv {A : Type u₀} [Category.{v₀} A] [Abelian A]
    [hs : HasExt.{v} A] [hl : HasExt.{w} A] (M N : A) (q : ℕ) :
    Abelian.Ext.{v} M N q ≃+ Abelian.Ext.{w} M N q where
  toEquiv := Abelian.Ext.chgUniv
  map_add' x y := by
    let := HasDerivedCategory.standard A
    have h (z : Abelian.Ext.{v} M N q) :
        Abelian.Ext.homAddEquiv.{max u₀ v₀, w} (Abelian.Ext.chgUniv z) =
          Abelian.Ext.homAddEquiv.{max u₀ v₀, v} z :=
      Abelian.Ext.homEquiv_chgUniv z
    apply Abelian.Ext.homAddEquiv.{max u₀ v₀, w}.injective
    exact (h (x + y)).trans
      (((Abelian.Ext.homAddEquiv.{max u₀ v₀, v}).map_add x y).trans
        ((congrArg₂ (· + ·) (h x).symm (h y).symm).trans
          ((Abelian.Ext.homAddEquiv.{max u₀ v₀, w}).map_add
            (Abelian.Ext.chgUniv x) (Abelian.Ext.chgUniv y)).symm))

def moduleAbelianCohomologyLarge (X : Scheme.{u})
    (F : X.Modules) (q : ℕ) : coherentModuleGroup X F q ≃+
      CoherentEtale.Source X F q :=
  ((moduleCohomologyExtResolutionNatIso X q).app F).addCommGroupIsoToAddEquiv.trans
    (@coherentExtUniverseEquiv
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      _ _ (comparisonHasExt X) (HasExt.standard _) _ _ q)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| CanonicalCoherentEtaleComparison | unclaimed | same maps; proved component APIs |
| CoherentEtaleComparisonPullback | unclaimed | consumer check |
| CoherentPowerComparison | unclaimed | consumer check |
| QcoherentComparisonDegreeZero | B2, new | normalization of the fixed component |
| QcoherentNormalizedComparison | B2 | uses both proved component APIs |
| CoherentFrobeniusPullback | A2, restored | one forced duplicate-import removal; compiles |
| CoherentFrobeniusComparison | Q2, quarantined | consumer check; mentions the fixed map |
| QcoherentCohomologyComparisonPullback | unclaimed | consumer check |
| QcoherentNormalizedPullbackSquare | F4, restored | two necessary import edits; compiles |

Names in this table are modules under `Sheaf.AlgebraicGeometry`.

## Status

landed 20261020T230711-L-602865 2026-10-20 (merge of deliver/B2/Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison)
