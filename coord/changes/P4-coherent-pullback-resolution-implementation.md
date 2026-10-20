# Fixed coherent comparison interfaces

## Reason

The quarantined item needs the upstream resolution edge theorem. That theorem imports the
upstream resolution naturality module, while the canonical comparison imported a retained
Sheaf implementation declaring the same names. Use the upstream implementation consistently.
Both construct the fixed normalized comparison from injective resolutions and sections;
N1-module-ext-comparison-components.md describes the retained implementation's caches.
No upstream file, declaration, attribute, signature, or public import is edited.

During this session the shared Sheaf FieldLinearModuleCohomologyOperations was withdrawn.
Its upstream replacement provides scalarCohomology. Redirect the canonical public import
accordingly; restoring the withdrawn duplicate would recreate the namespace collision.

The concrete comparison previously made the kernel repeatedly compare module-H aliases
and derived-category additive structures. Construct both Ext presentations together in a
CoherentExtPresentation record, with their existing coefficient maps, universe equivalence,
and a proved naturality field. The constructor is generic in the abelian category; its
naturality is proved by Ext.homAddEquiv before specializing to schemes. Cache the small
resolution equivalence with these exact group types. coherentModuleGroup uses the existing
forgetful functor, whose value is definitionally AddCommGrpCat.of the same module object.
The additive action constructs the same large comparison and conjugates the same coefficient
map, with all intermediate groups taken from that single record.

All existing public signatures stay verbatim. No arbitrary existence witness, axiom, or
postponed proof defines any new data. The comparison implementation import changes, so any
target using the canonical comparison requires the semantic review of AGENTS.md §4.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

```lean
def coherentModuleGroup (X : Scheme.{u})
    (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F)
```

```lean
def moduleAbelianCohomologyLarge (X : Scheme.{u})
    (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) :
    coherentModuleGroup X F q ≃+ CoherentEtale.Source X F q :=
  ((moduleCohomologyExtResolutionNatIso X q).app F).addCommGroupIsoToAddEquiv.trans
    (@coherentExtUniverseEquiv
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      inferInstance inferInstance (comparisonHasExt X) (HasExt.standard _) _ _ q)
```

```lean
def coherentAdditiveEndomorphism (X : Scheme.{u}) (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ)
    (φ : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F ⟶
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F) :
    coherentModuleGroup X F q →+ coherentModuleGroup X F q :=
  (moduleAbelianCohomologyLarge X F q).symm.toAddMonoidHom.comp
    ((@Sheaf.H.map _ _ _ inferInstance (HasExt.standard _) _ _ φ q).comp
      (moduleAbelianCohomologyLarge X F q).toAddMonoidHom)
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

```lean
def coherentModuleGroup (X : Scheme.{u})
    (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) : AddCommGrpCat.{u} :=
  (RingedSpace.moduleCohomology X.toRingedSpace q ⋙
    forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).obj F
```

```lean
def moduleAbelianCohomologyLarge (X : Scheme.{u})
    (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) :
    coherentModuleGroup X F q ≃+ CoherentEtale.Source X F q :=
  (coherentSmallResolutionEquiv X F q).trans (coherentExtPresentationFor X F q).change
```

```lean
def coherentAdditiveEndomorphism (X : Scheme.{u}) (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ)
    (φ : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F ⟶
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F) :
    coherentModuleGroup X F q →+ coherentModuleGroup X F q :=
  let D := coherentExtPresentationFor X F q
  let e := (coherentSmallResolutionEquiv X F q).trans D.change
  e.symm.toAddMonoidHom.comp ((D.largeMap φ).comp e.toAddMonoidHom)
```

The added public declarations are coherentExtUniverse_postcomp, CoherentExtPresentation,
coherentExtPresentationData, coherentCohomologyHasExt, coherentExtPresentationFor,
coherentSmallAbelianGroup, and coherentSmallResolutionEquiv. Their attachment is recorded
on def-pbc-canonical-coherent-etale-comparison. The retained Sheaf resolution module and
its attachment remain intact; this delivery withdraws nothing.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
--uses moduleAbelianCohomologyLarge` reports zero live downstream modules and four local
uses in the canonical comparison. Source inspection additionally checked all nine direct
archived importers. None mentions comparisonHasExt, comparisonHasSheafify,
sectionsComparisonNatIso, or siteSectionsNatIso through the removed resolution import.
Their statements continue to concern the same normalized common-resolution comparison.
The assigned importer is restored in this packet; other archived files retain their
separate rework assignments and are not withdrawn.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback | P4 | Restored; complete proof uses the upstream edge API. |
| Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison | unclaimed in synchronized records | Upstream resolution import; explicit caches of the same comparison data. |
| Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback | quarantined; separate rework | Same normalized comparison; archive unchanged. |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare | quarantined; separate rework | Same normalized comparison; archive unchanged. |
| Sheaf.AlgebraicGeometry.CoherentPowerComparison | quarantined; separate rework | Same normalized comparison; archive unchanged. |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison | quarantined; separate rework | Same normalized comparison; archive unchanged. |
| Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison | quarantined; separate rework | Same normalized comparison; archive unchanged. |
| Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback | quarantined; separate rework | Same normalized comparison; archive unchanged. |
| Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages | quarantined; separate rework | Same normalized comparison; archive unchanged. |
| Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel | quarantined; separate rework | Same normalized comparison; archive unchanged. |

## Status

landed 20261020T153015-L-2863194 2026-10-20 (merge of deliver/P4/Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback)
