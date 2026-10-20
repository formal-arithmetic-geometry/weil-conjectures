# AlgebraicGeometry.factorCoordinatesAbelian and affineTildePushforwardHomologyFactorization

## Reason

Restore the quarantined factorization module after the 2026-10-20 upstream
update. The original local Abelian instance fails to synthesize
`(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat` and leaves
universe constraints. Requesting the instance on `SheafOfModules.{u}` fixes the
module universe explicitly, as in the corresponding upstream module.

The universe-only repair compiled but exceeded 60 seconds during a later
preflight. Profiling isolated repeated definitional comparison between ordinary
scheme pushforward and ringed-space module direct image at an affine-tilde
complex. Use the ordinary scheme pushforward as an explicitly typed functor P
also for the derived unit. These functors are definitionally equal; their
additivity instances are proofs and hence proof irrelevant. All hypotheses,
objects, maps and conclusions retain their original meaning. No target or
source-library declaration changes.

The returned delivery at `90d6e451e1` passed mathematical review but could
not land over its old base `e0d550965`. Reconcile this packet with the current
quarantine archive and node. The live Lean path is still absent in both the
shared snapshot and server working tree; the rework archive is retained intact.
The current source tree has also retired
`Sheaf.Algebra.Homology.MixedTensorUnderlyingHomology` (B4, landing
`20261020T141302-L-2031820`). The returned packet now fails with
`Unknown identifier RingTensorCohomology.mapHomologyIso_hom_comp`.
Replace that proof import with `import all` of its adopted source counterpart,
which preserves the private helper and is the import already used by the
upstream factorization module. No source module is edited.

## Old

```lean
local instance (priority := 2000) factorCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := SheafOfModules.instAbelian Y.ringCatSheaf
```

Proof import:

```lean
import Sheaf.Algebra.Homology.MixedTensorUnderlyingHomology
```

In the theorem statement:

```lean
theorem affineTildePushforwardHomologyFactorization
    (D B : Type u) [CommRing D] [CommRing B] (ψ : B →+* D)
    [(affineTildeFunctor D ⋙
      Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom ψ))).PreservesZeroMorphisms]
    (Cg : CochainComplex (ModuleCat.{u} D) ℤ) (i : ℤ)
    (S : ModuleCat.{u} B)
    (v : S ⟶ (ModuleCat.restrictScalars ψ).obj (Cg.homology i)) :
    let T := affineTildeFunctor B
    let _ : T.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
    let _ : T.PreservesHomology := tilde_preservesHomology B
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i
    let σ := affineTildePushforwardComparison D B ψ
    let a := (σ.hom.mapHomologicalComplex
      (.up ℤ)).app Cg
    let β := (RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom ψ)).toLRSHom.toShHom).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((affineTildeFunctor D).mapHomologicalComplex (.up ℤ)).obj Cg))
    T.map (v ≫ ((Cg.sc i).mapHomologyIso (ModuleCat.restrictScalars ψ)).inv) ≫
        (((((ModuleCat.restrictScalars ψ).mapHomologicalComplex
          (.up ℤ)).obj Cg).sc i).mapHomologyIso T).inv ≫
        (DerivedCategory.homologyFunctorFactors _ i).inv.app
          ((T.mapHomologicalComplex (.up ℤ)).obj
            (((ModuleCat.restrictScalars ψ).mapHomologicalComplex (.up ℤ)).obj Cg)) ≫
        H.map (DerivedCategory.Q.map a) ≫ H.map β =
    T.map v ≫ affineTildePushforwardCohomologyMap D B ψ Cg i
```

## New

```lean
local instance (priority := 2000) factorCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))
```

Proof import:

```lean
import all WeilConjectures.Algebra.Homology.MixedTensorUnderlyingHomology
```

In the theorem statement:

```lean
theorem affineTildePushforwardHomologyFactorization
    (D B : Type u) [CommRing D] [CommRing B] (ψ : B →+* D)
    [(affineTildeFunctor D ⋙
      Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom ψ))).PreservesZeroMorphisms]
    (Cg : CochainComplex (ModuleCat.{u} D) ℤ) (i : ℤ)
    (S : ModuleCat.{u} B)
    (v : S ⟶ (ModuleCat.restrictScalars ψ).obj (Cg.homology i)) :
    let T := affineTildeFunctor B
    let _ : T.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
    let _ : T.PreservesHomology := tilde_preservesHomology B
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i
    let σ := affineTildePushforwardComparison D B ψ
    let a := (σ.hom.mapHomologicalComplex
      (.up ℤ)).app Cg
    -- Use the same pushforward functor for the comparison and its derived unit.
    let P : SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace) :=
      Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom ψ))
    let _ : P.Additive := RingedSpace.moduleDirectImage_additive
      (Spec.map (CommRingCat.ofHom ψ)).toLRSHom.toShHom
    let β := P.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((affineTildeFunctor D).mapHomologicalComplex (.up ℤ)).obj Cg))
    T.map (v ≫ ((Cg.sc i).mapHomologyIso (ModuleCat.restrictScalars ψ)).inv) ≫
        (((((ModuleCat.restrictScalars ψ).mapHomologicalComplex
          (.up ℤ)).obj Cg).sc i).mapHomologyIso T).inv ≫
        (DerivedCategory.homologyFunctorFactors _ i).inv.app
          ((T.mapHomologicalComplex (.up ℤ)).obj
            (((ModuleCat.restrictScalars ψ).mapHomologicalComplex (.up ℤ)).obj Cg)) ≫
        H.map (DerivedCategory.Q.map a) ≫ H.map β =
    T.map v ≫ affineTildePushforwardCohomologyMap D B ψ Cg i
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.AffineTildePushforwardHomologyFactorization | B6 | Restored; explicit instance universe and shared pushforward presentation. |
| Sheaf.Algebra.Homology.AffineTildeCoefficientPushforwardHomologyCoordinates | unclaimed, quarantined | Uses the definitionally unchanged main theorem; no adaptation required. |
| Sheaf.Algebra.Homology.AffineTildeDerivedTensorHomologyCoordinates | unclaimed, quarantined | Uses the unchanged inverse-composition theorem; no adaptation required. |

The current `tools/downstream.py --allow-missing --uses` check reports zero
live downstream modules and zero live users of either theorem. A search of the
quarantine retains the two consumers listed above and confirms their respective
uses. Their calls use the preserved interface; no consumer adaptation is required.

The local instance type and priority are unchanged. Both theorem proof bodies
are unchanged. Only the proof import changes; no public imports, definition
bodies, target statements or public instances change. The DAG Lean signature is updated to the definitionally equal
presentation; its mathematical statement and proof dependencies are unchanged.
The repaired import compiled via `lcompile.py` in 26.4 seconds on the server,
with no warnings. The retained packet failed against the same baseline with
the unknown-helper error above.
A separate generic check on arbitrary schemes proved both the pushforward-functor
equality and derived-unit equality by `rfl`; it recompiled in 2.3 seconds during
this repair session. The repaired dry run
`08db094f0c` passed compilation, the axiom probe, and server preflight on the
refreshed delivery base (review class CODEX). The generic check is in scratchpad,
not in the delivered library.

## Status

landed 20261020T154039-L-3032972 2026-10-20 (merge of deliver/B6/Sheaf.Algebra.Homology.AffineTildePushforwardHomologyFactorization)
