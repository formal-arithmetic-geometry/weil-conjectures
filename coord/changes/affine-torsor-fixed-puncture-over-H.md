# affine_torsor_fixed_orbits_compatibility

## Reason

Return X-77e71 E2 rejects the false arbitrary-θ/arbitrary-q interface.
The standing human decision recorded under STAGE 2 STATEMENT CORRECTION in
coord/STATE.md authorizes source-faithful corrections below unit level. This
node is not a realized unit statement or step. The source's over-base condition
is now encoded by an isomorphism in Over (Spec H), and q is fixed canonically.
No target statement or definition changes.

## Old

```lean
theorem affine_torsor_fixed_orbits_compatibility
    {R H : CommRingCat.{u}} {ι : R →+* H}
    {Y : Scheme.{u}} {p : Y ⟶ Spec R}
    {B : Type u} [CommRing B] [Algebra H B]
    {V : (Spec (CommRingCat.of B)).Opens}
    (θ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅ V.toScheme)
    (q : Spec (CommRingCat.of B) ⟶ Spec H) :
    θ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom ι))
```

## New

```lean
theorem affine_torsor_fixed_orbits_compatibility
    {R H : CommRingCat.{u}} {ι : R →+* H}
    {Y : Scheme.{u}} {p : Y ⟶ Spec R}
    {B : Type u} [CommRing B] [Algebra H B]
    {V : (Spec (CommRingCat.of B)).Opens}
    (θ : Over.mk (pullback.snd p (Spec.map (CommRingCat.ofHom ι))) ≅
      Over.mk (V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H B)))) :
    θ.hom.left ≫ V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H B)) =
      pullback.snd p (Spec.map (CommRingCat.ofHom ι))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentCore | unclaimed | Its old call expects a plain scheme iso and arbitrary q. The geometric input supplies no over-H iso, so replace only the invalid proof of affine_torsor_fixed_orbits with sorry. Its signature, visibility, dispute annotation and private counterexamples remain identical. |

The only actual caller is listed above (tools/downstream.py --uses). Its 140
transitive importers keep the same interfaces. No second interface correction
is made in an unheld module. DescentCore was already disputed because its
arbitrary m and K need not describe the descent action; repairing that statement
belongs to the independently returned geometric/descent item. We do not prove
it from the known-false geometric statement.

## Status

landed 20261013T201742-L-3966762 2026-10-13 (merge of deliver/D3/Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureCompatibility)

Repaired in the returned D3 delivery. The corrected interface is
human-approved under the standing stage-2 statement-correction decision.

## Forced adaptations

`Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentCore` is held
by another group and is included only as a forced adaptation. Against the
corrected dependency, its former proof attempted to apply the old compatibility
theorem to a plain scheme isomorphism and an arbitrary `q`; this no longer type
checks because the theorem now requires an isomorphism in `Over (Spec H)`. The
adapted file keeps its public signature and changes only the proof to its already
documented `sorry`, preserving the separate disputed theorem. No other line is
needed for the corrected interface.
