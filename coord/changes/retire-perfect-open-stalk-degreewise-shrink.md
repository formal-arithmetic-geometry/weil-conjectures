# Retire PerfectOpenStalkDegreewiseShrink

## Reason

The assigned retirement row in coord/retire-items.tsv identifies the Sheaf copy as a
restated twin of the source theorem. The source proof is complete. Its canonical
comparison interface differs from the old arbitrary-comparison interface, so the sole
consumer must explicitly transport coordinates.

## Old

Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseShrink declared:

```lean
theorem exists_affine_perfect_open_stalk_degreewise_shrink
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P)
    (W : X.Opens) (hxW : x ∈ W) (hWU : W ≤ U)
    (e :
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ) ⋙
      (openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ) ≅
      (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ))
    (g : ∀ n : ℤ,
      (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).obj P).X n ⟶
      (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).obj Q).X n)
    (hcomm : ∀ n : ℤ,
      (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g n) ≫
        (((openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ)).obj
          (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).obj Q)).d n (n + 1) =
      (((openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ)).obj
        (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).obj P)).d n (n + 1) ≫
        (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g (n + 1))) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (_hV : IsAffineOpen V) (_hVW : V ≤ W) (hVU : V ≤ U),
      let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S := (openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)
      let T := (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)
      ∃ (eV : R ⋙ S ≅ T) (k : ∀ n : ℤ, (R.obj P).X n ⟶ (R.obj Q).X n),
        (∀ n : ℤ, k n ≫ (R.obj Q).d n (n + 1) =
          (R.obj P).d n (n + 1) ≫ k (n + 1)) ∧
        (∀ n : ℤ, (openModuleStalkFunctor X V ⟨x, hxV⟩).map (k n) =
          (eV.app P).hom.f n ≫ (e.app P).inv.f n ≫
            (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g n) ≫
              (e.app Q).hom.f n ≫ (eV.app Q).inv.f n)
```

## New

The node is attached to the existing source declaration, unchanged:

```lean
theorem exists_affine_perfect_open_stalk_degreewise_shrink
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P)
    (W : X.Opens) (hxW : x ∈ W) (hWU : W ≤ U)
    (g : ∀ n : ℤ,
      (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).obj P).X n ⟶
      (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).obj Q).X n)
    (hcomm : ∀ n : ℤ,
      (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g n) ≫
        (((openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ)).obj
          (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).obj Q)).d n (n + 1) =
      (((openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ)).obj
        (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).obj P)).d n (n + 1) ≫
        (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g (n + 1))) :
    let e : (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ) ⋙
        (openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ) ≅
        (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ) :=
      Functor.mapHomologicalComplexCompIso
        (openModuleStalkRestrictionComparison X U W hWU x hxU hxW) (.up ℤ)
    ∃ (V : X.Opens) (hxV : x ∈ V) (_hV : IsAffineOpen V) (_hVW : V ≤ W) (hVU : V ≤ U),
      let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S := (openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)
      let T := (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)
      let eV : R ⋙ S ≅ T := Functor.mapHomologicalComplexCompIso
        (openModuleStalkRestrictionComparison X U V hVU x hxU hxV) (.up ℤ)
      ∃ k : ∀ n : ℤ, (R.obj P).X n ⟶ (R.obj Q).X n,
        (∀ n : ℤ, k n ≫ (R.obj Q).d n (n + 1) =
          (R.obj P).d n (n + 1) ≫ k (n + 1)) ∧
        (∀ n : ℤ, (openModuleStalkFunctor X V ⟨x, hxV⟩).map (k n) =
          (eV.app P).hom.f n ≫ (e.app P).inv.f n ≫
            (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g n) ≫
              (e.app Q).hom.f n ≫ (eV.app Q).inv.f n)
```

PerfectOpenStalkChainMapLift imports the source module. If cW and cV are its canonical
comparisons and eW is the arbitrary comparison returned by the degreewise lift, the
consumer takes eV = cV ≪≫ cW.symm ≪≫ eW. Expansion of components proves the same
chain-map formula as before. All parameters, universes, hypotheses and the public
signature of the consumer remain verbatim. The original node's arbitrary-coordinate
existence claim follows by this same composition; the canonical source result is
sufficient without restricting that claim. No definition or target changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOpenStalkChainMapLift | unclaimed | Switch private import, call canonical source theorem, compose comparison; unchanged signature. |
| Sheaf.AlgebraicGeometry.PerfectOpenStalkDerivedHomDescent | unclaimed | Indirect user; unchanged chain-map-lift interface. |
| Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift | unclaimed | Indirect user; unchanged chain-map-lift interface. |
| Sheaf.AlgebraicGeometry.PerfectStalkQuasiIsoDetection | unclaimed | Indirect user; unchanged chain-map-lift interface. |

The downstream.py --uses search and a search in both source roots identify one direct
importer and no other callers. Source counterparts keep every declaration, signature,
attribute and import. No source file is delivered. The parent node still depends on
the shrinking node, which now attaches to the source implementation. No unit step is
withdrawn. The Sheaf copy is listed in deleted.txt.

## Status

landed 20261020T162915-L-3674512 2026-10-20 (merge of deliver/M1/Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseShrink)
