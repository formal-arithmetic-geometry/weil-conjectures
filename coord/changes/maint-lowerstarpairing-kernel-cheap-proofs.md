# LowerStarPairing: kernel-cheap proofs (upstream file)

Module `WeilConjectures.WeilSheaf.LowerStarPairing` (upstream WeilConjectures file).
No statement, name or import changes; proofs only. For the PR agent to send upstream.

## Reason

The file compiled alone in 100-114 s, all of it kernel type checking: about 48 s for
`lowerStar_obj_obj_str_hom_hom` and about 47 s for `lowerStar_unit_str`.

* `lowerStar_obj_obj_str_hom_hom`: `simp only` with rfl lemmas (`adicLowerStarComp_hom_app_hom`,
  `Mod.comp_hom'`, ...) leaves no proof term, so the kernel had to re-check the closing equation
  `((adicLowerStarGeometricFiberMapCompFrobeniusIso ..).hom.app c).hom =
  (lowerStarGeometricFiberMapCompFrobeniusIso ..).hom.app c.X` by unfolding the sheaf categories
  (measured alone: 49.6 s for this `rfl`). The same lemmas used with `rw` give a proof term, and the
  kernel no longer unfolds anything.
* `lowerStar_unit_str`: the `rw [reassoc_of% hψ]` step cost about 47 s in the kernel. The argument is
  now a private lemma `unit_str_aux` over arbitrary monoidal categories and lax monoidal functors.
  It is applied once to the concrete functors.

Result: 6.9 s alone. Direct importers `WeilSheaf.Finiteness` (20 s) and `WeilSheaf.LowerStarTensorPow`
(22 s) compile against it.

## New proofs

```lean
  rw [lowerStar_obj_obj_str, Iso.trans_hom, Mod.comp_hom', Iso.app_hom, Functor.mapIso_hom,
    adicLowerStar_map_hom, adicLowerStarGeometricFiberMapCompFrobeniusIso,
    lowerStarGeometricFiberMapCompFrobeniusIso, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom,
    Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    Mod.comp_hom', Mod.comp_hom', Iso.symm_hom, Iso.symm_hom, adicLowerStarComp_hom_app_hom,
    adicLowerStarCongr_hom_app_hom, adicLowerStarComp_inv_app_hom]
```

```lean
private lemma unit_str_aux {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] (F : C ⥤ D) (GC : C ⥤ C) (GD : D ⥤ D) [F.LaxMonoidal]
    [GC.LaxMonoidal] [GD.LaxMonoidal] (ψ : F ⋙ GD ⟶ GC ⋙ F) [NatTrans.IsMonoidal ψ]
    (R : C) (s : GC.obj R ⟶ R) (η : 𝟙_ C ⟶ R) (h : ε GC ≫ GC.map η ≫ s = η) :
    ε GD ≫ GD.map (ε F ≫ F.map η) ≫ (ψ.app R ≫ F.map s) = ε F ≫ F.map η
-- lowerStar_unit_str:
  rw [lowerStar_obj_obj_str_hom_hom]
  exact unit_str_aux _ _ _ (lowerStarGeometricFiberMapCompFrobeniusIso (WeilCoefficients.{u} l) φ
    (comp_over φ (Spec (CommRingCat.of k₀)))).hom R.obj.carrier.X R.obj.str.hom.hom η h
```
