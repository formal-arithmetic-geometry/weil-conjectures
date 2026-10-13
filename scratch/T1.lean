import Mathlib

open CategoryTheory

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {MX : Type u₁} {MY : Type u₂} {MZ : Type u₃} {AX : Type u₄} {AY : Type u₅}
  {AZ : Type u₆} [Category.{v₁} MX] [Category.{v₂} MY] [Category.{v₃} MZ] [Category.{v₄} AX]
  [Category.{v₅} AY] [Category.{v₆} AZ]

/-- Lifting the composition isomorphism of left adjoints along faithful forgetful functors. -/
theorem exists_compIso_lift
    (UX : MX ⥤ AX) (UY : MY ⥤ AY) (UZ : MZ ⥤ AZ)
    {Lu : AX ⥤ AY} {Ru : AY ⥤ AX} (Au : Lu ⊣ Ru)
    {Lv : AY ⥤ AZ} {Rv : AZ ⥤ AY} (Av : Lv ⊣ Rv)
    {Luv : AX ⥤ AZ} {Ruv : AZ ⥤ AX} (Auv : Luv ⊣ Ruv)
    (dA : Rv ⋙ Ru ≅ Ruv)
    {PU : MY ⥤ MX} {PV : MZ ⥤ MY} {PUV : MZ ⥤ MX}
    (pU : PU ⋙ UX ≅ UY ⋙ Ru) (pV : PV ⋙ UY ≅ UZ ⋙ Rv) (pUV : PUV ⋙ UX ≅ UZ ⋙ Ruv)
    {LU : MX ⥤ MY} (eU : LU ⋙ UY ≅ UX ⋙ Lu) (aU : LU ⊣ PU)
    (hU : ∀ G F (h : LU.obj G ⟶ F), UX.map (aU.homEquiv G F h) ≫ pU.hom.app F =
      Au.homEquiv (UX.obj G) (UY.obj F) (eU.inv.app G ≫ UY.map h))
    {LV : MY ⥤ MZ} (eV : LV ⋙ UZ ≅ UY ⋙ Lv) (aV : LV ⊣ PV)
    (hV : ∀ G F (h : LV.obj G ⟶ F), UY.map (aV.homEquiv G F h) ≫ pV.hom.app F =
      Av.homEquiv (UY.obj G) (UZ.obj F) (eV.inv.app G ≫ UZ.map h))
    {LUV : MX ⥤ MZ} (eUV : LUV ⋙ UZ ≅ UX ⋙ Luv) (aUV : LUV ⊣ PUV)
    (hUV : ∀ G F (h : LUV.obj G ⟶ F), UX.map (aUV.homEquiv G F h) ≫ pUV.hom.app F =
      Auv.homEquiv (UX.obj G) (UZ.obj F) (eUV.inv.app G ≫ UZ.map h))
    (d : PUV ≅ PV ⋙ PU)
    (hd : ∀ F, UX.map (d.hom.app F) ≫ pU.hom.app (PV.obj F) ≫ Ru.map (pV.hom.app F) =
      pUV.hom.app F ≫ dA.inv.app (UZ.obj F)) :
    ∃ c : LU ⋙ LV ≅ LUV,
      (∀ G, UZ.map (c.hom.app G) ≫ eUV.hom.app G =
          eV.hom.app (LU.obj G) ≫ Lv.map (eU.hom.app G) ≫
            (((conjugateIsoEquiv Auv (Au.comp Av)).symm dA.symm).symm).inv.app (UX.obj G)) ∧
      (∀ G, (aU.comp aV).unit.app G ≫ (PV ⋙ PU).map (c.hom.app G) =
          aUV.unit.app G ≫ d.hom.app (LUV.obj G)) ∧
      (∀ c' : LU ⋙ LV ≅ LUV,
        (∀ G, (aU.comp aV).unit.app G ≫ (PV ⋙ PU).map (c'.hom.app G) =
          aUV.unit.app G ≫ d.hom.app (LUV.obj G)) → c' = c) := by
  set c := (conjugateIsoEquiv aUV (aU.comp aV)).symm d with hc
  have hunit : ∀ G, (aU.comp aV).unit.app G ≫ (PV ⋙ PU).map (c.hom.app G) =
      aUV.unit.app G ≫ d.hom.app (LUV.obj G) := fun G => by
    have := unit_conjugateEquiv_symm aUV (aU.comp aV) d.hom G
    simpa [hc] using this.symm
  refine ⟨c, fun G => ?_, hunit, fun c' hc' => ?_⟩
  · set g := UX.obj G
    have key : (Au.comp Av).homEquiv g (Luv.obj g)
        ((Lv.map (eU.inv.app G) ≫ eV.inv.app (LU.obj G)) ≫ UZ.map (c.hom.app G) ≫
          eUV.hom.app G) =
        (Au.comp Av).homEquiv g (Luv.obj g)
          ((((conjugateIsoEquiv Auv (Au.comp Av)).symm dA.symm).symm).inv.app g) := by
      have h1 : (Au.comp Av).homEquiv g (Luv.obj g)
          ((((conjugateIsoEquiv Auv (Au.comp Av)).symm dA.symm).symm).inv.app g) =
          Auv.unit.app g ≫ dA.inv.app (Luv.obj g) := by
        rw [homEquiv_unit]
        exact (unit_conjugateEquiv_symm Auv (Au.comp Av) dA.inv g).symm
      have hAv : Av.homEquiv (UY.obj (LU.obj G)) (Luv.obj g)
          (eV.inv.app (LU.obj G) ≫ UZ.map (c.hom.app G) ≫ eUV.hom.app G) =
          UY.map (aV.homEquiv _ _ (c.hom.app G)) ≫ pV.hom.app (LUV.obj G) ≫
            Rv.map (eUV.hom.app G) := by
        rw [← Category.assoc, Av.homEquiv_naturality_right, ← hV, Category.assoc]
      have hAu : Au.homEquiv g (Rv.obj (Luv.obj g))
          (eU.inv.app G ≫ UY.map (aV.homEquiv _ _ (c.hom.app G)) ≫ pV.hom.app (LUV.obj G) ≫
            Rv.map (eUV.hom.app G)) =
          UX.map (aU.homEquiv _ _ (aV.homEquiv _ _ (c.hom.app G))) ≫
            pU.hom.app (PV.obj (LUV.obj G)) ≫ Ru.map (pV.hom.app (LUV.obj G)) ≫
              Ru.map (Rv.map (eUV.hom.app G)) := by
        rw [← Category.assoc, ← Category.assoc, Au.homEquiv_naturality_right,
          Au.homEquiv_naturality_right, ← hU]
        simp only [Category.assoc]
      have hunit' : aU.homEquiv _ _ (aV.homEquiv _ _ (c.hom.app G)) =
          aUV.unit.app G ≫ d.hom.app (LUV.obj G) := by
        have := (aU.comp aV).homEquiv_unit G (LUV.obj G) (c.hom.app G)
        rw [comp_homEquiv, Equiv.trans_apply] at this
        rw [this]
        exact hunit G
      rw [h1, comp_homEquiv, Equiv.trans_apply, Category.assoc, Av.homEquiv_naturality_left]
      erw [hAv, hAu]
      rw [hunit', Functor.map_comp, Category.assoc, reassoc_of% (hd (LUV.obj G))]
      have hu := hUV G (LUV.obj G) (𝟙 _)
      simp only [Functor.map_id, homEquiv_unit] at hu
      rw [reassoc_of% hu]
      have hn := dA.inv.naturality (eUV.hom.app G)
      simp only [Functor.comp_map] at hn
      erw [← hn]
      rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
      erw [Functor.map_id, Category.id_comp]
      rfl
    have k := ((Au.comp Av).homEquiv _ _).injective key
    rw [← k]
    simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp,
      Iso.hom_inv_id_app_assoc]
  · ext G
    apply ((aU.comp aV).homEquiv _ _).injective
    simp only [homEquiv_unit]
    exact (hc' G).trans (hunit G).symm

end CategoryTheory.Adjunction
