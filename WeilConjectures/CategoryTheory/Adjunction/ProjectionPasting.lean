/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Pasting projection formulas lying over each other

Let `Lf ≅ I ⋙ G` be a factorization of a functor `Lf : W_X ⥤ W_Y` (in the application, the
direct image with compact support `Rf₀! = Rg_* ∘ i_!` of Weil complexes along a compactification
`X ⟶[i] Z ⟶[g] Y`), and let `Pf ≅ Pg ⋙ Pi` be the corresponding factorization of the inverse
images. Projection formulas `eI : I M ⊗ N ≅ I (M ⊗ Pi N)` and `eG : G A ⊗ T ≅ G (A ⊗ Pg T)` paste
to a projection formula `Lf M ⊗ T ≅ Lf (M ⊗ Pf T)`
(`CategoryTheory.Functor.projectionIsoOfComp`).

Suppose that functors `F_X, F_Z, F_Y` to monoidal categories (forgetting the Weil structures)
carry `I`, `G`, the inverse images and the tensor products to functors `I'`, `G'`, ... and to the
tensor products, and that they carry `eI` and `eG` to given projection morphisms `q` and `p`
(the inverse of the projection comparison of the extension by zero, and the projection morphism
of the proper direct image). Then they carry the pasted projection formula to the composite
projection morphism `p (I' K) B ≫ G' (q K (Pg' B) ≫ I' (K ◁ ε B))`
(`CategoryTheory.Functor.map_projectionIsoOfComp_hom_app`). If moreover the mates of the
comparisons of `I` and `G` under adjunctions are isomorphisms, so is the mate of the pasted
comparison (`CategoryTheory.Functor.isIso_mateEquiv_pasting_app`).
-/

@[expose] public section

namespace CategoryTheory.Functor

open MonoidalCategory

variable {WX WZ WY BX BZ BY : Type*} [Category* WX] [Category* WZ] [Category* WY]
  [Category* BX] [Category* BZ] [Category* BY]
  [MonoidalCategory BX] [MonoidalCategory BZ] [MonoidalCategory BY]

section Weil

variable {I : WX ⥤ WZ} {G : WZ ⥤ WY} {Lf : WX ⥤ WY} {Pi : WZ ⥤ WX} {Pg : WY ⥤ WZ}
  {Pf : WY ⥤ WX} {TX : WX × WX ⥤ WX} {TZ : WZ × WZ ⥤ WZ} {TY : WY × WY ⥤ WY}
  (ℓ : Lf ≅ I ⋙ G) (pc : Pg ⋙ Pi ≅ Pf)
  (eI : I.prod (𝟭 WZ) ⋙ TZ ≅ (𝟭 WX).prod Pi ⋙ TX ⋙ I)
  (eG : G.prod (𝟭 WY) ⋙ TY ≅ (𝟭 WZ).prod Pg ⋙ TZ ⋙ G)

/-- The projection formula `Lf M ⊗ T ≅ Lf (M ⊗ Pf T)` pasted from projection formulas for the
factors `I` and `G` of `Lf ≅ I ⋙ G`:
`Lf M ⊗ T ≅ G (I M) ⊗ T ≅ G (I M ⊗ Pg T) ≅ G (I (M ⊗ Pi (Pg T))) ≅ G (I (M ⊗ Pf T)) ≅ Lf (M ⊗ Pf T)`.
-/
noncomputable def projectionIsoOfComp :
    Lf.prod (𝟭 WY) ⋙ TY ≅ (𝟭 WX).prod Pf ⋙ TX ⋙ Lf :=
  isoWhiskerRight (NatIso.prod ℓ (Iso.refl (𝟭 WY))) TY ≪≫
    (Iso.refl (I.prod (𝟭 WY) ⋙ G.prod (𝟭 WY) ⋙ TY)) ≪≫
    isoWhiskerLeft (I.prod (𝟭 WY)) eG ≪≫
    (Iso.refl ((𝟭 WX).prod Pg ⋙ (I.prod (𝟭 WZ) ⋙ TZ) ⋙ G)) ≪≫
    isoWhiskerRight (isoWhiskerLeft ((𝟭 WX).prod Pg) eI) G ≪≫
    (Iso.refl (((𝟭 WX).prod (Pg ⋙ Pi) ⋙ TX) ⋙ I ⋙ G)) ≪≫
    isoWhiskerRight (isoWhiskerRight (NatIso.prod (Iso.refl (𝟭 WX)) pc) TX) (I ⋙ G) ≪≫
    isoWhiskerLeft ((𝟭 WX).prod Pf ⋙ TX) ℓ.symm

@[simp]
lemma projectionIsoOfComp_hom_app (M : WX) (T : WY) :
    (projectionIsoOfComp ℓ pc eI eG).hom.app (M, T) =
      TY.map ((ℓ.hom.app M, 𝟙 T) : (Lf.obj M, T) ⟶ ((I ⋙ G).obj M, T)) ≫
        eG.hom.app (I.obj M, T) ≫ G.map (eI.hom.app (M, Pg.obj T)) ≫
        G.map (I.map (TX.map ((𝟙 M, pc.hom.app T) : (M, Pi.obj (Pg.obj T)) ⟶ (M, Pf.obj T)))) ≫
        ℓ.inv.app (TX.obj (M, Pf.obj T)) := by
  simp [projectionIsoOfComp]
  rfl


end Weil

section Forget

variable {I : WX ⥤ WZ} {G : WZ ⥤ WY} {Lf : WX ⥤ WY} {Pi : WZ ⥤ WX} {Pg : WY ⥤ WZ}
  {Pf : WY ⥤ WX} {TX : WX × WX ⥤ WX} {TZ : WZ × WZ ⥤ WZ} {TY : WY × WY ⥤ WY}
  (ℓ : Lf ≅ I ⋙ G) (pc : Pg ⋙ Pi ≅ Pf)
  (eI : I.prod (𝟭 WZ) ⋙ TZ ≅ (𝟭 WX).prod Pi ⋙ TX ⋙ I)
  (eG : G.prod (𝟭 WY) ⋙ TY ≅ (𝟭 WZ).prod Pg ⋙ TZ ⋙ G)
  {I' : BX ⥤ BZ} {G' : BZ ⥤ BY} {Pi' : BZ ⥤ BX} {Pg' : BY ⥤ BZ} {Pf' : BY ⥤ BX}
  {FX : WX ⥤ BX} {FZ : WZ ⥤ BZ} {FY : WY ⥤ BY}
  (τX : TX ⋙ FX ≅ FX.prod FX ⋙ tensor BX) (τZ : TZ ⋙ FZ ≅ FZ.prod FZ ⋙ tensor BZ)
  (τY : TY ⋙ FY ≅ FY.prod FY ⋙ tensor BY)
  (βI : FX ⋙ I' ≅ I ⋙ FZ) (βG : FZ ⋙ G' ≅ G ⋙ FY)
  (γi : Pi ⋙ FX ≅ FZ ⋙ Pi') (γg : Pg ⋙ FZ ≅ FY ⋙ Pg') (ε : Pg' ⋙ Pi' ≅ Pf')

/-- The comparison `F_X ⋙ (I' ⋙ G') ≅ Lf ⋙ F_Y` pasted from the comparisons of `I` and `G`. -/
noncomputable def forgetCompIsoOfComp : FX ⋙ (I' ⋙ G') ≅ Lf ⋙ FY :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight βI G' ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft I βG ≪≫ (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight ℓ.symm FY

@[simp]
lemma forgetCompIsoOfComp_inv_app (M : WX) :
    (forgetCompIsoOfComp ℓ βI βG).inv.app M =
      FY.map (ℓ.hom.app M) ≫ βG.inv.app (I.obj M) ≫ G'.map (βI.inv.app M) := by
  simp [forgetCompIsoOfComp]

/-- The comparison `Pf ⋙ F_X ≅ F_Y ⋙ Pf'` pasted from the comparisons of `Pi` and `Pg`. -/
noncomputable def forgetPullIsoOfComp : Pf ⋙ FX ≅ FY ⋙ Pf' :=
  isoWhiskerRight pc.symm FX ≪≫ Functor.associator _ _ _ ≪≫ isoWhiskerLeft Pg γi ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight γg Pi' ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft FY ε

@[simp]
lemma forgetPullIsoOfComp_hom_app (T : WY) :
    (forgetPullIsoOfComp pc γi γg ε).hom.app T =
      FX.map (pc.inv.app T) ≫ γi.hom.app (Pg.obj T) ≫ Pi'.map (γg.hom.app T) ≫
        ε.hom.app (FY.obj T) := by
  simp [forgetPullIsoOfComp]

/-- **Pasting projection formulas lying over projection morphisms.** If the forgetful functors
carry the projection formulas `eI` and `eG` to the morphisms `q` and `p`, they carry the pasted
projection formula `Lf M ⊗ T ≅ Lf (M ⊗ Pf T)` to `p (I' K) B ≫ G' (q K (Pg' B) ≫ I' (K ◁ ε B))`. -/
theorem map_projectionIsoOfComp_hom_app
    (p : ∀ (A : BZ) (B : BY), G'.obj A ⊗ B ⟶ G'.obj (A ⊗ Pg'.obj B))
    (hp : ∀ {A A' : BZ} (φ : A ⟶ A') (B : BY),
      G'.map φ ▷ B ≫ p A' B = p A B ≫ G'.map (φ ▷ Pg'.obj B))
    (q : ∀ (K : BX) (N : BZ), I'.obj K ⊗ N ⟶ I'.obj (K ⊗ Pi'.obj N))
    (hq : ∀ (K : BX) {N N' : BZ} (h : N ⟶ N'),
      I'.obj K ◁ h ≫ q K N' = q K N ≫ I'.map (K ◁ Pi'.map h))
    (hG : ∀ (A : WZ) (T : WY), FY.map (eG.hom.app (A, T)) ≫ βG.inv.app _ ≫
        G'.map (τZ.hom.app (A, Pg.obj T) ≫ FZ.obj A ◁ γg.hom.app T) =
      τY.hom.app (G.obj A, T) ≫ βG.inv.app A ▷ FY.obj T ≫ p (FZ.obj A) (FY.obj T))
    (hI : ∀ (M : WX) (N : WZ), FZ.map (eI.hom.app (M, N)) ≫ βI.inv.app _ ≫
        I'.map (τX.hom.app (M, Pi.obj N) ≫ FX.obj M ◁ γi.hom.app N) =
      τZ.hom.app (I.obj M, N) ≫ βI.inv.app M ▷ FZ.obj N ≫ q (FX.obj M) (FZ.obj N))
    (M : WX) (T : WY) :
    FY.map ((projectionIsoOfComp ℓ pc eI eG).hom.app (M, T)) ≫
        (forgetCompIsoOfComp ℓ βI βG).inv.app _ ≫
        (I' ⋙ G').map (τX.hom.app (M, Pf.obj T) ≫
          FX.obj M ◁ (forgetPullIsoOfComp pc γi γg ε).hom.app T) =
      τY.hom.app (Lf.obj M, T) ≫ (forgetCompIsoOfComp ℓ βI βG).inv.app M ▷ FY.obj T ≫
        p (I'.obj (FX.obj M)) (FY.obj T) ≫
        G'.map (q (FX.obj M) (Pg'.obj (FY.obj T)) ≫
          I'.map (FX.obj M ◁ ε.hom.app (FY.obj T))) := by
  have hβG {A B : WZ} (h : A ⟶ B) : FY.map (G.map h) ≫ βG.inv.app B =
      βG.inv.app A ≫ G'.map (FZ.map h) := βG.inv.naturality h
  have hβI {A B : WX} (h : A ⟶ B) : FZ.map (I.map h) ≫ βI.inv.app B =
      βI.inv.app A ≫ I'.map (FX.map h) := βI.inv.naturality h
  have hτX {A B : WX × WX} (h : A ⟶ B) : FX.map (TX.map h) ≫ τX.hom.app B =
      τX.hom.app A ≫ (FX.map h.1 ⊗ₘ FX.map h.2) := τX.hom.naturality h
  have hτY {A B : WY × WY} (h : A ⟶ B) : FY.map (TY.map h) ≫ τY.hom.app B =
      τY.hom.app A ≫ (FY.map h.1 ⊗ₘ FY.map h.2) := τY.hom.naturality h
  have h₄ : FX.map (TX.map ((𝟙 M, pc.hom.app T) : (M, Pi.obj (Pg.obj T)) ⟶ (M, Pf.obj T))) ≫
      τX.hom.app (M, Pf.obj T) ≫ FX.obj M ◁ FX.map (pc.inv.app T) =
      τX.hom.app (M, Pi.obj (Pg.obj T)) := by
    rw [reassoc_of% (hτX _)]
    dsimp
    simp only [Functor.map_id, id_tensorHom, ← MonoidalCategory.whiskerLeft_comp,
      ← Functor.map_comp]
    simp
  have h₉ : FY.map (TY.map ((ℓ.hom.app M, 𝟙 T) : (Lf.obj M, T) ⟶ ((I ⋙ G).obj M, T))) ≫
      τY.hom.app ((I ⋙ G).obj M, T) = τY.hom.app (Lf.obj M, T) ≫ FY.map (ℓ.hom.app M) ▷ FY.obj T := by
    rw [hτY]
    dsimp
    rw [Functor.map_id, tensorHom_id]
  have hI' := hI M (Pg.obj T)
  have hG' := hG (I.obj M) T
  simp only [projectionIsoOfComp_hom_app, forgetCompIsoOfComp_inv_app, forgetPullIsoOfComp_hom_app,
    Functor.comp_map, Functor.map_comp, Category.assoc, MonoidalCategory.whiskerLeft_comp,
    comp_whiskerRight] at hI' hG' ⊢
  dsimp only [Functor.prod_obj, Functor.id_obj, Functor.comp_obj] at hI' hG' ⊢
  have r3 {A B : WX} (h : A ⟶ B) {Z' : BY} (z : G'.obj (I'.obj (FX.obj B)) ⟶ Z') :
      G'.map (FZ.map (I.map h)) ≫ G'.map (βI.inv.app B) ≫ z =
        G'.map (βI.inv.app A) ≫ G'.map (I'.map (FX.map h)) ≫ z := by
    rw [← G'.map_comp_assoc, hβI, G'.map_comp_assoc]
  have r4 {Z' : BY} (z : G'.obj (I'.obj (FX.obj M ⊗ FX.obj (Pi.obj (Pg.obj T)))) ⟶ Z') :
      G'.map (I'.map (FX.map (TX.map ((𝟙 M, pc.hom.app T) :
          (M, Pi.obj (Pg.obj T)) ⟶ (M, Pf.obj T))))) ≫
        G'.map (I'.map (τX.hom.app (M, Pf.obj T))) ≫
        G'.map (I'.map (FX.obj M ◁ FX.map (pc.inv.app T))) ≫ z =
      G'.map (I'.map (τX.hom.app (M, Pi.obj (Pg.obj T)))) ≫ z := by
    simp only [← G'.map_comp_assoc, ← I'.map_comp, h₄]
  have r6 {Z' : BY} (z : G'.obj (I'.obj (FX.obj M ⊗ Pi'.obj (FZ.obj (Pg.obj T)))) ⟶ Z') :
      G'.map (FZ.map (eI.hom.app (M, Pg.obj T))) ≫
        G'.map (βI.inv.app (TX.obj (M, Pi.obj (Pg.obj T)))) ≫
        G'.map (I'.map (τX.hom.app (M, Pi.obj (Pg.obj T)))) ≫
        G'.map (I'.map (FX.obj M ◁ γi.hom.app (Pg.obj T))) ≫ z =
      G'.map (τZ.hom.app (I.obj M, Pg.obj T)) ≫
        G'.map (βI.inv.app M ▷ FZ.obj (Pg.obj T)) ≫
        G'.map (q (FX.obj M) (FZ.obj (Pg.obj T))) ≫ z := by
    simp only [← G'.map_comp_assoc, hI']
  have r7 {Z' : BY} (z : G'.obj (I'.obj (FX.obj M ⊗ Pi'.obj (Pg'.obj (FY.obj T)))) ⟶ Z') :
      G'.map (q (FX.obj M) (FZ.obj (Pg.obj T))) ≫
        G'.map (I'.map (FX.obj M ◁ Pi'.map (γg.hom.app T))) ≫ z =
      G'.map (I'.obj (FX.obj M) ◁ γg.hom.app T) ≫ G'.map (q (FX.obj M) (Pg'.obj (FY.obj T))) ≫ z := by
    rw [← G'.map_comp_assoc, ← G'.map_comp_assoc]
    erw [hq]
    rfl
  have r8 {Z' : BY} (z : G'.obj (I'.obj (FX.obj M) ⊗ Pg'.obj (FY.obj T)) ⟶ Z') :
      G'.map (βI.inv.app M ▷ FZ.obj (Pg.obj T)) ≫ G'.map (I'.obj (FX.obj M) ◁ γg.hom.app T) ≫ z =
      G'.map (FZ.obj (I.obj M) ◁ γg.hom.app T) ≫ G'.map (βI.inv.app M ▷ Pg'.obj (FY.obj T)) ≫ z := by
    rw [← G'.map_comp_assoc, ← G'.map_comp_assoc]
    erw [← whisker_exchange]
    rfl
  have r10 {Z' : BY} (z : G'.obj (I'.obj (FX.obj M) ⊗ Pg'.obj (FY.obj T)) ⟶ Z') :
      p (FZ.obj (I.obj M)) (FY.obj T) ≫ G'.map (βI.inv.app M ▷ Pg'.obj (FY.obj T)) ≫ z =
      G'.map (βI.inv.app M) ▷ FY.obj T ≫ p (I'.obj (FX.obj M)) (FY.obj T) ≫ z := by
    rw [← Category.assoc, ← hp]
    exact Category.assoc _ _ _
  rw [← FY.map_comp_assoc (ℓ.inv.app _), Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
    reassoc_of% (hβG _), r3, r4, reassoc_of% (hβG _), r6, r7, r8, reassoc_of% hG', r10,
    reassoc_of% h₉]

omit [MonoidalCategory BX] [MonoidalCategory BZ] [MonoidalCategory BY] in
/-- The pasted comparison `F_X ⋙ (I' ⋙ G') ≅ Lf ⋙ F_Y`, as a 2-square, is the vertical
composite of the comparisons of `I` and `G`, whiskered by `ℓ⁻¹ : I ⋙ G ⟶ Lf`. -/
lemma forgetCompIsoOfComp_hom_eq :
    TwoSquare.mk _ _ _ _ (forgetCompIsoOfComp ℓ βI βG).hom =
      (TwoSquare.vComp (TwoSquare.mk _ _ _ _ βI.hom)
        (TwoSquare.mk _ _ _ _ βG.hom)).whiskerLeft ℓ.inv := by
  ext X
  simp [forgetCompIsoOfComp]

omit [MonoidalCategory BX] [MonoidalCategory BZ] [MonoidalCategory BY] in
/-- **The mate of a pasted comparison is invertible** if the mates of the comparisons of the
factors `I` and `G` are: the mate of `F_X ⋙ (I' ⋙ G') ≅ Lf ⋙ F_Y` under `Lf ⊣ R` and the
composite adjunction `I' ⋙ G' ⊣ R_G' ⋙ R_I'`. -/
theorem isIso_mateEquiv_forgetCompIsoOfComp_app {RI : WZ ⥤ WX} {RG : WY ⥤ WZ} {R : WY ⥤ WX}
    {RI' : BZ ⥤ BX} {RG' : BY ⥤ BZ} (adjI : I ⊣ RI) (adjG : G ⊣ RG) (adjLf : Lf ⊣ R)
    (adjI' : I' ⊣ RI') (adjG' : G' ⊣ RG')
    (hI : ∀ L, IsIso ((mateEquiv adjI adjI' (TwoSquare.mk _ _ _ _ βI.hom)).natTrans.app L))
    (hG : ∀ L, IsIso ((mateEquiv adjG adjG' (TwoSquare.mk _ _ _ _ βG.hom)).natTrans.app L))
    (L : WY) :
    IsIso ((mateEquiv adjLf (adjI'.comp adjG')
      (TwoSquare.mk _ _ _ _ (forgetCompIsoOfComp ℓ βI βG).hom)).natTrans.app L) := by
  rw [forgetCompIsoOfComp_hom_eq, conjugateEquiv_mateEquiv_vcomp adjLf (adjI.comp adjG),
    mateEquiv_hcomp]
  dsimp only [TwoSquare.whiskerTop, TwoSquare.hComp, TwoSquare.natTrans, TwoSquare.mk]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  have := hI (RG.obj L)
  have := hG L
  infer_instance


end Forget

end CategoryTheory.Functor
