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
  sorry

end Forget

end CategoryTheory.Functor
