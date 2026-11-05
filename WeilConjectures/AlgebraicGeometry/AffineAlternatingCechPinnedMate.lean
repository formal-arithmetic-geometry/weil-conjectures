/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechModel
public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechExchangeResolution
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # The alternating Čech calculation for the pinned derived mate

Source: Stacks Project, Tags 02KH and 08HY; Steps 1--3 of
`lem-pc-affine-alternating-cech-base-change-factorization`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

private theorem mate_factorization
    {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄]
    (F : C₁ ⥤ C₂) (R : C₃ ⥤ C₄) (L : C₂ ⥤ C₄) (P : C₁ ⥤ C₃)
    {E₀ E₁ : C₁} {S₁ S₂ : C₂} {Y₀ Y₁ Y₂ : C₃} {T₁ T₂ T₃ : C₄}
    (s : E₀ ≅ E₁) (α : S₁ ≅ F.obj E₁) (v : S₁ ≅ S₂)
    (w : T₁ ≅ T₂) (b : T₁ ≅ T₃) (β : T₃ ≅ R.obj Y₁)
    (z : Y₀ ≅ Y₁) (c : Y₀ ≅ Y₂)
    (d₀ : P.obj E₀ ⟶ Y₀) (d₁ : P.obj E₁ ⟶ Y₁)
    (δ : L.obj S₁ ⟶ T₁) (δ' : L.obj S₂ ⟶ T₂)
    (bc₀ : L.obj (F.obj E₀) ⟶ R.obj (P.obj E₀))
    (bc₁ : L.obj (F.obj E₁) ⟶ R.obj (P.obj E₁))
    (hn : L.map (F.map s.hom) ≫ bc₁ = bc₀ ≫ R.map (P.map s.hom))
    (hp : P.map s.hom ≫ d₁ = d₀ ≫ z.hom)
    (hu : L.map α.hom ≫ bc₁ ≫ R.map d₁ = δ ≫ b.hom ≫ β.hom)
    (hg : L.map v.hom ≫ δ' = δ ≫ w.hom) :
    bc₀ ≫ R.map (d₀ ≫ c.hom) =
      L.map (F.mapIso s ≪≫ α.symm ≪≫ v).hom ≫ δ' ≫
        (w.symm ≪≫ b ≪≫ β ≪≫ R.mapIso z.symm ≪≫ R.mapIso c).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hg]
  simp only [w.hom_inv_id_assoc]
  rw [← reassoc_of% hu]
  simp only [← L.map_comp_assoc, α.inv_hom_id, Category.comp_id]
  rw [reassoc_of% hn, ← R.map_comp_assoc, hp, R.map_comp]
  simp

private theorem pinnedBaseChange_naturality
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) {E E' : schemeDerivedCategory X} (a : E ⟶ E') :
    (derivedPullback g).map ((schemeDerivedDirectImage f).map a) ≫
        schemeDerivedBaseChangeMap f f' g p h E' =
      schemeDerivedBaseChangeMap f f' g p h E ≫
        (schemeDerivedDirectImage f').map ((derivedPullback p).map a) := by
  classical
  let δ {V W : Scheme.{u}} (k : V ⟶ W) :=
    (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) k
  let c {V W Z : Scheme.{u}} (k : V ⟶ W) (l : W ⟶ Z) :=
    (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))) k l
  let adj (k : X ⟶ S) := Classical.choose (exists_schemeDerivedAdjunction k
    (hAdd := (Classical.choose exists_derivedPullbackComposition.{u, w}) k)
    (δ k) ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) k))
  let adj' := Classical.choose (exists_schemeDerivedAdjunction f'
    (hAdd := (Classical.choose exists_derivedPullbackComposition.{u, w}) f')
    (δ f') ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) f'))
  let τ : derivedPullback (f' ≫ g) ⟶ derivedPullback (p ≫ f) :=
    (eqToIso (congrArg (fun k ↦ derivedPullback k) h.symm)).hom
  let σ : schemeDerivedDirectImage f ⋙ derivedPullback g ⋙ derivedPullback f' ⟶
      derivedPullback p :=
    Functor.whiskerLeft (schemeDerivedDirectImage f) ((c f' g).hom ≫ τ ≫ (c p f).inv) ≫
      (Functor.associator (schemeDerivedDirectImage f) (derivedPullback f)
        (derivedPullback p)).inv ≫
      Functor.whiskerRight (adj f).counit (derivedPullback p)
  have hx (K : schemeDerivedCategory X) :
      schemeDerivedBaseChangeMap f f' g p h K = adj'.homEquiv _ _ (σ.app K) := by
    unfold schemeDerivedBaseChangeMap
    congr 1
    simp only [σ, τ, adj, δ, c, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp,
      Functor.comp_obj, Category.assoc]
    simp only [eqToIso.hom, eqToHom_app]
  rw [hx, hx]
  exact adj'.homEquiv_naturality_left_square _ _ _ _ (σ.naturality a)

end AlgebraicGeometry
