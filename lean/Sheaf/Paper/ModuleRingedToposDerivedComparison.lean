/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.SectionDerivedRealization
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Algebra.Homology.KFlatModuleObject
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.ProjectionMateExact

import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import Sheaf.Paper.SectionDerivedTensorNormalization

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Module-object and ringed-topos derived comparison

Source: Stacks Project, Sites, Tag 00YV; Modules on Sites, Tags 03EK, 03EL,
03D7, 03DI and 03DJ; Cohomology on Sites, Tags 07A4, 07A6 and 0B56
(blueprint: lem-pd-module-ringed-topos-derived-comparison).

## Main definitions and statements

- `ordinary_exact_flat_kflat`, `ordinary_monoidal`: the ordinary equivalence clauses.
- `derivedPullComparison`, `derivedPushComparison`, `derived_homEquiv`: derived operations.
- `tensorPullComparison`, `delta_comparison`, `mu_comparison`: specified tensor maps.
- `composition_comparison`, `projection_comparison`: composition and the proper mate.
- `open_homEquiv`, `openProjection_comparison`: open adjunction and its unit mate.

-/

@[expose] public noncomputable section

set_option linter.all false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

private def curryComparison {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : C ⥤ C ⥤ C) (S : D × D ⥤ D)
    (t : Functor.uncurry.obj T ⋙ F ⟶ F.prod F ⋙ S) :
    (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (Functor.curry.obj S) where
  app M :=
    { app := fun N ↦ t.app (M, N)
      naturality := by
        intro N N' f
        simpa using t.naturality (Prod.mkHom (𝟙 M) f) }
  naturality := by
    intro M M' f
    ext N
    simpa using t.naturality (Prod.mkHom f (𝟙 N))

private theorem tensorSquare_right
    {C : Type*} [Category C] (T : C × C ⥤ C)
    {A B V W X X' Y Y' : C} (p : X ≅ X') (q : Y ≅ Y') (r : A ≅ B)
    (a : A ⟶ V) (b : V ⟶ T.obj (X, Y))
    (c : B ⟶ W) (d : W ⟶ T.obj (X', Y'))
    (h : a ≫ b ≫ T.map (Prod.mkHom p.hom q.hom) = r.hom ≫ c ≫ d) :
    c ≫ d ≫ T.map (Prod.mkHom p.inv (𝟙 Y')) ≫
        T.map (Prod.mkHom (𝟙 X) q.inv) = r.inv ≫ a ≫ b := by
  rw [← T.map_comp]
  simp only [prod_comp, Category.comp_id, Category.id_comp]
  rw [← cancel_epi r.hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← reassoc_of% h]
  simp only [← T.map_comp, prod_comp, Iso.hom_inv_id, ← prod_id,
    T.map_id, Category.comp_id]

private theorem tensorSquare_inverse
    {C : Type*} [Category C] (T : C × C ⥤ C)
    {A B V W X X' Y Y' : C} (p : X ≅ X') (q : Y ≅ Y')
    (a : A ≅ B) (f : W ≅ T.obj (X', Y'))
    (b : B ⟶ T.obj (X, Y)) (d : A ⟶ V) (e : V ⟶ W)
    (h : a.hom ≫ b ≫ T.map (Prod.mkHom p.hom q.hom) = d ≫ e ≫ f.hom) :
    a.inv ≫ d ≫ e = b ≫ T.map (Prod.mkHom p.hom (𝟙 Y)) ≫
        T.map (Prod.mkHom (𝟙 X') q.hom) ≫ f.inv := by
  rw [← T.map_comp_assoc]
  simp only [prod_comp, Category.comp_id, Category.id_comp]
  rw [← cancel_mono f.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h]
  simp only [Iso.inv_hom_id_assoc]

private theorem mapIso_cancel_left {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (e : X ≅ Y) {Z : D}
    (b : F.obj Y ⟶ Z) (c : F.obj X ⟶ Z) (h : b = F.map e.inv ≫ c) :
    F.map e.hom ≫ b = c := by
  rw [h, ← F.map_comp_assoc, e.hom_inv_id, F.map_id, Category.id_comp]

private theorem projection_comparison_of_squares
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (F : C₂ ⥤ C₁) (G : C₁ ⥤ C₂) (adj : F ⊣ G)
    (F' : D₂ ⥤ D₁) (G' : D₁ ⥤ D₂) (adj' : F' ⊣ G')
    (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)
    (T₁ : C₁ ⥤ C₁ ⥤ C₁) (T₂ : C₂ ⥤ C₂ ⥤ C₂)
    (S₁ : D₁ × D₁ ⥤ D₁) (S₂ : D₂ × D₂ ⥤ D₂)
    (p : F ⋙ E₁ ≅ E₂ ⋙ F') (q : G ⋙ E₂ ≅ E₁ ⋙ G')
    (c₁ : Functor.uncurry.obj T₁ ⋙ E₁ ≅ E₁.prod E₁ ⋙ S₁)
    (c₂ : Functor.uncurry.obj T₂ ⋙ E₂ ≅ E₂.prod E₂ ⋙ S₂)
    (δ : (Functor.postcompose₂.obj F).obj T₂ ⟶
      (((Functor.whiskeringLeft₂ C₁).obj F).obj F).obj T₁)
    (δ' : S₂ ⋙ F' ≅ F'.prod F' ⋙ S₁)
    (hδ : ∀ M N,
      E₁.map ((δ.app M).app N) ≫ c₁.hom.app (F.obj M, F.obj N) ≫
          S₁.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
        p.hom.app ((T₂.obj M).obj N) ≫ F'.map (c₂.hom.app (M, N)) ≫
          δ'.hom.app (E₂.obj M, E₂.obj N))
    (hCounit : ∀ A, adj'.counit.app (E₁.obj A) =
      F'.map (q.inv.app A) ≫ p.inv.app (G.obj A) ≫ E₁.map (adj.counit.app A))
    (K : C₁) (L : C₂) :
    E₂.map (adj.homEquiv _ _
        (((δ.app (G.obj K)).app L) ≫ (T₁.map (adj.counit.app K)).app (F.obj L))) ≫
        q.hom.app ((T₁.obj K).obj (F.obj L)) ≫
        G'.map (c₁.hom.app (K, F.obj L)) ≫
        G'.map (S₁.map (Prod.mkHom (𝟙 (E₁.obj K)) (p.hom.app L))) =
      c₂.hom.app (G.obj K, L) ≫
        S₂.map (Prod.mkHom (q.hom.app K) (𝟙 (E₂.obj L))) ≫
        derivedProjectionFormulaMate F' G' adj' S₂ S₁ δ' (E₁.obj K) (E₂.obj L) := by
  let d := Functor.curry.map δ'.hom ≫
    (Functor.curryObjProdComp F' F'
      S₁).hom
  let tX := curryComparison E₁
    T₁ S₁
    c₁.hom
  let tY := curryComparison E₂
    T₂ S₂
    c₂.hom
  have hs : ∀ M N,
      F'.map ((tY.app M).app N) ≫
        (d.app (E₂.obj M)).app
          (E₂.obj N) ≫
        ((Functor.curry.obj S₁).map
          (p.inv.app M)).app _ ≫
        ((Functor.curry.obj S₁).obj _).map
          (p.inv.app N) =
      p.inv.app _ ≫
        E₁.map ((δ.app M).app N) ≫
        (tX.app _).app _ := by
    intro M N
    change F'.map
        (c₂.hom.app (M, N)) ≫
      (δ'.hom.app
        (E₂.obj M,
          E₂.obj N) ≫ 𝟙 _) ≫
      S₁.map (Prod.mkHom (p.inv.app M) (𝟙 _)) ≫
      S₁.map (Prod.mkHom (𝟙 _) (p.inv.app N)) =
      p.inv.app _ ≫
        E₁.map ((δ.app M).app N) ≫
        c₁.hom.app
          (F.obj M, F.obj N)
    simp only [Category.comp_id]
    exact tensorSquare_right S₁
      (p.app M) (p.app N)
      (p.app
        ((T₂.obj M).obj N))
      (E₁.map ((δ.app M).app N))
      (c₁.hom.app
        (F.obj M, F.obj N))
      (F'.map (c₂.hom.app (M, N)))
      (δ'.hom.app
        (E₂.obj M, E₂.obj N))
      (hδ M N)
  have hc (A : C₁) :
      F'.map (q.hom.app A) ≫ adj'.counit.app (E₁.obj A) =
        p.inv.app (G.obj A) ≫ E₁.map (adj.counit.app A) :=
    mapIso_cancel_left F' (q.app A) _ _ (hCounit A)
  have h := Adjunction.rightAdjointProjectionMap_mate
    adj adj'
    (T₂ := Functor.curry.obj S₁) (S₂ := Functor.curry.obj S₂)
    (U := E₂) (V := E₁)
    δ d tY tX p.inv
    q.hom hs hc K L
  have hh := congrArg (fun q ↦ q ≫ G'.map
    (S₁.map (Prod.mkHom (𝟙 (E₁.obj K))
      (p.hom.app L)))) h
  dsimp only [tX, tY, curryComparison] at hh
  change (E₂.map ((adj.homEquiv _ _
        (((δ.app (G.obj K)).app L) ≫ (T₁.map (adj.counit.app K)).app (F.obj L)))) ≫
      q.hom.app _ ≫
      G'.map (c₁.hom.app
        (K, F.obj L))) ≫
      G'.map (S₁.map (Prod.mkHom (𝟙 _)
        (p.hom.app L))) =
    (c₂.hom.app (G.obj K, L) ≫
      S₂.map (Prod.mkHom (q.hom.app K) (𝟙 _)) ≫
      derivedProjectionFormulaMate F' G' adj' S₂ S₁ δ' (E₁.obj K)
        (E₂.obj L) ≫
      G'.map (S₁.map (Prod.mkHom (𝟙 _)
        (p.inv.app L)))) ≫
      G'.map (S₁.map (Prod.mkHom (𝟙 _)
        (p.hom.app L))) at hh
  simp only [Category.assoc, ← G'.map_comp,
    ← S₁.map_comp, prod_comp, Category.id_comp, Iso.inv_hom_id_app,
    ← prod_id] at hh
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id] at hh
  simpa only [Functor.id_obj, G'.map_comp] using hh

private theorem openProjection_comparison_of_squares
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (F : C₂ ⥤ C₁) (G : C₁ ⥤ C₂) (adj : G ⊣ F)
    (F' : D₂ ⥤ D₁) (G' : D₁ ⥤ D₂) (adj' : G' ⊣ F')
    (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)
    (T₁ : C₁ ⥤ C₁ ⥤ C₁) (T₂ : C₂ ⥤ C₂ ⥤ C₂)
    (S₁ : D₁ × D₁ ⥤ D₁) (S₂ : D₂ × D₂ ⥤ D₂)
    (p : F ⋙ E₁ ≅ E₂ ⋙ F') (q : G ⋙ E₂ ≅ E₁ ⋙ G')
    (c₁ : Functor.uncurry.obj T₁ ⋙ E₁ ≅ E₁.prod E₁ ⋙ S₁)
    (c₂ : Functor.uncurry.obj T₂ ⋙ E₂ ≅ E₂.prod E₂ ⋙ S₂)
    (δ : (Functor.postcompose₂.obj F).obj T₂ ⟶
      (((Functor.whiskeringLeft₂ C₁).obj F).obj F).obj T₁)
    [∀ M N, IsIso ((δ.app M).app N)]
    (δ' : S₂ ⋙ F' ≅ F'.prod F' ⋙ S₁)
    (hδ : ∀ M N,
      E₁.map ((δ.app M).app N) ≫ c₁.hom.app (F.obj M, F.obj N) ≫
          S₁.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
        p.hom.app ((T₂.obj M).obj N) ≫ F'.map (c₂.hom.app (M, N)) ≫
          δ'.hom.app (E₂.obj M, E₂.obj N))
    (hAdj : ∀ (M : C₁) (N : C₂) (r : G.obj M ⟶ N),
      adj'.homEquiv _ _ (q.inv.app M ≫ E₂.map r) =
        E₁.map (adj.homEquiv _ _ r) ≫ p.hom.app N)
    (K : C₁) (L : C₂) :
    E₂.map ((adj.homEquiv _ _).symm
        ((T₁.map (adj.unit.app K)).app (F.obj L) ≫
          inv ((δ.app (G.obj K)).app L))) ≫
        c₂.hom.app (G.obj K, L) ≫
        S₂.map (Prod.mkHom (q.hom.app K) (𝟙 (E₂.obj L))) =
      q.hom.app ((T₁.obj K).obj (F.obj L)) ≫
        G'.map (c₁.hom.app (K, F.obj L)) ≫
        G'.map (S₁.map (Prod.mkHom (𝟙 (E₁.obj K)) (p.hom.app L))) ≫
        ((adj'.homEquiv _ _).symm
          (S₁.map (Prod.mkHom (adj'.unit.app (E₁.obj K)) (𝟙 (F'.obj (E₂.obj L)))) ≫
            δ'.inv.app (G'.obj (E₁.obj K), E₂.obj L))) := by
  let : ∀ M, IsIso (δ.app M) :=
    fun M ↦ NatIso.isIso_of_isIso_app _
  let : IsIso δ := NatIso.isIso_of_isIso_app _
  let d₁ :
      (((Functor.whiskeringLeft₂ _).obj F).obj
        F).obj T₁ ⟶
      (Functor.postcompose₂.obj F).obj
        T₂ := inv δ
  let d₂ := (Functor.curryObjProdComp F'
      F' S₁).inv ≫
    Functor.curry.map δ'.inv
  let tU := curryComparison E₁
    T₁ S₁
    c₁.hom
  let tX := curryComparison E₂
    T₂ S₂
    c₂.hom
  have hb : ∀ A,
      adj'.unit.app (E₁.obj A) ≫
        F'.map (q.inv.app A) =
      E₁.map (adj.unit.app A) ≫
        p.hom.app (G.obj A) := by
    intro A
    have h := hAdj A _ (𝟙 (G.obj A))
    simp only [CategoryTheory.Functor.map_id, Adjunction.homEquiv_unit] at h
    erw [Category.comp_id, Category.comp_id] at h
    exact h
  have ht : ∀ M N,
      E₁.map ((d₁.app M).app N) ≫
        p.hom.app
          ((T₂.obj M).obj N) ≫
        F'.map ((tX.app M).app N) =
      (tU.app (F.obj M)).app
          (F.obj N) ≫
        ((Functor.curry.obj S₁).map (p.hom.app M)).app _ ≫
        ((Functor.curry.obj S₁).obj _).map
          (p.hom.app N) ≫
        (d₂.app (E₂.obj M)).app
          (E₂.obj N) := by
    intro M N
    dsimp only [tU, tX, curryComparison, d₁]
    simp only [NatIso.isIso_inv_app]
    change E₁.map (inv ((δ.app M).app N)) ≫
        p.hom.app _ ≫
        F'.map (c₂.hom.app (M, N)) =
      c₁.hom.app
          (F.obj M, F.obj N) ≫
        S₁.map (Prod.mkHom (p.hom.app M) (𝟙 _)) ≫
        S₁.map (Prod.mkHom (𝟙 _) (p.hom.app N)) ≫
        (𝟙 _ ≫ δ'.inv.app
          (E₂.obj M, E₂.obj N))
    simp only [Category.id_comp]
    exact tensorSquare_inverse S₁
      (p.app M) (p.app N)
      (E₁.mapIso (asIso ((δ.app M).app N)))
      (δ'.app
        (E₂.obj M, E₂.obj N))
      (c₁.hom.app
        (F.obj M, F.obj N))
      (p.hom.app
        ((T₂.obj M).obj N))
      (F'.map (c₂.hom.app (M, N)))
      (hδ M N)
  have h := Adjunction.projectionMap_mate
    adj adj'
    F F'
    (T₂ := Functor.curry.obj S₁) (T'₂ := Functor.curry.obj S₂)
    (U := E₁) (V := E₂)
    d₁ d₂ tU tX p.hom p.hom
    q.inv hb ht K L
  have hi : ((adj.projectionMap
        F T₁
        T₂ d₁).app K).app L =
      ((adj.homEquiv _ _).symm
        ((T₁.map (adj.unit.app K)).app (F.obj L) ≫
          inv ((δ.app (G.obj K)).app L))) := by
    rw [Adjunction.projectionMap_app_app, Adjunction.projectionMapTranspose_app_app]
    simp only [d₁, NatIso.isIso_inv_app]
    rfl
  have ho : ((adj'.projectionMap F'
        (Functor.curry.obj S₁) (Functor.curry.obj S₂) d₂).app
        (E₁.obj K)).app
        (E₂.obj L) =
      ((adj'.homEquiv _ _).symm
        (S₁.map (Prod.mkHom (adj'.unit.app (E₁.obj K)) (𝟙 (F'.obj (E₂.obj L)))) ≫
          δ'.inv.app (G'.obj (E₁.obj K), E₂.obj L))) := by
    rw [Adjunction.projectionMap_app_app, Adjunction.projectionMapTranspose_app_app]
    change (adj'.homEquiv _ _).symm
      (_ ≫ (𝟙 _ ≫ _)) = _
    rw [Category.id_comp]
    rfl
  rw [hi, ho] at h
  dsimp only [tU, tX, curryComparison] at h
  change q.inv.app _ ≫
      E₂.map (((adj.homEquiv _ _).symm
        ((T₁.map (adj.unit.app K)).app (F.obj L) ≫
          inv ((δ.app (G.obj K)).app L)))) ≫
      c₂.hom.app (G.obj K, L) =
    G'.map
        (c₁.hom.app (K, F.obj L)) ≫
      G'.map (S₁.map (Prod.mkHom (𝟙 _)
        (p.hom.app L))) ≫
      ((adj'.homEquiv _ _).symm
        (S₁.map (Prod.mkHom (adj'.unit.app (E₁.obj K)) (𝟙 (F'.obj (E₂.obj L)))) ≫
          δ'.inv.app (G'.obj (E₁.obj K), E₂.obj L))) ≫
      S₂.map (Prod.mkHom (q.inv.app K) (𝟙 _)) at h
  have hh := congrArg (fun w ↦ w ≫
    S₂.map (Prod.mkHom (q.hom.app K)
      (𝟙 (E₂.obj L)))) h
  simp only [Category.assoc, ← S₂.map_comp, prod_comp,
    Iso.inv_hom_id_app, Category.id_comp, ← prod_id] at hh
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hh
  rw [← cancel_epi (q.inv.app
    ((T₁.obj K).obj (F.obj L)))]
  simp only [Iso.inv_hom_id_app_assoc]
  simpa only [Functor.id_obj] using hh


private theorem unitSquare_of_mate
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₁) (adj : F ⊣ G)
    (F' : D₁ ⥤ D₂) (G' : D₂ ⥤ D₁) (adj' : F' ⊣ G')
    (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)
    (p : G ⋙ E₁ ≅ E₂ ⋙ G') (q : F ⋙ E₂ ≅ E₁ ⋙ F')
    (h : (mateEquiv adj adj' (.mk _ _ _ _ q.inv)).natTrans = p.hom) (M : C₁) :
    adj'.unit.app (E₁.obj M) ≫ G'.map (q.inv.app M) =
      E₁.map (adj.unit.app M) ≫ p.hom.app (F.obj M) := by
  exact (unit_mateEquiv adj adj' (.mk _ _ _ _ q.inv) M).symm.trans
    (congrArg (fun t : G ⋙ E₁ ⟶ E₂ ⋙ G' ↦
      E₁.map (adj.unit.app M) ≫ t.app (F.obj M)) h)

private theorem shifted_homEquiv_of_unitSquare
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    {F : C₁ ⥤ C₂} {G H : C₂ ⥤ C₁} (adj : F ⊣ G)
    {F' : D₁ ⥤ D₂} {G' : D₂ ⥤ D₁} (adj' : F' ⊣ G')
    {E₁ : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂}
    (i : H ≅ G) (p : G ⋙ E₁ ≅ E₂ ⋙ G') (q : E₁ ⋙ F' ⟶ F ⋙ E₂)
    (M : C₁) (N : C₂) (f : F.obj M ⟶ N)
    (hunit : adj'.unit.app (E₁.obj M) ≫ G'.map (q.app M) =
      E₁.map (adj.unit.app M) ≫ p.hom.app (F.obj M)) :
    adj'.homEquiv _ _ (q.app M ≫ E₂.map f) =
      E₁.map ((adj.ofNatIsoRight i.symm).homEquiv _ _ f) ≫
        (Functor.isoWhiskerRight i E₁ ≪≫ p).hom.app N := by
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  dsimp only [Iso.symm_hom, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  rw [← Functor.map_comp_assoc, Category.assoc, i.inv_hom_id_app,
    Category.comp_id]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, hunit, Category.assoc]
  have hn : E₁.map (G.map f) ≫ p.hom.app N =
      p.hom.app (F.obj M) ≫ G'.map (E₂.map f) := p.hom.naturality f
  rw [← hn]
  rw [← Category.assoc, ← E₁.map_comp]

private theorem symmetric_tensor_test {C : Type*} [Category C]
    (T : C → C → C) (Q : C → Prop) (swap : ∀ X Y, T X Y ≅ T Y X)
    (stable : ∀ {X Y}, Q X → (X ≅ Y) → Q Y) (K : C) :
    (∀ N, Q N → Q (T K N)) ↔ (∀ N, Q N → Q (T N K)) := by
  constructor
  · intro h N hN
    exact stable (h N hN) (swap K N)
  · intro h N hN
    exact stable (h N hN) (swap N K)

private theorem third_conjunct {P Q R S : Prop} (h : P ∧ Q ∧ R ∧ S) : R :=
  h.2.2.1

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Additivity, exactness, flatness and the two recorded K-flat definitions agree.
Source: Stacks 00YV, 03EK and 0G7E
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: use internal_section_tensor_comparison on the pulled-back coefficient ring.
It preserves kernels and cokernels on the unchanged abelian sheaf, hence is exact
and additive. The normalized tensor isomorphism conjugates the fixed-factor tensor
functors, giving flatness in both directions. Termwise it identifies the signed
total tensors and preserves and reflects acyclicity. Signed symmetry exchanges
P tensor N with N tensor P, relating IsKFlatModuleObject to the independent
coefficient sheaf definition. The quasi-inverse supplies every target acyclic test. -/
theorem ordinary_exact_flat_kflat (X : Scheme.{u}) :
    (equivalence Λ X).functor.Additive ∧
    exactFunctor _ _ (equivalence Λ X).functor ∧
    (∀ M : internalModules Λ X,
      exactFunctor _ _ (tensorRight M) ↔
        SheafOfModules.IsFlatOnSite ((equivalence Λ X).functor.obj M)) ∧
    (∀ P : CochainComplex (internalModules Λ X) ℤ,
      IsKFlatModuleObject X (CommMon.mk (condensedRingObj Λ X)) P ↔
        CochainComplex.IsKFlatIndependentCoefficients
          (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  have h := InternalAbelianSheafModule.internal_section_tensor_comparison.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  obtain ⟨e, e₀, hpure, hunit, hnat, hassoc, hl, hr, hb, ht, ha, hf, hk⟩ := h.2
  refine ⟨inferInstance, h.1, hf, ?_⟩
  intro P
  rw [← hk P]
  exact symmetric_tensor_test
    (fun A B : CochainComplex (internalModules Λ X) ℤ ↦ HomologicalComplex.tensorObj A B)
    (fun A ↦ A.Acyclic) (fun A B ↦ β_ A B) (fun {A B} h e ↦ h.of_iso e) P

set_option maxHeartbeats 800000 in
-- Comparing the two normalized monoidal witnesses elaborates the sheaf tensor constraints.
/-- The chosen ordinary tensor maps obey all symmetric-monoidal coherence diagrams.
Source: Stacks 03EK (blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: these are exactly the maps chosen from internal_section_tensor_comparison,
whose proof checks the naturality, associator, unitors and symmetry on local pure
tensors. The regular-unit comparison fixes local scalars, so the unit diagrams
are the scalar action laws. Local generation extends each equality to the sheaf. -/
theorem ordinary_monoidal (X : Scheme.{u}) :
    (∀ (M M' N N' : internalModules Λ X) (f : M ⟶ M') (g : N ⟶ N'),
      (equivalence Λ X).functor.map (f ⊗ₘ g) ≫
          (ordinaryTensorComparison Λ X M' N').hom =
        (ordinaryTensorComparison Λ X M N).hom ≫
          ((equivalence Λ X).functor.map f ⊗ₘ (equivalence Λ X).functor.map g)) ∧
    (∀ M N P : internalModules Λ X,
      (ordinaryTensorComparison Λ X (M ⊗ N) P).hom ≫
          (ordinaryTensorComparison Λ X M N).hom ▷ (equivalence Λ X).functor.obj P ≫
          (α_ _ _ _).hom =
        (equivalence Λ X).functor.map (α_ M N P).hom ≫
          (ordinaryTensorComparison Λ X M (N ⊗ P)).hom ≫
          (equivalence Λ X).functor.obj M ◁ (ordinaryTensorComparison Λ X N P).hom) ∧
    (∀ M : internalModules Λ X,
      (ordinaryTensorComparison Λ X (𝟙_ _) M).hom ≫
          (ordinaryUnitComparison Λ X).hom ▷ (equivalence Λ X).functor.obj M ≫
          (λ_ _).hom = (equivalence Λ X).functor.map (λ_ M).hom) ∧
    (∀ M : internalModules Λ X,
      (ordinaryTensorComparison Λ X M (𝟙_ _)).hom ≫
          (equivalence Λ X).functor.obj M ◁ (ordinaryUnitComparison Λ X).hom ≫
          (ρ_ _).hom = (equivalence Λ X).functor.map (ρ_ M).hom) ∧
    (∀ M N : internalModules Λ X,
      (ordinaryTensorComparison Λ X M N).hom ≫ (β_ _ _).hom =
        (equivalence Λ X).functor.map (β_ M N).hom ≫
          (ordinaryTensorComparison Λ X N M).hom) := by
  have h := InternalAbelianSheafModule.internal_section_tensor_comparison.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  refine Exists.elim h.2 (fun e h₁ ↦ ?_)
  refine Exists.elim h₁ (fun e₀ hs ↦ ?_)
  have he : e = ordinaryTensorComparison Λ X := by
    funext M N
    exact (ordinaryTensorComparison_existsUnique Λ X M N).unique (hs.1 M N)
      (ordinaryTensorComparison_existsUnique Λ X M N).exists.choose_spec
  have he₀ : e₀ = ordinaryUnitComparison Λ X :=
    (ordinaryUnitComparison_existsUnique Λ X).unique hs.2.1
      (ordinaryUnitComparison_existsUnique Λ X).exists.choose_spec
  have hc := And.intro hs.2.2.1 (And.intro hs.2.2.2.1
    (And.intro hs.2.2.2.2.1 (And.intro hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1)))
  simp only [← he, ← he₀, equivalence] at hc ⊢
  -- The kernel checks this existing proof directly; elaborator conversion unfolds the
  -- large sheaf associator a second time and exceeds the single-file compilation limit.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `hc
      | Lean.throwError "missing coherence proof"
    (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

variable [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]

/-- The specified internal derived tensor map is invertible.
Source: Stacks 07A4 (blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: resolve both factors by flat-term K-flat complexes. The ordinary pullback
mate is invertible on every pair of modules, so its signed total is invertible.
Pullback preserves flat modules and acyclic complexes, hence these resolutions
compute all three derived tensors and their specified comparison. Localization
and naturality give invertibility on arbitrary unbounded derived objects. -/
@[instance] theorem internalDelta_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    IsIso (((internalDelta Λ f).app M).app N) := by
  let _ := (inferInstance : ∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X))
  unfold internalDelta
  infer_instance

/-- The actual module-object proper projection arrow, the adjoint of counit after delta.
Source: Stacks 0B56 (blueprint: lem-pd-module-ringed-topos-derived-comparison). -/
def internalProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (internalModules Λ X)) (L : DerivedCategory (internalModules Λ Y)) :
    ((CondensedRing.derivedTensor Λ Y).obj ((internalDerivedPushforward Λ f).obj K)).obj L ⟶
      (internalDerivedPushforward Λ f).obj
        (((CondensedRing.derivedTensor Λ X).obj K).obj ((internalDerivedPullback Λ f).obj L)) :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _
    (((internalDelta Λ f).app ((internalDerivedPushforward Λ f).obj K)).app L ≫
      (((CondensedRing.derivedTensor Λ X).map
        ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).counit.app K)).app
          ((internalDerivedPullback Λ f).obj L)))

/-- The precise ringed projection mate alpha, in the dependency's uncurried interface.
Source: Stacks 0B56 (blueprint: lem-pd-module-ringed-topos-derived-comparison). -/
def projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (modules Λ X)) (L : DerivedCategory (modules Λ Y)) :
    (tensor Λ Y).obj ((derivedPushforward Λ f).obj K, L) ⟶
      (derivedPushforward Λ f).obj ((tensor Λ X).obj (K, (derivedPullback Λ f).obj L)) :=
  derivedProjectionFormulaMate (derivedPullback Λ f) (derivedPushforward Λ f)
    (derivedAdjunction Λ f) (tensor Λ Y) (tensor Λ X) (tensorPullComparison Λ f) K L

/-- Equality of the specified derived Hom bijections; thus both units and counits agree.
Source: Stacks 07A6 and Derived Categories 09T5
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: derive the two equal ordinary Hom bijections on K-flat and K-injective
resolutions. The comparisons in derivedPullComparison and derivedPushComparison
are the canonical resolution comparisons, so uniqueness of derived adjunctions
gives this equality on all objects. Applying it to identities gives the unit
and counit statements. -/
theorem derived_homEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (internalModules Λ Y)) (N : DerivedCategory (internalModules Λ X))
    (q : (internalDerivedPullback Λ f).obj M ⟶ N) :
    (derivedAdjunction Λ f).homEquiv _ _
        ((derivedPullComparison Λ f).inv.app M ≫ (derivedEquivalence Λ X).functor.map q) =
      (derivedEquivalence Λ Y).functor.map
        ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _ q) ≫
          (derivedPushComparison Λ f).hom.app N := by
  exact (sectionDerivedPushpullNormalization Λ f).2.2.2.2.2.2.1 M N q

/-- Equality of the actual oplax tensor natural transformations under comparison.
Inverting this equation identifies the actual lax maps as well.
Source: Stacks 07A4 (blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: the normalized underived maps both send s tensor (m tensor n) to
(s tensor m) tensor (1 tensor n). Apply this equality to flat-term K-flat
representatives and totalize with the same signs. The representative square in
tensorPullComparison_existsUnique and uniqueness of two-variable derived tensor
in lem-weil-pbc-site-derived-tensor-descent give the equation on every pair. -/
theorem delta_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    (derivedEquivalence Λ X).functor.map (((internalDelta Λ f).app M).app N) ≫
        (tensorComparison Λ X).hom.app
          ((internalDerivedPullback Λ f).obj M,
            (internalDerivedPullback Λ f).obj N) ≫
        (tensor Λ X).map (Prod.mkHom
          ((derivedPullComparison Λ f).hom.app M) ((derivedPullComparison Λ f).hom.app N)) =
      (derivedPullComparison Λ f).hom.app (((CondensedRing.derivedTensor Λ Y).obj M).obj N) ≫
        (derivedPullback Λ f).map ((tensorComparison Λ Y).hom.app (M, N)) ≫
        (tensorPullComparison Λ f).hom.app
          ((derivedEquivalence Λ Y).functor.obj M, (derivedEquivalence Λ Y).functor.obj N) := by
  exact third_conjunct (section_derived_tensor_normalization Λ f) M N

/-- The actual lax tensor map is the inverse of the localized strong oplax map.
Source: Stacks 07A4 (blueprint: lem-pd-module-ringed-topos-derived-comparison). -/
def internalMu {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    ((CondensedRing.derivedTensor Λ X).obj ((internalDerivedPullback Λ f).obj M)).obj
        ((internalDerivedPullback Λ f).obj N) ⟶
      (internalDerivedPullback Λ f).obj (((CondensedRing.derivedTensor Λ Y).obj M).obj N) :=
  inv (((internalDelta Λ f).app M).app N)

/-- Equality for the actual lax map mu and the inverse canonical ringed tensor map.
Source: Stacks 07A4 (blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: invert the square in delta_comparison. Both transformations are strong,
so their lax maps are precisely the inverses of their specified oplax maps.
The inverse of the tensor of comparison isomorphisms is the tensor of their
inverses; functors preserve inverses. This gives the displayed equation. -/
theorem mu_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    (tensor Λ X).map (Prod.mkHom ((derivedPullComparison Λ f).inv.app M)
        ((derivedPullComparison Λ f).inv.app N)) ≫
        (tensorComparison Λ X).inv.app
          ((internalDerivedPullback Λ f).obj M,
            (internalDerivedPullback Λ f).obj N) ≫
        (derivedEquivalence Λ X).functor.map (internalMu Λ f M N) =
      (tensorPullComparison Λ f).inv.app
          ((derivedEquivalence Λ Y).functor.obj M, (derivedEquivalence Λ Y).functor.obj N) ≫
        (derivedPullback Λ f).map ((tensorComparison Λ Y).inv.app (M, N)) ≫
        (derivedPullComparison Λ f).inv.app (((CondensedRing.derivedTensor Λ Y).obj M).obj N) := by
  have h :
      (derivedEquivalence Λ X).functor.mapIso (asIso (((internalDelta Λ f).app M).app N)) ≪≫
          (tensorComparison Λ X).app
            ((internalDerivedPullback Λ f).obj M, (internalDerivedPullback Λ f).obj N) ≪≫
          (tensor Λ X).mapIso (Iso.prod ((derivedPullComparison Λ f).app M)
            ((derivedPullComparison Λ f).app N)) =
        (derivedPullComparison Λ f).app (((CondensedRing.derivedTensor Λ Y).obj M).obj N) ≪≫
          (derivedPullback Λ f).mapIso ((tensorComparison Λ Y).app (M, N)) ≪≫
          (tensorPullComparison Λ f).app
            ((derivedEquivalence Λ Y).functor.obj M, (derivedEquivalence Λ Y).functor.obj N) :=
    Iso.ext (delta_comparison Λ f M N)
  simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.prod_inv, Iso.app_inv,
    asIso_inv, internalMu, Category.assoc] using congrArg Iso.inv h

set_option maxHeartbeats 1600000 in
-- The comparison instances contain large sheaf tensor constraints.
/-- The module-object proper projection is the precise ringed projection mate alpha.
This statement makes no invertibility assertion about the projection arrow.
Source: Stacks 0B56 (blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: derived_homEquiv identifies the specified Hom bijection and counit, and
delta_comparison identifies its tensor arrow. Their composite therefore has the
same adjoint transpose, which is exactly derivedProjectionFormulaMate used in
ringedProjectionMateExact. Naturality and unit normalization follow from the same
identifications and the adjunction triangle identities. -/
theorem projection_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (internalModules Λ X)) (L : DerivedCategory (internalModules Λ Y)) :
    (derivedEquivalence Λ Y).functor.map (internalProjection Λ f K L) ≫
        (derivedPushComparison Λ f).hom.app
          (((CondensedRing.derivedTensor Λ X).obj K).obj ((internalDerivedPullback Λ f).obj L)) ≫
        (derivedPushforward Λ f).map ((tensorComparison Λ X).hom.app
          (K, (internalDerivedPullback Λ f).obj L)) ≫
        (derivedPushforward Λ f).map ((tensor Λ X).map (Prod.mkHom
          (𝟙 ((derivedEquivalence Λ X).functor.obj K))
          ((derivedPullComparison Λ f).hom.app L))) =
      (tensorComparison Λ Y).hom.app
          ((internalDerivedPushforward Λ f).obj K, L) ≫
        (tensor Λ Y).map (Prod.mkHom ((derivedPushComparison Λ f).hom.app K)
          (𝟙 ((derivedEquivalence Λ Y).functor.obj L))) ≫
        projection Λ f ((derivedEquivalence Λ X).functor.obj K)
          ((derivedEquivalence Λ Y).functor.obj L) := by
  exact projection_comparison_of_squares
    (internalDerivedPullback Λ f) (internalDerivedPushforward Λ f)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f)
    (derivedPullback Λ f) (derivedPushforward Λ f) (derivedAdjunction Λ f)
    (derivedEquivalence Λ X).functor (derivedEquivalence Λ Y).functor
    (CondensedRing.derivedTensor Λ X) (CondensedRing.derivedTensor Λ Y)
    (tensor Λ X) (tensor Λ Y) (derivedPullComparison Λ f) (derivedPushComparison Λ f)
    (tensorComparison Λ X) (tensorComparison Λ Y) (internalDelta Λ f)
    (tensorPullComparison Λ f) (delta_comparison Λ f)
    ((sectionDerivedPushpullNormalization Λ f).2.2.2.2.2.2.2.2.1) K L


set_option maxHeartbeats 800000 in
-- Comparing the two localized mate squares elaborates the section-module constraints.
/-- Equality of the specified open Hom bijections, hence of their units and counits.
Source: Stacks 03DI and 03DJ
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: the comparison inserts the section equivalence unit into the same linearized
extension-by-zero functor. The sheaf open adjunction is unchanged on underlying maps.
The ordinary adjunction triangles give the Hom equality, and applying localization
preserves that equality since both functors are exact. Evaluate at identities for
units and counits. -/
theorem open_homEquiv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : DerivedCategory (internalModules Λ U)) (N : DerivedCategory (internalModules Λ X))
    (q : (internalDerivedExtension Λ j).obj M ⟶ N) :
    (derivedOpenAdjunction Λ j).homEquiv _ _
        ((derivedExtensionComparison Λ j).inv.app M ≫
          (derivedEquivalence Λ X).functor.map q) =
      (derivedEquivalence Λ U).functor.map ((internalOpenAdjunction Λ j).homEquiv _ _ q) ≫
        (derivedPullComparison Λ j).hom.app N := by
  have hunit := Adjunction.mapDerivedCategoryAdjunction_mate
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
    (openAdjunction Λ j) (pullComparison Λ j) (extensionComparison Λ j).symm
    (unitSquare_of_mate
      (CondensedRing.openImmersionLowerShriek Λ j) (CondensedRing.upperStar Λ j)
      (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
      (extension Λ j) (pullback Λ j) (openAdjunction Λ j)
      (equivalence Λ U).functor (equivalence Λ X).functor
      (pullComparison Λ j) (extensionComparison Λ j)
      (InternalModuleOperations.openComparison_existsUnique Λ j).exists.choose_spec) M
  have he : (derivedExtensionComparison Λ j).inv =
      (Functor.mapDerivedCategorySquareIso (extensionComparison Λ j).symm).hom := by
    simp only [derivedExtensionComparison, Functor.mapDerivedCategorySquareIso,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  have hh := shifted_homEquiv_of_unitSquare
    (C₁ := DerivedCategory (internalModules Λ U))
    (C₂ := DerivedCategory (internalModules Λ X))
    (D₁ := DerivedCategory (modules Λ U)) (D₂ := DerivedCategory (modules Λ X))
    (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
    (derivedOpenAdjunction Λ j)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ j)
    (Functor.mapDerivedCategorySquareIso (pullComparison Λ j))
    (Functor.mapDerivedCategorySquareIso (extensionComparison Λ j).symm).hom
    M N q hunit
  simp only [he, derivedOpenAdjunction, internalOpenAdjunction,
    CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction,
    derivedPullComparison, derivedEquivalence, derivedFunctor, derivedPullback,
    Functor.asEquivalence, equivalence, InternalModuleOperations.equivalence] at hh ⊢
  exact hh

/-- The actual internal adjoint-of-unit open projection arrow, using inverse delta.
Source: Stacks 03DJ and 0B56
(blueprint: lem-pd-module-ringed-topos-derived-comparison). -/
def internalOpenProjection {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (internalModules Λ U)) (L : DerivedCategory (internalModules Λ X)) :
    (internalDerivedExtension Λ j).obj
        (((CondensedRing.derivedTensor Λ U).obj K).obj ((internalDerivedPullback Λ j).obj L)) ⟶
      ((CondensedRing.derivedTensor Λ X).obj ((internalDerivedExtension Λ j).obj K)).obj L :=
  ((internalOpenAdjunction Λ j).homEquiv _ _).symm
    ((((CondensedRing.derivedTensor Λ U).map
        ((internalOpenAdjunction Λ j).unit.app K)).app ((internalDerivedPullback Λ j).obj L)) ≫
      inv (((internalDelta Λ j).app
        ((internalDerivedExtension Λ j).obj K)).app L))

/-- The ringed adjoint-of-unit open projection arrow, using inverse canonical delta.
Source: Stacks 03DJ and 0B56
(blueprint: lem-pd-module-ringed-topos-derived-comparison). -/
def openProjection {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (modules Λ U)) (L : DerivedCategory (modules Λ X)) :
    (derivedExtension Λ j).obj ((tensor Λ U).obj (K, (derivedPullback Λ j).obj L)) ⟶
      (tensor Λ X).obj ((derivedExtension Λ j).obj K, L) :=
  ((derivedOpenAdjunction Λ j).homEquiv _ _).symm
    ((tensor Λ U).map (Prod.mkHom ((derivedOpenAdjunction Λ j).unit.app K)
        (𝟙 ((derivedPullback Λ j).obj L))) ≫
      (tensorPullComparison Λ j).inv.app ((derivedExtension Λ j).obj K, L))

set_option maxHeartbeats 1600000 in
-- The curried tensor and derived adjunction interfaces have large instance arguments.
/-- Equality of the actual adjoint-of-unit open projection morphisms.
Source: Stacks 03DJ and 0B56
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: open_homEquiv identifies the specified unit, and delta_comparison identifies
its inverse, the actual lax map mu. Naturality of the tensor and extension
comparisons identifies their composite. Taking the specified open adjoint transpose
gives precisely the displayed equality, without choosing another projection map. -/
theorem openProjection_comparison {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (internalModules Λ U)) (L : DerivedCategory (internalModules Λ X)) :
    (derivedEquivalence Λ X).functor.map (internalOpenProjection Λ j K L) ≫
        (tensorComparison Λ X).hom.app
          ((internalDerivedExtension Λ j).obj K, L) ≫
        (tensor Λ X).map (Prod.mkHom ((derivedExtensionComparison Λ j).hom.app K)
          (𝟙 ((derivedEquivalence Λ X).functor.obj L))) =
      (derivedExtensionComparison Λ j).hom.app
          (((CondensedRing.derivedTensor Λ U).obj K).obj ((internalDerivedPullback Λ j).obj L)) ≫
        (derivedExtension Λ j).map ((tensorComparison Λ U).hom.app
          (K, (internalDerivedPullback Λ j).obj L)) ≫
        (derivedExtension Λ j).map ((tensor Λ U).map (Prod.mkHom
          (𝟙 ((derivedEquivalence Λ U).functor.obj K))
          ((derivedPullComparison Λ j).hom.app L))) ≫
        openProjection Λ j ((derivedEquivalence Λ U).functor.obj K)
          ((derivedEquivalence Λ X).functor.obj L) := by
  exact openProjection_comparison_of_squares
    (internalDerivedPullback Λ j) (internalDerivedExtension Λ j) (internalOpenAdjunction Λ j)
    (derivedPullback Λ j) (derivedExtension Λ j) (derivedOpenAdjunction Λ j)
    (derivedEquivalence Λ U).functor (derivedEquivalence Λ X).functor
    (CondensedRing.derivedTensor Λ U) (CondensedRing.derivedTensor Λ X)
    (tensor Λ U) (tensor Λ X) (derivedPullComparison Λ j) (derivedExtensionComparison Λ j)
    (tensorComparison Λ U) (tensorComparison Λ X) (internalDelta Λ j)
    (tensorPullComparison Λ j) (delta_comparison Λ j) (open_homEquiv Λ j) K L
/-- Pullback composition is identified with the canonical ringed pasting comparison.
Source: Stacks 03D7 and 07A6
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: the internal composition comparison is the localization of inverse-image
pasting followed by the compatible coefficient isomorphisms alpha. Under E this is
the same scalar-extension pasting map for ringed modules. Its Hom adjunction
characterization and K-flat normalization determine it uniquely. Essential
surjectivity of D(E_Z) extends the equation to all ringed derived objects. -/
theorem composition_comparison {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ M : DerivedCategory (internalModules Λ Z),
        (derivedPullComparison Λ (f ≫ g)).hom.app M ≫
            (derivedPullbackComposition Λ f g).hom.app ((derivedEquivalence Λ Z).functor.obj M) =
          (derivedEquivalence Λ X).functor.map
              ((CondensedRing.leftDerivedUpperStarComp Λ f g).hom.app M) ≫
            (derivedPullComparison Λ f).hom.app
              ((internalDerivedPullback Λ g).obj M) ≫
            (derivedPullback Λ f).map ((derivedPullComparison Λ g).hom.app M) := by
  exact (sectionDerivedPushpullNormalization Λ f).2.2.2.2.2.2.2.2.2.1 g

/-- The specified derived tensor transformation comparison in the paper's field setting.
Together with ordinary_exact_flat_kflat, ordinary_monoidal, tensor_representatives,
derived_homEquiv, composition_comparison, projection_comparison, open_homEquiv and
openProjection_comparison, this states every clause of the comparison lemma.
Source: Stacks 00YV, 03EK, 03D7, 03DJ, 07A4, 07A6 and 0B56
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: construct the sectionwise equivalence and its normalized ordinary tensor
maps, and identify signed total complexes and the two K-flat tests. Localize on
K-flat and K-injective representatives, identifying the specified adjunction Hom
bijections and composition pasting. The ordinary pure-tensor formula identifies
actual delta, and its inverse identifies actual mu. Transpose counit after delta
for the proper projection map. For an open immersion, localize the exact extension
by zero and transpose unit followed by mu. These are precisely the equalities
stated in the named clauses above; see their proof plans for the individual steps. -/
theorem module_ringed_topos_derived_comparison
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hne : p ≠ ℓ)
    {X Y : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y.left)) :
    (derivedEquivalence Λ X.left).functor.map (((internalDelta Λ f.left).app M).app N) ≫
        (tensorComparison Λ X.left).hom.app
          ((internalDerivedPullback Λ f.left).obj M,
            (internalDerivedPullback Λ f.left).obj N) ≫
        (tensor Λ X.left).map (Prod.mkHom
          ((derivedPullComparison Λ f.left).hom.app M)
          ((derivedPullComparison Λ f.left).hom.app N)) =
      (derivedPullComparison Λ f.left).hom.app
          (((CondensedRing.derivedTensor Λ Y.left).obj M).obj N) ≫
        (derivedPullback Λ f.left).map ((tensorComparison Λ Y.left).hom.app (M, N)) ≫
        (tensorPullComparison Λ f.left).hom.app
          ((derivedEquivalence Λ Y.left).functor.obj M,
            (derivedEquivalence Λ Y.left).functor.obj N) := by
  exact delta_comparison Λ f.left M N

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
