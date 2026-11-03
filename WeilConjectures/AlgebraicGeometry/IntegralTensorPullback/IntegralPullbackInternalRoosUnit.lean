/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralTensorPullback.IntegralTensorPullbackData

import all WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.WeilObject.Sheaf.StalkUnit

/-! # Ordinary pullback and the actual completion augmentation

Source: blueprint det-lem-int-tensor-pullback, first paragraph; Stacks 099M.
(blueprint: lem-sfb-internal-pullback-roos-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralTensorPullback
attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar
  Mod.extendScalarsIsoComapInv
private def tensorSquareIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {N : C} {N' : D} (e : F.obj N ≅ N') :
    tensorRight N ⋙ F ≅ F ⋙ tensorRight N' :=
  (Functor.Monoidal.commTensorRight F N).symm ≪≫
    Functor.isoWhiskerLeft F ((tensoringRight D).mapIso e)

private theorem tensorSquareIso_natural
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {N₁ N₂ : C} {N₁' N₂' : D}
    (e₁ : F.obj N₁ ≅ N₁') (e₂ : F.obj N₂ ≅ N₂')
    (f : N₁ ⟶ N₂) (f' : N₁' ⟶ N₂')
    (h : F.map f ≫ e₂.hom = e₁.hom ≫ f') (M : C) :
    F.map (M ◁ f) ≫ (tensorSquareIso F e₂).hom.app M =
      (tensorSquareIso F e₁).hom.app M ≫ F.obj M ◁ f' := by
  change F.map (M ◁ f) ≫ (Functor.OplaxMonoidal.δ F M N₂ ≫ F.obj M ◁ e₂.hom) =
    (Functor.OplaxMonoidal.δ F M N₁ ≫ F.obj M ◁ e₁.hom) ≫ F.obj M ◁ f'
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc,
    ← whiskerLeft_comp, Category.assoc, ← whiskerLeft_comp, h]

private theorem tensorSquareIso_unit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {N : C} {N' : D} (e : F.obj N ≅ N')
    (q : 𝟙_ C ⟶ N) (q' : 𝟙_ D ⟶ N')
    (h : F.map q ≫ e.hom = (Functor.Monoidal.εIso F).inv ≫ q') (M : C) :
    F.map ((ρ_ M).inv ≫ M ◁ q) ≫ (tensorSquareIso F e).hom.app M =
      (ρ_ (F.obj M)).inv ≫ F.obj M ◁ q' := by
  change F.map ((ρ_ M).inv ≫ M ◁ q) ≫
      (Functor.OplaxMonoidal.δ F M N ≫ F.obj M ◁ e.hom) = _
  rw [Functor.map_comp, Category.assoc,
    ← Functor.OplaxMonoidal.δ_natural_right_assoc, ← whiskerLeft_comp, h]
  simp only [Functor.Monoidal.map_rightUnitor_inv, whiskerLeft_comp,
    Category.assoc, Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.εIso_inv,
    Functor.Monoidal.whiskerLeft_ε_η_assoc]

private theorem quotientUnit_comp
    {B C D : Type*} [Category B] [Category C] [Category D]
    (F : C ⥤ D) (G : B ⥤ C) (H : B ⥤ D) (e : G ⋙ F ≅ H)
    (R : B) {U : C} {U' : D} (s : G.obj R ≅ U) (s' : H.obj R ≅ U')
    (η : F.obj U ⟶ U') (he : e.hom.app R = F.map s.hom ≫ η ≫ s'.inv)
    {N : B} (q : R ⟶ N) :
    F.map (s.inv ≫ G.map q) ≫ e.hom.app N = η ≫ s'.inv ≫ H.map q := by
  have hn := e.hom.naturality q
  dsimp only [Functor.comp_map] at hn
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc, he,
    ← Functor.map_comp_assoc, Iso.inv_hom_id]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]

private theorem productIso_natural
    {C : Type*} [Category C] [Preadditive C] [HasCountableProducts C]
    {K K' : ℕ → C} (f : ∀ n, K (n + 1) ⟶ K n)
    (f' : ∀ n, K' (n + 1) ⟶ K' n) (e : ∀ n, K n ≅ K' n)
    (h : ∀ n, (e (n + 1)).hom ≫ f' n = f n ≫ (e n).hom) :
    (Pi.mapIso e).hom ≫ towerTransitionEndomorphism f' =
      towerTransitionEndomorphism f ≫ (Pi.mapIso e).hom := by
  exact towerTransitionEndomorphism_natural_backward f f' (fun n ↦ (e n).hom) h

private theorem productIso_lift
    {C : Type*} [Category C] [HasCountableProducts C] {P : C}
    {K K' : ℕ → C} (e : ∀ n, K n ≅ K' n)
    (c : ∀ n, P ⟶ K n) (c' : ∀ n, P ⟶ K' n)
    (h : ∀ n, c n ≫ (e n).hom = c' n) :
    Pi.lift c ≫ (Pi.mapIso e).hom = Pi.lift c' := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, Pi.mapIso_hom_π, Pi.lift_π_assoc, Pi.lift_π]
  exact h n

private def roosIso
    {C : Type*} [Category C] [Abelian C] {V V' : CochainComplex C ℤ}
    (t : V ⟶ V) (t' : V' ⟶ V') (a : V ≅ V') (ht : a.hom ≫ t' = t ≫ a.hom) :
    CochainComplex.mappingCocone t ≅ AdicCompletion.genericRoos V' t' :=
  AdicCompletion.genericCoconeIso V t ≪≫
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ biprod.mapIso
        ((HomologicalComplex.eval _ _ i).mapIso a)
        ((HomologicalComplex.eval _ _ (i - 1)).mapIso a)) (by
      intro i j hij
      obtain rfl : i + 1 = j := hij
      change biprod.map (a.hom.f i) (a.hom.f (i - 1)) ≫
          (AdicCompletion.genericRoos V' t').d i (i + 1) =
        (AdicCompletion.genericRoos V t).d i (i + 1) ≫
          biprod.map (a.hom.f (i + 1)) (a.hom.f (i + 1 - 1))
      simpa only [AdicCompletion.genericRoos, CochainComplex.of_d] using
        AdicCompletion.genericRoosMap_comm t t' a.hom ht i)

private theorem roosIso_lift
    {C : Type*} [Category C] [Abelian C] {P V V' : CochainComplex C ℤ}
    (t : V ⟶ V) (t' : V' ⟶ V') (a : V ≅ V') (ht : a.hom ≫ t' = t ≫ a.hom)
    (c : P ⟶ V) (c' : P ⟶ V') (hc : c ≫ a.hom = c')
    (h : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P V (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (c ≫ t) = 0)
    (α : P ⟶ AdicCompletion.genericRoos V' t')
    (hα : ∀ i, α.f i = biprod.lift (c'.f i) 0) :
    CochainComplex.mappingCocone.lift t c 0 h ≫ (roosIso t t' a ht).hom = α := by
  ext i : 1
  rw [hα i]
  change (CochainComplex.mappingCocone.lift t c 0 h).f i ≫
      (biprod.lift ((CochainComplex.mappingCocone.fst t).f i)
        (-(CochainComplex.mappingCocone.snd t).v i (i - 1) (by omega)) ≫
      biprod.map (a.hom.f i) (a.hom.f (i - 1))) = biprod.lift (c'.f i) 0
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc,
      biprod.lift_fst, CochainComplex.mappingCocone.lift_f_fst_f_assoc]
    simpa only [HomologicalComplex.comp_f] using congrArg (fun f ↦ f.f i) hc
  · simp [Category.assoc]

private abbrev pointUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] :=
  @MonoidalCategoryStruct.tensorUnit
    (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) _
    MonoidalCategory.toMonoidalCategoryStruct

private def pointRegularIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) :=
  (Functor.Monoidal.εIso (CondensedRing.upperStarFromPointMod Λ X)).symm

private theorem pointRegularIso_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) :
    pointRegularIso Λ X = eqToIso (show
      (CondensedRing.upperStarFromPointMod Λ X).obj (Mod.regular Λ) =
        Mod.regular (condensedRingObj Λ X) from rfl) := by
  apply Iso.ext
  apply Mod.hom_ext
  rfl

private theorem pointUnitHom_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) :
    (Functor.Monoidal.εIso (CondensedRing.upperStarFromPointMod Λ X)).hom =
      (eqToIso (show
        (CondensedRing.upperStarFromPointMod Λ X).obj (Mod.regular Λ) =
          Mod.regular (condensedRingObj Λ X) from rfl)).inv := by
  exact congrArg Iso.inv (pointRegularIso_eq Λ X)

private theorem pointQuotientUnit_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    {N : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ}
    (q : pointUnit Λ ⟶ N) :
    (CondensedRing.upperStar Λ g).map
        ((Functor.Monoidal.εIso (CondensedRing.upperStarFromPointMod Λ Y)).hom ≫
          (CondensedRing.upperStarFromPointMod Λ Y).map q) ≫
      (CondensedRing.upperStarFromPointModComp Λ g).hom.app N =
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ g)).inv ≫
      (Functor.Monoidal.εIso (CondensedRing.upperStarFromPointMod Λ X)).hom ≫
        (CondensedRing.upperStarFromPointMod Λ X).map q := by
  exact quotientUnit_comp (CondensedRing.upperStar Λ g)
    (CondensedRing.upperStarFromPointMod Λ Y) (CondensedRing.upperStarFromPointMod Λ X)
    (CondensedRing.upperStarFromPointModComp Λ g)
    (@MonoidalCategoryStruct.tensorUnit
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) _
      MonoidalCategory.toMonoidalCategoryStruct)
    (Functor.Monoidal.εIso (CondensedRing.upperStarFromPointMod Λ Y)).symm
    (Functor.Monoidal.εIso (CondensedRing.upperStarFromPointMod Λ X)).symm
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ g)).inv
    (CondensedRing.upperStarFromPointModComp_hom_app_unit Λ g) q

private def regularPointIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) :
    ((upperStarFromPoint X).mapMod Λ).obj (Mod.regular Λ) ≅
      Mod.regular (condensedRingObj Λ X) := eqToIso (by rfl)

private theorem regularQuotientUnit_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    {N : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ}
    (q : Mod.regular Λ ⟶ N) :
    (CondensedRing.upperStar Λ g).map
        ((regularPointIso Λ Y).inv ≫ ((upperStarFromPoint Y).mapMod Λ).map q) ≫
      (CondensedRing.upperStarFromPointModComp Λ g).hom.app N =
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ g)).inv ≫
      (regularPointIso Λ X).inv ≫ ((upperStarFromPoint X).mapMod Λ).map q := by
  have h := pointQuotientUnit_comp Λ g q
  rw [pointUnitHom_eq, pointUnitHom_eq] at h
  simpa only [regularPointIso, CondensedRing.upperStarFromPointMod] using h

private theorem regularQuotientUnit_comp_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (sY : ((upperStarFromPoint Y).mapMod Λ).obj (Mod.regular Λ) ≅
      Mod.regular (condensedRingObj Λ Y))
    (sX : ((upperStarFromPoint X).mapMod Λ).obj (Mod.regular Λ) ≅
      Mod.regular (condensedRingObj Λ X))
    (hsY : sY = regularPointIso Λ Y) (hsX : sX = regularPointIso Λ X)
    {N : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ}
    (q : Mod.regular Λ ⟶ N) :
    (CondensedRing.upperStar Λ g).map
        (sY.inv ≫ ((upperStarFromPoint Y).mapMod Λ).map q) ≫
      (CondensedRing.upperStarFromPointModComp Λ g).hom.app N =
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ g)).inv ≫
      sX.inv ≫ ((upperStarFromPoint X).mapMod Λ).map q := by
  subst sY
  subst sX
  exact regularQuotientUnit_comp Λ g q

private theorem regularUnit_comp_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (sY : ((upperStarFromPoint Y).mapMod Λ).obj (Mod.regular Λ) ≅
      Mod.regular (condensedRingObj Λ Y))
    (sX : ((upperStarFromPoint X).mapMod Λ).obj (Mod.regular Λ) ≅
      Mod.regular (condensedRingObj Λ X))
    (hsY : sY = regularPointIso Λ Y) (hsX : sX = regularPointIso Λ X) :
    (CondensedRing.upperStar Λ g).map sY.inv ≫
      (CondensedRing.upperStarFromPointModComp Λ g).hom.app (Mod.regular Λ) =
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ g)).inv ≫ sX.inv := by
  have h := regularQuotientUnit_comp_of_iso Λ g sY sX hsY hsX (𝟙 (Mod.regular Λ))
  have hY := ((upperStarFromPoint Y).mapMod Λ).map_id (Mod.regular Λ)
  have hX := ((upperStarFromPoint X).mapMod Λ).map_id (Mod.regular Λ)
  rw [hY, hX, Category.comp_id, Category.comp_id] at h
  exact h

private theorem regularUnit_comp_of_data
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (G : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (H : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hG : G = (upperStarFromPoint Y).mapMod Λ)
    (hH : H = (upperStarFromPoint X).mapMod Λ)
    (hF : F = CondensedRing.upperStar Λ g)
    (sY : G.obj (Mod.regular Λ) ≅ Mod.regular (condensedRingObj Λ Y))
    (sX : H.obj (Mod.regular Λ) ≅ Mod.regular (condensedRingObj Λ X))
    (hsY : HEq sY (regularPointIso Λ Y)) (hsX : HEq sX (regularPointIso Λ X))
    (e : G ⋙ F ≅ H) (he : HEq e (CondensedRing.upperStarFromPointModComp Λ g))
    (η : F.obj (Mod.regular (condensedRingObj Λ Y)) ⟶ Mod.regular (condensedRingObj Λ X))
    (hη : HEq η (Functor.Monoidal.εIso (CondensedRing.upperStar Λ g)).inv) :
    F.map sY.inv ≫ e.hom.app (Mod.regular Λ) = η ≫ sX.inv := by
  subst G
  subst H
  subst F
  cases hsY
  cases hsX
  cases he
  cases hη
  exact regularUnit_comp_of_iso Λ g _ _ rfl rfl

private theorem quotientUnit_comp_of_regular
    {B C D : Type*} [Category B] [Category C] [Category D]
    (F : C ⥤ D) (G : B ⥤ C) (H : B ⥤ D) (e : G ⋙ F ≅ H)
    (R : B) {U : C} {U' : D} (s : G.obj R ≅ U) (s' : H.obj R ≅ U')
    (η : F.obj U ⟶ U')
    (he : F.map s.inv ≫ e.hom.app R = η ≫ s'.inv)
    {N : B} (q : R ⟶ N) :
    F.map (s.inv ≫ G.map q) ≫ e.hom.app N = η ≫ s'.inv ≫ H.map q := by
  have hn := e.hom.naturality q
  dsimp only [Functor.comp_map] at hn
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc, he, Category.assoc]

set_option maxHeartbeats 800000 in
-- The unit comparison involves several module-functor wrappers.
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private abbrev pull {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  CondensedRing.upperStar (DerivedNakayama.integerRing l E) g

private def pointComp {X Y : Scheme.{u}} (g : X ⟶ Y) :
    DerivedNakayama.pullback l E Y ⋙ pull l E g ≅ DerivedNakayama.pullback l E X :=
  CondensedRing.upperStarFromPointModComp (DerivedNakayama.integerRing l E) g

private def levelFunctorIso {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) :
    tensorRight (AdicCompletion.finiteModule l E Y n) ⋙ pull l E g ≅
      pull l E g ⋙ tensorRight (AdicCompletion.finiteModule l E X n) :=
  tensorSquareIso (pull l E g)
    ((pointComp l E g).app (DerivedNakayama.quotientModule l E (n + 1)))

private def levelIso {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) (n : ℕ) :
    (pulledTower l E g P).obj (op n) ≅
      (AdicCompletion.level l E X n).obj
        (((pull l E g).mapHomologicalComplex (.up ℤ)).obj P) :=
  (Functor.mapHomologicalComplexCompIso (levelFunctorIso l E g n) (.up ℤ)).app P

private theorem levelIso_step {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) (n : ℕ) :
    ((pull l E g).mapHomologicalComplex (.up ℤ)).map
        (AdicCompletion.levelStep l E Y P n) ≫ (levelIso l E g P n).hom =
      (levelIso l E g P (n + 1)).hom ≫
        AdicCompletion.levelStep l E X
          (((pull l E g).mapHomologicalComplex (.up ℤ)).obj P) n := by
  ext i : 1
  exact tensorSquareIso_natural (pull l E g)
    ((pointComp l E g).app (DerivedNakayama.quotientModule l E ((n + 1) + 1)))
    ((pointComp l E g).app (DerivedNakayama.quotientModule l E (n + 1)))
    ((DerivedNakayama.pullback l E Y).map (AdicCompletion.quotientStep l E n))
    ((DerivedNakayama.pullback l E X).map (AdicCompletion.quotientStep l E n))
    (by simpa only [Functor.comp_map, Functor.comp_obj, Iso.app_hom,
      CondensedRing.upperStarFromPointMod, DerivedNakayama.pullback] using
      ((pointComp l E g).hom.naturality
        (X := DerivedNakayama.quotientModule l E ((n + 1) + 1))
        (Y := DerivedNakayama.quotientModule l E (n + 1))
        (AdicCompletion.quotientStep l E n))) (P.X i)

private theorem regularPointIso_integral (X : Scheme.{u}) :
    DerivedNakayama.regularPullbackIso l E X =
      regularPointIso (DerivedNakayama.integerRing l E) X := by
  apply Iso.ext
  apply Mod.hom_ext
  rfl

private theorem regularUnit_comp_integral {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (pull l E g).map (DerivedNakayama.regularPullbackIso l E Y).inv ≫
      (pointComp l E g).hom.app (Mod.regular (DerivedNakayama.integerRing l E)) =
    (Functor.Monoidal.εIso (pull l E g)).inv ≫
      (DerivedNakayama.regularPullbackIso l E X).inv := by
  exact regularUnit_comp_of_data (DerivedNakayama.integerRing l E) g
    (DerivedNakayama.pullback l E Y) (DerivedNakayama.pullback l E X) (pull l E g)
    rfl rfl rfl
    (DerivedNakayama.regularPullbackIso l E Y) (DerivedNakayama.regularPullbackIso l E X)
    (heq_of_eq (regularPointIso_integral l E Y))
    (heq_of_eq (regularPointIso_integral l E X))
    (pointComp l E g) (by rfl) (Functor.Monoidal.εIso (pull l E g)).inv (by rfl)

private theorem finiteUnit_comp {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) :
    (pull l E g).map (AdicCompletion.finiteUnit l E Y n) ≫
        (pointComp l E g).hom.app (DerivedNakayama.quotientModule l E (n + 1)) =
      (Functor.Monoidal.εIso (pull l E g)).inv ≫
        AdicCompletion.finiteUnit l E X n := by
  exact quotientUnit_comp_of_regular (pull l E g)
    (DerivedNakayama.pullback l E Y) (DerivedNakayama.pullback l E X) (pointComp l E g)
    (Mod.regular (DerivedNakayama.integerRing l E))
    (DerivedNakayama.regularPullbackIso l E Y) (DerivedNakayama.regularPullbackIso l E X)
    (Functor.Monoidal.εIso (pull l E g)).inv (regularUnit_comp_integral l E g)
    (AdicCompletion.quotientUnit l E n)

private theorem levelIso_unit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) (n : ℕ) :
    ((pull l E g).mapHomologicalComplex (.up ℤ)).map
        (AdicCompletion.levelUnit l E Y P n) ≫ (levelIso l E g P n).hom =
      AdicCompletion.levelUnit l E X
        (((pull l E g).mapHomologicalComplex (.up ℤ)).obj P) n := by
  ext i : 1
  exact tensorSquareIso_unit (pull l E g)
    ((pointComp l E g).app (DerivedNakayama.quotientModule l E (n + 1)))
    (AdicCompletion.finiteUnit l E Y n) (AdicCompletion.finiteUnit l E X n)
    (finiteUnit_comp l E g n) (P.X i)

/-- The pulled strict quotient tower has the same augmented Roos complex as the
quotient tower of the ordinary inverse image. This holds before localization and
without completeness, constructibility, or K-flatness assumptions.

Source: blueprint det-lem-int-tensor-pullback, first paragraph; strict normalization
step 8; Stacks 099M and 08TC.
(blueprint: lem-sfb-internal-pullback-roos-unit).

Proof: the monoidal coefficient-square comparison identifies the pullback of each
finite quotient module with that quotient on X, naturally in its coefficient
module. Compose this with the strong monoidal tensor comparison to identify
F(P tensor A_n) with F(P) tensor A_n in each degree. Naturality in the quotient
map identifies consecutive transitions, and monoidal unit compatibility identifies
the quotient augmentations. Take the product of these level isomorphisms. It
intertwines 1 minus shift, hence induces the diagonal mapping-cocone isomorphism.
Convert the mapping cocone to the explicit completion coordinates (x,-y); its
second coordinate differential is (1-shift)x-dy. Both augmentations have zero
second coordinate and the same first coordinate, proving the asserted equality.
The argument applies unchanged to zero complexes, empty schemes, and identity
morphisms. -/
theorem ordinary_roos_unit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    ∃ e : WeilConjectures.integralOperationsRoos (pulledTower l E g P) ≅
        AdicCompletion.roos l E X
          (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapHomologicalComplex
            (.up ℤ)).obj P),
      comparison l E g P ≫ e.hom =
        AdicCompletion.augmentation l E X
          (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapHomologicalComplex
            (.up ℤ)).obj P) := by
  let Q := ((pull l E g).mapHomologicalComplex (.up ℤ)).obj P
  let V := ∏ᶜ fun n : ℕ ↦ (pulledTower l E g P).obj (op n)
  let t : V ⟶ V := towerTransitionEndomorphism
    (WeilConjectures.integralOperationsTowerStep (pulledTower l E g P))
  let a : V ≅ AdicCompletion.product l E X Q := Pi.mapIso (levelIso l E g P)
  have ht : a.hom ≫ AdicCompletion.oneSubShift l E X Q = t ≫ a.hom := by
    change (Pi.mapIso (levelIso l E g P)).hom ≫
        towerTransitionEndomorphism (AdicCompletion.levelStep l E X Q) =
      towerTransitionEndomorphism _ ≫ (Pi.mapIso (levelIso l E g P)).hom
    exact productIso_natural
      (C := CochainComplex (AdicCompletion.Modules l E X) ℤ)
      (K := fun n ↦ (pulledTower l E g P).obj (op n))
      (K' := fun n ↦ (AdicCompletion.level l E X n).obj Q)
      (WeilConjectures.integralOperationsTowerStep (pulledTower l E g P))
      (AdicCompletion.levelStep l E X Q) (levelIso l E g P)
      (fun n ↦ by
        simp only [WeilConjectures.integralOperationsTowerStep, pulledTower,
          Functor.comp_map, tower, Functor.ofOpSequence_map_homOfLE_succ]
        change @Eq
          ((((pull l E g).mapHomologicalComplex (.up ℤ)).obj
            ((AdicCompletion.level l E Y (n + 1)).obj P)) ⟶
            (AdicCompletion.level l E X n).obj Q)
          ((levelIso l E g P (n + 1)).hom ≫ AdicCompletion.levelStep l E X Q n)
          (((pull l E g).mapHomologicalComplex (.up ℤ)).map
            (AdicCompletion.levelStep l E Y P n) ≫ (levelIso l E g P n).hom)
        exact (levelIso_step l E g P n).symm)
  change ∃ e : CochainComplex.mappingCocone t ≅
      AdicCompletion.genericRoos (AdicCompletion.product l E X Q)
        (AdicCompletion.oneSubShift l E X Q),
    comparison l E g P ≫ e.hom = AdicCompletion.augmentation l E X Q
  refine ⟨roosIso t (AdicCompletion.oneSubShift l E X Q) a ht, ?_⟩
  have hp : Pi.lift (fun n ↦ ((pull l E g).mapHomologicalComplex (.up ℤ)).map
        (AdicCompletion.levelUnit l E Y P n)) ≫ a.hom =
      AdicCompletion.unitProduct l E X Q := by
    change Pi.lift _ ≫ (Pi.mapIso (levelIso l E g P)).hom =
      Pi.lift (AdicCompletion.levelUnit l E X Q)
    exact productIso_lift
      (C := CochainComplex (AdicCompletion.Modules l E X) ℤ) (P := Q)
      (K := fun n ↦ (pulledTower l E g P).obj (op n))
      (K' := fun n ↦ (AdicCompletion.level l E X n).obj Q)
      (levelIso l E g P)
      (fun n ↦ ((pull l E g).mapHomologicalComplex (.up ℤ)).map
        (AdicCompletion.levelUnit l E Y P n))
      (AdicCompletion.levelUnit l E X Q) (levelIso_unit l E g P)
  simp only [comparison, augmentation, towerUnit]
  exact roosIso_lift t (AdicCompletion.oneSubShift l E X Q) a ht _ _ hp _
    (AdicCompletion.augmentation l E X Q) (by intro i; rfl)

set_option maxHeartbeats 800000 in
-- Normalize the concrete quotient and complex wrappers in this compatibility proof.
set_option maxHeartbeats 800000 in
-- Check unit coherence using the named comparison without unfolding its construction.
set_option maxHeartbeats 800000 in
-- Convert the concrete complex wrappers to the degreewise monoidal unit calculation.
set_option maxHeartbeats 800000 in
-- The concrete product and completion models require several definitional conversions.
end AlgebraicGeometry.ProEtale.IntegralTensorPullback
