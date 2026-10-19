/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.SystemLevelLeftExtension
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-! Uncurrying module presheaves on a varying coefficient diagram. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t v u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace SheafOfModules.CoefficientDiagram
variable {C : Type t} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{u})

/-- The varying coefficient presheaf on the product site. -/
abbrev ring : (ℕ × C)ᵒᵖ ⥤ RingCat.{u} :=
  (prodOpEquiv (C := ℕ) (D := C)).functor ⋙
    Functor.uncurry.obj (B ⋙ sheafCompose J (forget₂ CommRingCat RingCat) ⋙
      sheafToPresheaf J RingCat)

/-- Vertical module sheaves over a specified product presheaf. -/
abbrev towersOf (R : (ℕ × C)ᵒᵖ ⥤ RingCat.{u}) :=
  ObjectProperty.FullSubcategory (C := PresheafOfModules.{u} R)
    (fun M ↦ ∀ n : ℕ, Presheaf.IsSheaf J ((Prod.sectR n C).op ⋙ M.presheaf))

abbrev towers := towersOf (J := J) (ring B)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
private theorem vertical (n : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (ring B).map (Prod.mkHom (𝟙 n) f.unop).op =
      (derivedChangeRingIndependentCoefficients J (B.obj (op n))).obj.map f := by
  change (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
    (B.map (𝟙 (op n)))).hom.app U) ≫ _ = _
  simp

private def sliceRing (n : ℕ) :
    (derivedChangeRingIndependentCoefficients J (B.obj (op n))).obj ⟶
      (Prod.sectR n C).op ⋙ ring B where
  app _ := 𝟙 _
  naturality {U V} f := by
    simp only [Category.id_comp, Category.comp_id]
    change (derivedChangeRingIndependentCoefficients J (B.obj (op n))).obj.map f =
      (ring B).map (Prod.mkHom (𝟙 n) f.unop).op
    exact (vertical B n f).symm

private def level (M : towers B) (n : ℕ) : systemLevel B n where
  val :=
    { obj := fun U ↦ M.obj.obj (op (n, U.unop))
      map := fun {U V} f ↦ M.obj.map (Prod.mkHom (𝟙 n) f.unop).op ≫
        (ModuleCat.restrictScalarsCongr
          (congrArg RingCat.Hom.hom (vertical B n f))).hom.app
            (M.obj.obj (op (n, V.unop)))
      map_id := by
        intro U
        ext x
        change M.obj.map (𝟙 (op (n, U.unop))) x = x
        rw [M.obj.map_id]
        rfl
      map_comp := by
        intro U V W f g
        ext x
        change M.obj.map (Prod.mkHom (𝟙 n) (g.unop ≫ f.unop)).op x =
          M.obj.map (Prod.mkHom (𝟙 n) g.unop).op
            (M.obj.map (Prod.mkHom (𝟙 n) f.unop).op x)
        erw [← M.obj.map_comp_apply]
        exact M.obj.congr_map_apply (by
          apply Quiver.Hom.unop_inj
          ext <;> simp) x }
  isSheaf := by
    let i : _ ≅ (Prod.sectR n C).op ⋙ M.obj.presheaf :=
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro U V f; ext x; rfl)
    exact (Presheaf.isSheaf_of_iso_iff i).2 (M.property n)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
private theorem horizontal {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) :
    (ring B).map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op =
      (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
        (B.map (homOfLE h).op)).hom.app U) := by
  simp [ring, Functor.uncurry_obj_map]

private def transition (M : towers B) {m n : ℕ} (h : m ≤ n) :
    level B M n ⟶ (systemRestriction B h).obj (level B M m) where
  val :=
    { app := fun U ↦ M.obj.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op ≫
        (ModuleCat.restrictScalarsCongr
          (congrArg RingCat.Hom.hom (horizontal B h U))).hom.app
            (M.obj.obj (op (m, U.unop)))
      naturality := by
        intro U V f
        ext x
        change M.obj.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op
            (M.obj.map (Prod.mkHom (𝟙 n) f.unop).op x) =
          M.obj.map (Prod.mkHom (𝟙 m) f.unop).op
            (M.obj.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)
        erw [← M.obj.map_comp_apply, ← M.obj.map_comp_apply]
        exact M.obj.congr_map_apply (by
          apply Quiver.Hom.unop_inj
          ext <;> simp) x }

private def spTowerToStrictObj (M : towers B) :
    StrictRingSystem B where
  level := level B M
  transition := transition B M
  identity n U x := by
    change M.obj.map (Prod.mkHom (homOfLE (Nat.le_refl n)) (𝟙 U.unop)).op x = x
    have hh : (Prod.mkHom (homOfLE (Nat.le_refl n)) (𝟙 U.unop)).op =
        𝟙 (op (n, U.unop)) := rfl
    rw [hh, M.obj.map_id]
    rfl
  compose {r m n} h k U x := by
    change M.obj.map (Prod.mkHom (homOfLE (h.trans k)) (𝟙 U.unop)).op x =
      M.obj.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
        (M.obj.map (Prod.mkHom (homOfLE k) (𝟙 U.unop)).op x)
    erw [← M.obj.map_comp_apply]
    exact M.obj.congr_map_apply (by
      apply Quiver.Hom.unop_inj
      ext <;> simp) x

private def spTowerToStrict : towers B ⥤
    StrictRingSystem B where
  obj := spTowerToStrictObj B
  map f :=
    { app := fun n ↦
        { val :=
            { app := fun U ↦ f.hom.app (op (n, U.unop))
              naturality := by
                intro U V g
                ext x
                exact PresheafOfModules.naturality_apply f.hom (Prod.mkHom (𝟙 n) g.unop).op x } }
      comm := by
        intro m n h
        ext U x
        exact (PresheafOfModules.naturality_apply f.hom
          (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x).symm }


private def spStrictPresheaf (M :
    StrictRingSystem B) :
    PresheafOfModules.{u} (ring B) where
  obj X := (M.level X.unop.1).val.obj (op X.unop.2)
  map {X Y} f := ModuleCat.ofHom
    (X := (M.level X.unop.1).val.obj (op X.unop.2))
    (Y := (ModuleCat.restrictScalars ((ring B).map f).hom).obj
      ((M.level Y.unop.1).val.obj (op Y.unop.2)))
    { toFun := fun x ↦ (M.level Y.unop.1).val.map f.unop.2.op
        ((M.transition (leOfHom f.unop.1)).val.app (op X.unop.2) x)
      map_add' := by intro x y; simp
      map_smul' := by
        change ∀ (r : (derivedChangeRingIndependentCoefficients J
          (B.obj (op X.unop.1))).obj.obj (op X.unop.2))
          (x : (M.level X.unop.1).val.obj (op X.unop.2)), _
        intro r x
        change (M.level Y.unop.1).val.map f.unop.2.op
          (((M.transition (leOfHom f.unop.1)).val.app (op X.unop.2)).hom (r • x)) =
          ((ring B).map f).hom r • _
        change (M.level Y.unop.1).val.map f.unop.2.op
          (((M.transition (leOfHom f.unop.1)).val.app (op X.unop.2)) (r • x)) = _
        have ht := ((M.transition (leOfHom f.unop.1)).val.app (op X.unop.2)).hom.map_smul r x
        have ht' : ((M.transition (leOfHom f.unop.1)).val.app (op X.unop.2)) (r • x) =
            ((B.map (homOfLE (leOfHom f.unop.1)).op).hom.app (op X.unop.2)) r •
              (show (M.level Y.unop.1).val.obj (op X.unop.2) from
                (M.transition (leOfHom f.unop.1)).val.app (op X.unop.2) x) := ht
        rw [ht', (M.level Y.unop.1).val.map_smul]
        rfl }

  map_id X := by
    ext x
    change (M.level X.unop.1).val.map (𝟙 (op X.unop.2))
      ((M.transition (Nat.le_refl X.unop.1)).val.app (op X.unop.2) x) = x
    rw [M.identity]
    simp
  map_comp {X Y Z} f g := by
    ext x
    change (M.level Z.unop.1).val.map (g.unop.2 ≫ f.unop.2).op
        ((M.transition ((leOfHom g.unop.1).trans (leOfHom f.unop.1))).val.app (op X.unop.2) x) =
      (M.level Z.unop.1).val.map g.unop.2.op
        ((M.transition (leOfHom g.unop.1)).val.app (op Y.unop.2)
          ((M.level Y.unop.1).val.map f.unop.2.op
            ((M.transition (leOfHom f.unop.1)).val.app (op X.unop.2) x)))
    have hc := (M.level Z.unop.1).val.map_comp_apply f.unop.2.op g.unop.2.op
      ((M.transition ((leOfHom g.unop.1).trans (leOfHom f.unop.1))).val.app
        (op X.unop.2) x)
    change _ = _ at hc
    refine hc.trans ?_
    have hh := PresheafOfModules.naturality_apply (M.transition (leOfHom g.unop.1)).val f.unop.2.op
      ((M.transition (leOfHom f.unop.1)).val.app (op X.unop.2) x)
    change (M.transition (leOfHom g.unop.1)).val.app (op Y.unop.2)
        ((M.level Y.unop.1).val.map f.unop.2.op
          ((M.transition (leOfHom f.unop.1)).val.app (op X.unop.2) x)) =
      (M.level Z.unop.1).val.map f.unop.2.op
        ((M.transition (leOfHom g.unop.1)).val.app (op X.unop.2)
          ((M.transition (leOfHom f.unop.1)).val.app (op X.unop.2) x)) at hh
    rw [hh, ← M.compose]

private def spStrictToTower :
    StrictRingSystem B ⥤
      towers B where
  obj M := ⟨spStrictPresheaf B M, by
    intro n
    let i : (Prod.sectR n C).op ⋙ (spStrictPresheaf B M).presheaf ≅
        (M.level n).val.presheaf :=
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
        intro U V f
        ext x
        change (M.level n).val.map f
          ((M.transition (Nat.le_refl n)).val.app U x) = (M.level n).val.map f x
        rw [M.identity])
    exact (Presheaf.isSheaf_of_iso_iff i).2 (M.level n).isSheaf⟩
  map {M N} f := ObjectProperty.homMk
    { app := fun X ↦ (f.app X.unop.1).val.app (op X.unop.2)
      naturality := by
        intro X Y g
        ext x
        have hh := congrArg (fun k ↦ k.val.app (op X.unop.2) x)
          (f.comm (leOfHom g.unop.1))
        have hv := PresheafOfModules.naturality_apply (f.app Y.unop.1).val g.unop.2.op
          ((M.transition (leOfHom g.unop.1)).val.app (op X.unop.2) x)
        dsimp [spStrictPresheaf]
        change (N.transition (leOfHom g.unop.1)).val.app (op X.unop.2)
            ((f.app X.unop.1).val.app (op X.unop.2) x) =
          (f.app Y.unop.1).val.app (op X.unop.2)
            ((M.transition (leOfHom g.unop.1)).val.app (op X.unop.2) x) at hh
        rw [hv]
        exact congrArg (fun y ↦ (N.level Y.unop.1).val.map g.unop.2.op y) hh.symm }

private def spTowerUnit (M : towers B) :
    M ≅ (spStrictToTower B).obj ((spTowerToStrict B).obj M) :=
  ObjectProperty.isoMk _ (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro X Y f
    ext x
    change M.obj.map f x =
      M.obj.map (Prod.mkHom (𝟙 Y.unop.1) f.unop.2).op
        (M.obj.map (Prod.mkHom f.unop.1 (𝟙 X.unop.2)).op x)
    erw [← M.obj.map_comp_apply]
    exact M.obj.congr_map_apply (by
      apply Quiver.Hom.unop_inj
      ext <;> simp) x))

private def spStrictCounit (M :
    StrictRingSystem B) :
    (spTowerToStrict B).obj ((spStrictToTower B).obj M) ≅ M where
  hom :=
    { app := fun n ↦
        { val :=
            { app := fun _ ↦ 𝟙 _
              naturality := by
                intro U V f
                ext x
                change (M.level n).val.map f
                  ((M.transition (Nat.le_refl n)).val.app U x) = (M.level n).val.map f x
                rw [M.identity] } }
      comm := by
        intro m n h
        ext U x
        change (M.transition h).val.app U x =
          (M.level m).val.map (𝟙 U) ((M.transition h).val.app U x)
        simp }
  inv :=
    { app := fun n ↦
        { val :=
            { app := fun _ ↦ 𝟙 _
              naturality := by
                intro U V f
                ext x
                change (M.level n).val.map f x =
                  (M.level n).val.map f ((M.transition (Nat.le_refl n)).val.app U x)
                rw [M.identity] } }
      comm := by
        intro m n h
        ext U x
        change (M.level m).val.map (𝟙 U) ((M.transition h).val.app U x) =
          (M.transition h).val.app U x
        simp }
  hom_inv_id := by congr 1
  inv_hom_id := by congr 1

private theorem transport_heq {R S : Type u} [Ring R] [Ring S]
    {f g : R →+* S} (h : f = g) (X : ModuleCat.{u} R) (Y : ModuleCat.{u} S)
    (k : X ⟶ (ModuleCat.restrictScalars f).obj Y) :
    HEq (k ≫ (ModuleCat.restrictScalarsCongr h).hom.app Y) k := by
  subst g
  rfl

private def spTowerEquivalence : towers B ≌
    StrictRingSystem B where
  functor := spTowerToStrict B
  inverse := spStrictToTower B
  unitIso := NatIso.ofComponents (spTowerUnit B) (by
    intro M N f
    ext X x
    rfl)
  counitIso := NatIso.ofComponents (spStrictCounit B) (by
    intro M N f
    have ext {P Q : StrictRingSystem B} (a b : P ⟶ Q)
        (h : a.app = b.app) : a = b := by
      cases a
      cases b
      congr
    apply ext
    funext n
    ext U x
    rfl)
  functor_unitIso_comp M := by congr 1


/-- Uncurrying fixes the section modules, vertical maps, iterated transitions and
morphism components. Source: Bhatt--Scholze, Definition 3.5.3, and the coefficient-tower
lemma, step 1 (blueprint: lem-sp-coefficient-diagram-uncurrying).

Proof: restrict to vertical slices and use horizontal presheaf restrictions for the
semilinear transitions. Conversely factor a product arrow into its horizontal and
vertical arrows. The naturality square for transitions proves functoriality. The two
composites have identity maps on every section, which give the unit and counit.
The formulas retain the maps themselves, using only scalar-restriction transport. -/
theorem exists_uncurrying :
    ∃ e : towers B ≌ StrictRingSystem B,
      (∀ (M : towers B) (n : ℕ) (U : Cᵒᵖ),
        HEq (((e.functor.obj M).level n).val.obj U) (M.obj.obj (op (n, U.unop)))) ∧
      (∀ (M : towers B) (n : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V),
        HEq (((e.functor.obj M).level n).val.map f)
          (M.obj.map (Prod.mkHom (𝟙 n) f.unop).op)) ∧
      (∀ (M : towers B) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ),
        HEq (((e.functor.obj M).transition h).val.app U)
          (M.obj.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)) ∧
      (∀ {M N : towers B} (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ),
        HEq (((e.functor.map f).app n).val.app U) (f.hom.app (op (n, U.unop)))) := by
  refine ⟨spTowerEquivalence B, ?_, ?_, ?_, ?_⟩
  · intro M n U
    rfl
  · intro M n U V f
    exact transport_heq (congrArg RingCat.Hom.hom (vertical B n f)) _ _ _
  · intro M m n h U
    exact transport_heq (congrArg RingCat.Hom.hom (horizontal B h U)) _ _ _
  · intro M N f n U
    rfl


/-- The sectionwise normalization of an uncurrying equivalence. -/
structure Normalized (R : (ℕ × C)ᵒᵖ ⥤ RingCat.{u})
    (e : towersOf (J := J) R ≌ StrictRingSystem B) : Prop where
  sections : ∀ (M : towersOf (J := J) R) (n : ℕ) (U : Cᵒᵖ),
    HEq (((e.functor.obj M).level n).val.obj U) (M.obj.obj (op (n, U.unop)))
  restrictions : ∀ (M : towersOf (J := J) R) (n : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V),
    HEq (((e.functor.obj M).level n).val.map f)
      (M.obj.map (Prod.mkHom (𝟙 n) f.unop).op)
  transitions : ∀ (M : towersOf (J := J) R) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ),
    HEq (((e.functor.obj M).transition h).val.app U)
      (M.obj.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
  morphisms : ∀ {M N : towersOf (J := J) R} (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ),
    HEq (((e.functor.map f).app n).val.app U) (f.hom.app (op (n, U.unop)))

/-- Transport uncurrying to an equal coefficient presheaf.
Source: the preceding construction (blueprint: lem-sp-coefficient-diagram-uncurrying). -/
theorem exists_uncurrying_of_eq (R : (ℕ × C)ᵒᵖ ⥤ RingCat.{u})
    (hR : R = ring B) :
    ∃ e : towersOf (J := J) R ≌ StrictRingSystem B, Normalized B R e := by
  subst R
  obtain ⟨e, hs, hv, ht, hm⟩ := exists_uncurrying B
  exact ⟨e, hs, hv, ht, hm⟩

end SheafOfModules.CoefficientDiagram
