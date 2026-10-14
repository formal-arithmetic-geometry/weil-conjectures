/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Equivalence

/-! # The pair-category construction for coherent systems

Source: Stacks Project, Categories, Tag 004A, applied fibrewise.
(blueprint: lem-weil-pbc-site-system-strictification-category)
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace CategoryTheory.SiteSystemPairs

variable {I : Type u} [Preorder I] (C : I → Cat.{u, u})

/-- The stage-labelled objects used in the splitting construction of Stacks 004A. -/
structure Obj (i : I) where
  stage : I
  le : stage ≤ i
  obj : C stage

variable (U : ∀ (i j : I), i ≤ j → C i ⥤ C j)

/-- Evaluation of a labelled object at the current stage. -/
abbrev evalObj (i : I) (X : Obj C i) : C i := (U X.stage i X.le).obj X.obj

/-- The category of labelled objects, with arrows evaluated at the current stage. -/
abbrev Fiber (i : I) := InducedCategory (C i) (evalObj C U i)

/-- Evaluation is the fully faithful induced functor. -/
abbrev eval (i : I) : Fiber C U i ⥤ C i := inducedFunctor (evalObj C U i)

/-- The inclusion of the current stage. -/
def inclusion (i : I) : C i ⥤ Fiber C U i where
  obj X := ⟨i, le_rfl, X⟩
  map f := InducedCategory.homMk ((U i i le_rfl).map f)
  map_id X := by apply InducedCategory.hom_ext; exact (U i i le_rfl).map_id X
  map_comp f g := by apply InducedCategory.hom_ext; exact (U i i le_rfl).map_comp f g

variable (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
  U i j h ⋙ U j k h' ≅ U i k (h.trans h'))

/-- Transition fixes labels and conjugates the evaluated arrow by the comparison. -/
def transition (i j : I) (h : i ≤ j) : Fiber C U i ⥤ Fiber C U j where
  obj X := ⟨X.stage, X.le.trans h, X.obj⟩
  map {X Y} f := InducedCategory.homMk
    ((gamma X.stage i j X.le h).inv.app X.obj ≫ (U i j h).map f.hom ≫
      (gamma Y.stage i j Y.le h).hom.app Y.obj)
  map_id X := by
    apply InducedCategory.hom_ext
    change (gamma X.stage i j X.le h).inv.app X.obj ≫
      (U i j h).map (𝟙 _) ≫ (gamma X.stage i j X.le h).hom.app X.obj = 𝟙 _
    rw [Functor.map_id]
    exact (congrArg (fun f ↦ (gamma X.stage i j X.le h).inv.app X.obj ≫ f)
      (Category.id_comp ((gamma X.stage i j X.le h).hom.app X.obj))).trans
      ((gamma X.stage i j X.le h).inv_hom_id_app X.obj)
  map_comp {X Y Z} f g := by
    apply InducedCategory.hom_ext
    change (gamma X.stage i j X.le h).inv.app X.obj ≫
      (U i j h).map (f.hom ≫ g.hom) ≫ (gamma Z.stage i j Z.le h).hom.app Z.obj =
      ((gamma X.stage i j X.le h).inv.app X.obj ≫ (U i j h).map f.hom ≫
        (gamma Y.stage i j Y.le h).hom.app Y.obj) ≫
      ((gamma Y.stage i j Y.le h).inv.app Y.obj ≫ (U i j h).map g.hom ≫
        (gamma Z.stage i j Z.le h).hom.app Z.obj)
    simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]


/-- Evaluation intertwines transition with the original transition up to gamma. -/
def comparison (i j : I) (h : i ≤ j) :
    transition C U gamma i j h ⋙ eval C U j ≅ eval C U i ⋙ U i j h :=
  NatIso.ofComponents (fun X ↦ ((gamma X.stage i j X.le h).app X.obj).symm)
    (by
      intro X Y f
      change ((gamma X.stage i j X.le h).inv.app X.obj ≫ (U i j h).map f.hom ≫
        (gamma Y.stage i j Y.le h).hom.app Y.obj) ≫
          (gamma Y.stage i j Y.le h).inv.app Y.obj =
        (gamma X.stage i j X.le h).inv.app X.obj ≫ (U i j h).map f.hom
      simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj]
      exact congrArg (fun f ↦ (gamma X.stage i j X.le h).inv.app X.obj ≫ f)
        (Category.comp_id ((U i j h).map f.hom)))

variable (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))

/-- The current-stage inclusion followed by evaluation is the identity transition. -/
theorem inclusion_eval (i : I) : inclusion C U i ⋙ eval C U i = U i i le_rfl := rfl

/-- Evaluation is an equivalence: every object is represented at its own stage. -/
theorem eval_isEquivalence
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i)) (i : I) : (eval C U i).IsEquivalence := by
  have : (eval C U i).EssSurj := ⟨fun X ↦ ⟨⟨i, le_rfl, X⟩, ⟨(eqToIso (hUid i)).app X⟩⟩⟩
  exact { faithful := inferInstanceAs (inducedFunctor (evalObj C U i)).Faithful
          full := inferInstanceAs (inducedFunctor (evalObj C U i)).Full
          essSurj := this }

/-- The inclusion is an equivalence since its composite with evaluation is identity. -/
theorem inclusion_isEquivalence
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i)) (i : I) : (inclusion C U i).IsEquivalence := by
  have : (eval C U i).IsEquivalence := eval_isEquivalence C U hUid i
  have : (inclusion C U i ⋙ eval C U i).IsEquivalence := by
    rw [inclusion_eval, hUid i]
    infer_instance
  exact Functor.isEquivalence_of_comp_right (inclusion C U i) (eval C U i)

private theorem normalized_map
    {A B E : Type u} [SmallCategory A] [SmallCategory B] [SmallCategory E]
    (G : E ⥤ E) (hG : G = 𝟭 E) (K : A ⥤ E) (L : B ⥤ E)
    (a : K ⋙ G ≅ K) (b : L ⋙ G ≅ L)
    (ha : HEq a (Iso.refl K)) (hb : HEq b (Iso.refl L))
    (X : A) (Y : B) (f : K.obj X ⟶ L.obj Y) :
    a.inv.app X ≫ G.map f ≫ b.hom.app Y = f := by
  subst hG
  have ha' : a = Iso.refl K := eq_of_heq ha
  have hb' : b = Iso.refl L := eq_of_heq hb
  rw [ha', hb']
  simp

/-- Right normalization makes a self-transition strictly the identity. -/
theorem transition_id (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hgammaRight : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i k k h le_rfl) (Iso.refl (U i k h))) (i : I) :
    transition C U gamma i i le_rfl = 𝟭 (Fiber C U i) := by
  apply Functor.hext (fun X ↦ by cases X; rfl)
  intro X Y f
  apply heq_of_eq
  apply InducedCategory.hom_ext
  exact normalized_map (U i i le_rfl) (hUid i) (U X.stage i X.le) (U Y.stage i Y.le)
    (gamma X.stage i i X.le le_rfl) (gamma Y.stage i i Y.le le_rfl)
    (hgammaRight _ _ _) (hgammaRight _ _ _) X.obj Y.obj f.hom

/-- The cocycle makes consecutive transitions compose strictly. -/
theorem transition_comp
    (hgamma : ∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (X : C i),
      (gamma j k l h' h'').hom.app ((U i j h).obj X) ≫
          (gamma i j l h (h'.trans h'')).hom.app X =
        (U k l h'').map ((gamma i j k h h').hom.app X) ≫
          (gamma i k l (h.trans h') h'').hom.app X)
    (i j k : I) (h : i ≤ j) (h' : j ≤ k) :
    transition C U gamma i j h ⋙ transition C U gamma j k h' =
      transition C U gamma i k (h.trans h') := by
  refine Functor.hext (F := transition C U gamma i j h ⋙ transition C U gamma j k h')
    (G := transition C U gamma i k (h.trans h')) (fun X ↦ rfl) ?_
  intro X Y f
  apply heq_of_eq
  apply InducedCategory.hom_ext
  change (gamma X.stage j k (X.le.trans h) h').inv.app X.obj ≫
      (U j k h').map ((gamma X.stage i j X.le h).inv.app X.obj ≫
        (U i j h).map f.hom ≫ (gamma Y.stage i j Y.le h).hom.app Y.obj) ≫
      (gamma Y.stage j k (Y.le.trans h) h').hom.app Y.obj =
    (gamma X.stage i k X.le (h.trans h')).inv.app X.obj ≫
      (U i k (h.trans h')).map f.hom ≫
      (gamma Y.stage i k Y.le (h.trans h')).hom.app Y.obj
  apply (cancel_epi ((U j k h').map ((gamma X.stage i j X.le h).hom.app X.obj) ≫
    (gamma X.stage j k (X.le.trans h) h').hom.app X.obj)).mp
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [← Functor.map_comp_assoc]
  rw [← Category.assoc ((U j k h').map ((gamma X.stage i j X.le h).hom.app X.obj))]
  rw [← hgamma X.stage i j k X.le h h' X.obj]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← hgamma Y.stage i j k Y.le h h' Y.obj]
  exact (gamma i j k h h').hom.naturality_assoc f.hom
    ((gamma Y.stage i k Y.le (h.trans h')).hom.app Y.obj)

/-- The strict diagram defined by the pair-category transitions. -/
def diagram
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hgammaRight : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i k k h le_rfl) (Iso.refl (U i k h)))
    (hgamma : ∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (X : C i),
      (gamma j k l h' h'').hom.app ((U i j h).obj X) ≫
          (gamma i j l h (h'.trans h'')).hom.app X =
        (U k l h'').map ((gamma i j k h h').hom.app X) ≫
          (gamma i k l (h.trans h') h'').hom.app X) : I ⥤ Cat.{u, u} where
  obj i := Cat.of (Fiber C U i)
  map f := (transition C U gamma _ _ (leOfHom f)).toCatHom
  map_id i := Cat.ext (transition_id C U gamma hUid hgammaRight i)
  map_comp f g := Cat.ext (transition_comp C U gamma hgamma _ _ _
    (leOfHom f) (leOfHom g)).symm

variable (D : Type v) [Category.{w} D] (v : ∀ i : I, C i ⥤ D)
  (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i)

/-- A coefficient functor retains the label, conjugating arrows by delta. -/
def coefficients (i : I) : Fiber C U i ⥤ D where
  obj X := (v X.stage).obj X.obj
  map {X Y} f := (delta X.stage i X.le).inv.app X.obj ≫ (v i).map f.hom ≫
    (delta Y.stage i Y.le).hom.app Y.obj
  map_id X := by
    change (delta X.stage i X.le).inv.app X.obj ≫
      (v i).map (𝟙 _) ≫ (delta X.stage i X.le).hom.app X.obj = 𝟙 _
    rw [Functor.map_id]
    exact (congrArg (fun f ↦ (delta X.stage i X.le).inv.app X.obj ≫ f)
      (Category.id_comp ((delta X.stage i X.le).hom.app X.obj))).trans
      ((delta X.stage i X.le).inv_hom_id_app X.obj)
  map_comp {X Y Z} f g := by
    change (delta X.stage i X.le).inv.app X.obj ≫
      (v i).map (f.hom ≫ g.hom) ≫ (delta Z.stage i Z.le).hom.app Z.obj =
      ((delta X.stage i X.le).inv.app X.obj ≫ (v i).map f.hom ≫
        (delta Y.stage i Y.le).hom.app Y.obj) ≫
      ((delta Y.stage i Y.le).inv.app Y.obj ≫ (v i).map g.hom ≫
        (delta Z.stage i Z.le).hom.app Z.obj)
    simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem normalized_natiso_map
    {A : Type u} [SmallCategory A] {E : Type v} [Category.{w} E]
    (G H : A ⥤ E) (hG : G = H) (a : G ≅ H) (ha : HEq a (Iso.refl H))
    {X Y : A} (f : X ⟶ Y) : a.inv.app X ≫ G.map f ≫ a.hom.app Y = H.map f := by
  subst hG
  rw [eq_of_heq ha]
  simp

/-- The coefficient functor restricts strictly to the original coefficient functor. -/
theorem inclusion_coefficients
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hdeltaId : ∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i))) (i : I) :
    inclusion C U i ⋙ coefficients C U D v delta i = v i := by
  refine Functor.hext (F := inclusion C U i ⋙ coefficients C U D v delta i)
    (G := v i) (fun X ↦ rfl) ?_
  intro X Y f
  apply heq_of_eq
  exact normalized_natiso_map (U i i le_rfl ⋙ v i) (v i)
    (by rw [hUid i]; rfl) (delta i i le_rfl) (hdeltaId i) f

/-- The delta cocycle makes coefficient compatibility strict. -/
theorem transition_coefficients
    (hdelta : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k) (X : C i),
      (v k).map ((gamma i j k h h').hom.app X) ≫
          (delta i k (h.trans h')).hom.app X =
        (delta j k h').hom.app ((U i j h).obj X) ≫ (delta i j h).hom.app X)
    (i j : I) (h : i ≤ j) :
    transition C U gamma i j h ⋙ coefficients C U D v delta j =
      coefficients C U D v delta i := by
  refine Functor.hext (F := transition C U gamma i j h ⋙ coefficients C U D v delta j)
    (G := coefficients C U D v delta i) (fun X ↦ rfl) ?_
  intro X Y f
  apply heq_of_eq
  change (delta X.stage j (X.le.trans h)).inv.app X.obj ≫
    (v j).map ((gamma X.stage i j X.le h).inv.app X.obj ≫
      (U i j h).map f.hom ≫ (gamma Y.stage i j Y.le h).hom.app Y.obj) ≫
    (delta Y.stage j (Y.le.trans h)).hom.app Y.obj =
    (delta X.stage i X.le).inv.app X.obj ≫ (v i).map f.hom ≫
      (delta Y.stage i Y.le).hom.app Y.obj
  apply (cancel_epi ((v j).map ((gamma X.stage i j X.le h).hom.app X.obj) ≫
    (delta X.stage j (X.le.trans h)).hom.app X.obj)).mp
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [← Functor.map_comp_assoc]
  rw [← Category.assoc ((v j).map ((gamma X.stage i j X.le h).hom.app X.obj)),
    hdelta X.stage i j X.le h X.obj]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  rw [hdelta Y.stage i j Y.le h Y.obj]
  exact (delta i j h).hom.naturality_assoc f.hom ((delta Y.stage i Y.le).hom.app Y.obj)

/-- The identity comparison between the two representations at the later stage. -/
def theta
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hgammaLeft : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i i k le_rfl h) (Iso.refl (U i k h)))
    (i j : I) (h : i ≤ j) :
    inclusion C U i ⋙ transition C U gamma i j h ≅ U i j h ⋙ inclusion C U j :=
  NatIso.ofComponents (fun X ↦ InducedCategory.isoMk
    (((eqToIso (hUid j)).app ((U i j h).obj X)).symm)) (by
      intro X Y f
      apply InducedCategory.hom_ext
      change ((gamma i i j le_rfl h).inv.app X ≫
          (U i j h).map ((U i i le_rfl).map f) ≫
          (gamma i i j le_rfl h).hom.app Y) ≫
            (eqToIso (hUid j)).inv.app ((U i j h).obj Y) =
        (eqToIso (hUid j)).inv.app ((U i j h).obj X) ≫
          (U j j le_rfl).map ((U i j h).map f)
      have hn := normalized_natiso_map (U i i le_rfl ⋙ U i j h) (U i j h)
        (by rw [hUid i]; rfl) (gamma i i j le_rfl h) (hgammaLeft i j h) f
      change (gamma i i j le_rfl h).inv.app X ≫
        (U i j h).map ((U i i le_rfl).map f) ≫ (gamma i i j le_rfl h).hom.app Y =
        (U i j h).map f at hn
      rw [hn]
      exact (eqToIso (hUid j)).inv.naturality ((U i j h).map f))

private theorem normalized_coefficient_identity
    {A : Type u} [SmallCategory A] {E : Type v} [Category.{w} E]
    (G : A ⥤ A) (hG : G = 𝟭 A) (H : A ⥤ E) (a : G ⋙ H ≅ H)
    (ha : HEq a (Iso.refl H)) (X : A) :
    H.map ((eqToIso hG).inv.app X) ≫ a.hom.app X = 𝟙 (H.obj X) := by
  subst hG
  rw [eq_of_heq ha]
  simp

/-- The coefficient image of theta is delta inverse, with its endpoints. -/
theorem theta_coefficients
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hgammaLeft : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i i k le_rfl h) (Iso.refl (U i k h)))
    (hdeltaId : ∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i)))
    (i j : I) (h : i ≤ j) (X : C i) :
    Arrow.mk ((coefficients C U D v delta j).map
      ((theta C U gamma hUid hgammaLeft i j h).hom.app X)) =
        Arrow.mk ((delta i j h).inv.app X) := by
  apply congrArg Arrow.mk
  change (delta i j h).inv.app X ≫
    (v j).map ((eqToIso (hUid j)).inv.app ((U i j h).obj X)) ≫
    (delta j j le_rfl).hom.app ((U i j h).obj X) = (delta i j h).inv.app X
  rw [normalized_coefficient_identity (U j j le_rfl) (hUid j) (v j)
    (delta j j le_rfl) (hdeltaId j)]
  exact Category.comp_id _

end CategoryTheory.SiteSystemPairs
