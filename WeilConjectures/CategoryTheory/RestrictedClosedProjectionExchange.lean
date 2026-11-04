/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering

/-!
# Yoneda exchange on full subcategories

Source: exceptional internal-Hom exchange, displayed Hom chain and Yoneda argument.
(blueprint: lem-trf-restricted-closed-projection-exchange).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v u' v' w z

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace CategoryTheory


private theorem iso_of_homEquiv
    {C : Type u} [Category.{v} C] {J : Type w} [Category.{z} J]
    (S T : J ⥤ C)
    (E : ∀ (P : C) (j : J), (P ⟶ S.obj j) ≃ (P ⟶ T.obj j))
    (hP : ∀ {P P' : C} (p : P' ⟶ P) (j : J) (a : P ⟶ S.obj j),
      E P' j (p ≫ a) = p ≫ E P j a)
    (hJ : ∀ (P : C) {j j' : J} (f : j ⟶ j') (a : P ⟶ S.obj j),
      E P j' (a ≫ S.map f) = E P j a ≫ T.map f) :
    ∃! e : S ≅ T, ∀ j, e.hom.app j = E (S.obj j) j (𝟙 _) := by
  let h (j : J) := E (S.obj j) j (𝟙 _)
  have factor (P : C) (j : J) (a : P ⟶ S.obj j) :
      E P j a = a ≫ h j := by
    simpa only [Category.comp_id] using hP a j (𝟙 _)
  let e (j : J) : S.obj j ≅ T.obj j :=
    { hom := h j
      inv := (E (T.obj j) j).symm (𝟙 _)
      hom_inv_id := by
        apply (E (S.obj j) j).injective
        rw [factor, Category.assoc, ← factor, Equiv.apply_symm_apply,
          Category.comp_id]
      inv_hom_id := by
        rw [← factor, Equiv.apply_symm_apply] }
  refine ⟨NatIso.ofComponents e (fun {j j'} f ↦ ?_), fun _ ↦ rfl, ?_⟩
  · have hf := hJ (S.obj j) f (𝟙 _)
    simpa only [Category.id_comp, factor] using hf
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext j
    exact he' j

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [MonoidalClosed D]
  (P : ObjectProperty C) (Q : ObjectProperty D)
  (L : D ⥤ C) (F : P.FullSubcategory ⥤ Q.FullSubcategory)
  (G : Q.FullSubcategory ⥤ P.FullSubcategory)

/-- The ordinary-pullback/exceptional-pullback internal Hom bifunctor.
Source: item, left side of the comparison
(blueprint: lem-trf-restricted-closed-projection-exchange). -/
abbrev restrictedExchangeSource : Q.FullSubcategoryᵒᵖ × Q.FullSubcategory ⥤ C where
  obj j := (ihom (L.obj j.1.unop.obj)).obj (G.obj j.2).obj
  map {j j'} f := (pre (L.map f.1.unop.hom)).app (G.obj j.2).obj ≫
    (ihom (L.obj j'.1.unop.obj)).map (G.map f.2).hom
  map_id j := by
    exact ((((Q.ι ⋙ L).op.prod (G ⋙ P.ι))) ⋙
      Functor.uncurry.obj internalHom).map_id j
  map_comp f g := by
    exact ((((Q.ι ⋙ L).op.prod (G ⋙ P.ι))) ⋙
      Functor.uncurry.obj internalHom).map_comp f g

/-- Internal Hom of the two original inputs.
Source: item, internal Hom before exceptional pullback
(blueprint: lem-trf-restricted-closed-projection-exchange). -/
abbrev restrictedExchangeBase : Q.FullSubcategoryᵒᵖ × Q.FullSubcategory ⥤ D where
  obj j := (ihom j.1.unop.obj).obj j.2.obj
  map {j j'} f := (pre f.1.unop.hom).app j.2.obj ≫
    (ihom j'.1.unop.obj).map f.2.hom
  map_id j := by
    exact ((Q.ι.op.prod Q.ι) ⋙ Functor.uncurry.obj internalHom).map_id j
  map_comp f g := by
    exact ((Q.ι.op.prod Q.ι) ⋙ Functor.uncurry.obj internalHom).map_comp f g

/-- Exceptional pullback of the original internal Hom, restricted to its domain.
Source: item, right side of the comparison
(blueprint: lem-trf-restricted-closed-projection-exchange). -/
@[implicit_reducible]
def restrictedExchangeTarget
    (hQ : ∀ j, Q ((restrictedExchangeBase Q).obj j)) :
    Q.FullSubcategoryᵒᵖ × Q.FullSubcategory ⥤ C :=
  Q.lift (restrictedExchangeBase Q) hQ ⋙ G ⋙ P.ι

variable {P Q L F G}

private def subHomEquiv (A B : P.FullSubcategory) : (A ⟶ B) ≃ (A.obj ⟶ B.obj) where
  toFun a := a.hom
  invFun a := ObjectProperty.homMk a
  left_inv _ := rfl
  right_inv _ := rfl

omit [MonoidalCategory C] [MonoidalClosed C] in
private lemma homMk_comp
    {A B C' : P.FullSubcategory} (a : A.obj ⟶ B.obj) (b : B.obj ⟶ C'.obj) :
    (ObjectProperty.homMk a : A ⟶ B) ≫ ObjectProperty.homMk b =
      ObjectProperty.homMk (a ≫ b) := rfl

private def exchangeHomEquiv
    (adj : F ⊣ G)
    (ht : ∀ (M : Q.FullSubcategory) (K : P.FullSubcategory), P (L.obj M.obj ⊗ K.obj))
    (hQ : ∀ j, Q ((restrictedExchangeBase Q).obj j))
    (hH : ∀ j, P ((restrictedExchangeSource P Q L G).obj j))
    (q : ∀ (M : Q.FullSubcategory) (K : P.FullSubcategory),
      M.obj ⊗ (F.obj K).obj ≅ (F.obj ⟨L.obj M.obj ⊗ K.obj, ht M K⟩).obj)
    (K : P.FullSubcategory) (j : Q.FullSubcategoryᵒᵖ × Q.FullSubcategory) :
    (K ⟶ ⟨(restrictedExchangeSource P Q L G).obj j, hH j⟩) ≃
      (K ⟶ G.obj ⟨(restrictedExchangeBase Q).obj j, hQ j⟩) :=
  (subHomEquiv _ _).trans <|
    ((ihom.adjunction (L.obj j.1.unop.obj)).homEquiv K.obj (G.obj j.2).obj).symm.trans <|
    (subHomEquiv ⟨_, ht j.1.unop K⟩ (G.obj j.2)).symm.trans <|
    (adj.homEquiv _ j.2).symm.trans <|
    (subHomEquiv _ _).trans <|
    (Iso.homCongr (q j.1.unop K).symm (Iso.refl _)).trans <|
    ((ihom.adjunction j.1.unop.obj).homEquiv (F.obj K).obj j.2.obj).trans <|
    (subHomEquiv (F.obj K) ⟨_, hQ j⟩).symm.trans (adj.homEquiv _ _)

private lemma exchangeHomEquiv_apply
    (adj : F ⊣ G)
    (ht : ∀ (M : Q.FullSubcategory) (K : P.FullSubcategory), P (L.obj M.obj ⊗ K.obj))
    (hQ : ∀ j, Q ((restrictedExchangeBase Q).obj j))
    (hH : ∀ j, P ((restrictedExchangeSource P Q L G).obj j))
    (q : ∀ (M : Q.FullSubcategory) (K : P.FullSubcategory),
      M.obj ⊗ (F.obj K).obj ≅ (F.obj ⟨L.obj M.obj ⊗ K.obj, ht M K⟩).obj)
    (K : P.FullSubcategory) (j : Q.FullSubcategoryᵒᵖ × Q.FullSubcategory)
    (a : K ⟶ ⟨(restrictedExchangeSource P Q L G).obj j, hH j⟩) :
    exchangeHomEquiv adj ht hQ hH q K j a =
      adj.homEquiv K ⟨_, hQ j⟩ (ObjectProperty.homMk
        (curry ((q j.1.unop K).hom ≫
          ((adj.homEquiv ⟨_, ht j.1.unop K⟩ j.2).symm
            (ObjectProperty.homMk (uncurry a.hom))).hom))) := by
  simp [exchangeHomEquiv, subHomEquiv, Iso.homCongr, curry, uncurry]


private lemma exchangeHomEquiv_natural_test
    (adj : F ⊣ G)
    (ht : ∀ (M : Q.FullSubcategory) (K : P.FullSubcategory), P (L.obj M.obj ⊗ K.obj))
    (hQ : ∀ j, Q ((restrictedExchangeBase Q).obj j))
    (hH : ∀ j, P ((restrictedExchangeSource P Q L G).obj j))
    (q : ∀ (M : Q.FullSubcategory) (K : P.FullSubcategory),
      M.obj ⊗ (F.obj K).obj ≅ (F.obj ⟨L.obj M.obj ⊗ K.obj, ht M K⟩).obj)
    (hq : ∀ (M : Q.FullSubcategory) {K K' : P.FullSubcategory} (p : K ⟶ K'),
      M.obj ◁ (F.map p).hom ≫ (q M K').hom =
        (q M K).hom ≫ (F.map (ObjectProperty.homMk (L.obj M.obj ◁ p.hom))).hom)
    {K K' : P.FullSubcategory} (p : K' ⟶ K)
    (j : Q.FullSubcategoryᵒᵖ × Q.FullSubcategory)
    (a : K ⟶ ⟨(restrictedExchangeSource P Q L G).obj j, hH j⟩) :
    exchangeHomEquiv adj ht hQ hH q K' j (p ≫ a) =
      p ≫ exchangeHomEquiv adj ht hQ hH q K j a := by
  rw [exchangeHomEquiv_apply adj ht hQ hH q K' j (p ≫ a),
    exchangeHomEquiv_apply adj ht hQ hH q K j a]
  simp only [ObjectProperty.FullSubcategory.comp_hom, uncurry_natural_left]
  have htensor :
      (ObjectProperty.homMk (L.obj j.1.unop.obj ◁ p.hom ≫ uncurry a.hom) :
        (⟨_, ht j.1.unop K'⟩ : P.FullSubcategory) ⟶ G.obj j.2) =
      (ObjectProperty.homMk (L.obj j.1.unop.obj ◁ p.hom) :
        (⟨_, ht j.1.unop K'⟩ : P.FullSubcategory) ⟶ ⟨_, ht j.1.unop K⟩) ≫
        ObjectProperty.homMk (uncurry a.hom) := rfl
  rw [htensor, adj.homEquiv_naturality_left_symm]
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [← Category.assoc, ← hq, Category.assoc, curry_natural_left]
  exact adj.homEquiv_naturality_left p _

private lemma exchangeHomEquiv_natural_input
    (adj : F ⊣ G)
    (ht : ∀ (M : Q.FullSubcategory) (K : P.FullSubcategory), P (L.obj M.obj ⊗ K.obj))
    (hQ : ∀ j, Q ((restrictedExchangeBase Q).obj j))
    (hH : ∀ j, P ((restrictedExchangeSource P Q L G).obj j))
    (q : ∀ (M : Q.FullSubcategory) (K : P.FullSubcategory),
      M.obj ⊗ (F.obj K).obj ≅ (F.obj ⟨L.obj M.obj ⊗ K.obj, ht M K⟩).obj)
    (hq : ∀ {M M' : Q.FullSubcategory} (a : M' ⟶ M) (K : P.FullSubcategory),
      a.hom ▷ (F.obj K).obj ≫ (q M K).hom =
        (q M' K).hom ≫ (F.map (ObjectProperty.homMk (L.map a.hom ▷ K.obj))).hom)
    (K : P.FullSubcategory)
    {j j' : Q.FullSubcategoryᵒᵖ × Q.FullSubcategory} (f : j ⟶ j')
    (a : K ⟶ ⟨(restrictedExchangeSource P Q L G).obj j, hH j⟩) :
    exchangeHomEquiv adj ht hQ hH q K j'
        (a ≫ ObjectProperty.homMk ((restrictedExchangeSource P Q L G).map f)) =
      exchangeHomEquiv adj ht hQ hH q K j a ≫
        G.map (ObjectProperty.homMk ((restrictedExchangeBase Q).map f)) := by
  rw [exchangeHomEquiv_apply adj ht hQ hH q K j'
    (a ≫ ObjectProperty.homMk ((restrictedExchangeSource P Q L G).map f)),
    exchangeHomEquiv_apply adj ht hQ hH q K j a]
  have hu : uncurry (a.hom ≫ (restrictedExchangeSource P Q L G).map f) =
      L.map f.1.unop.hom ▷ K.obj ≫ uncurry a.hom ≫ (G.map f.2).hom := by
    change uncurry (a.hom ≫ (pre (L.map f.1.unop.hom)).app _ ≫
      (ihom _).map (G.map f.2).hom) = _
    rw [← Category.assoc, uncurry_natural_right, uncurry_pre_app]
    exact Category.assoc _ _ _
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
  rw [hu]
  have hsub :
      (ObjectProperty.homMk
        (L.map f.1.unop.hom ▷ K.obj ≫ uncurry a.hom ≫ (G.map f.2).hom) :
          (⟨_, ht j'.1.unop K⟩ : P.FullSubcategory) ⟶ G.obj j'.2) =
      (ObjectProperty.homMk (L.map f.1.unop.hom ▷ K.obj) :
        (⟨_, ht j'.1.unop K⟩ : P.FullSubcategory) ⟶ ⟨_, ht j.1.unop K⟩) ≫
        ObjectProperty.homMk (uncurry a.hom) ≫ G.map f.2 := rfl
  rw [hsub, adj.homEquiv_naturality_left_symm,
    adj.homEquiv_naturality_right_symm]
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [← Category.assoc, ← hq]
  simp only [← Category.assoc]
  rw [curry_natural_right]
  simp only [Category.assoc]
  rw [← curry_pre_app]
  simpa only [homMk_comp, Category.assoc] using
    adj.homEquiv_naturality_right
      (ObjectProperty.homMk (curry
        ((q j.1.unop K).hom ≫
          ((adj.homEquiv ⟨_, ht j.1.unop K⟩ j.2).symm
            (ObjectProperty.homMk (uncurry a.hom))).hom)))
    (ObjectProperty.homMk ((restrictedExchangeBase Q).map f) :
      (⟨_, hQ j⟩ : Q.FullSubcategory) ⟶ ⟨_, hQ j'⟩)

/-- A projection isomorphism gives the canonical internal-Hom exchange on full
subcategories. No adjunction on the entire ambient categories is required.

For `M, N` in `Q`, the component `e_{M,N} : Hom(L M, G N) ⟶ G (Hom(M, N))` is the
`F ⊣ G` transpose of the curried composite
```
                         q                         F (ev)                ε_N
  M ⊗ F (Hom(L M, G N)) ──→ F (L M ⊗ Hom(L M, G N)) ──────→ F (G N) ─────→ N
```
and `e` is the unique natural isomorphism with these components.

Source: the Hom chain and Yoneda argument of
lem-trf-exceptional-internal-hom-exchange, proof steps 2--3.
(blueprint: lem-trf-restricted-closed-projection-exchange).

Proof: uncurry on C, use the inverse restricted adjunction, precompose with the
projection isomorphism, curry on D, and apply the restricted adjunction. Naturality
in the test object follows from that of the projection and the two adjunctions.
Naturality in both inputs follows from projection naturality, evaluation and
precomposition in internal Hom. Apply the bijection to the identity of the source
object. The inverse image of the target identity is its inverse, by naturality and
injectivity. Evaluating the Hom chain at the identity gives precisely the stated
double transpose, since the inverse adjunction is F of the map followed by its counit.
-/
theorem restrictedClosedProjectionExchange
    (adj : F ⊣ G)
    (ht : ∀ (M : Q.FullSubcategory) (K : P.FullSubcategory), P (L.obj M.obj ⊗ K.obj))
    (hQ : ∀ j, Q ((restrictedExchangeBase Q).obj j))
    (hH : ∀ j, P ((restrictedExchangeSource P Q L G).obj j))
    (q : ∀ (M : Q.FullSubcategory) (K : P.FullSubcategory),
      M.obj ⊗ (F.obj K).obj ≅ (F.obj ⟨L.obj M.obj ⊗ K.obj, ht M K⟩).obj)
    (hqP : ∀ (M : Q.FullSubcategory) {K K' : P.FullSubcategory} (p : K ⟶ K'),
      M.obj ◁ (F.map p).hom ≫ (q M K').hom =
        (q M K).hom ≫ (F.map (ObjectProperty.homMk (L.obj M.obj ◁ p.hom))).hom)
    (hqM : ∀ {M M' : Q.FullSubcategory} (a : M' ⟶ M) (K : P.FullSubcategory),
      a.hom ▷ (F.obj K).obj ≫ (q M K).hom =
        (q M' K).hom ≫ (F.map (ObjectProperty.homMk (L.map a.hom ▷ K.obj))).hom) :
    ∃! e : restrictedExchangeSource P Q L G ≅ restrictedExchangeTarget P Q G hQ,
      ∀ (M N : Q.FullSubcategory), e.hom.app (op M, N) =
        (adj.homEquiv ⟨_, hH (op M, N)⟩ ⟨_, hQ (op M, N)⟩
          (ObjectProperty.homMk (curry
            ((q M ⟨_, hH (op M, N)⟩).hom ≫
              (F.map (ObjectProperty.homMk ((ihom.ev (L.obj M.obj)).app
                (G.obj N).obj))).hom ≫ (adj.counit.app N).hom)))).hom := by
  let S := P.lift (restrictedExchangeSource P Q L G) hH
  let T := Q.lift (restrictedExchangeBase Q) hQ ⋙ G
  obtain ⟨e, he, hu⟩ := iso_of_homEquiv S T
    (exchangeHomEquiv adj ht hQ hH q)
    (fun p j a ↦ exchangeHomEquiv_natural_test adj ht hQ hH q hqP p j a)
    (fun K {j j'} f a ↦ exchangeHomEquiv_natural_input adj ht hQ hH q hqM K f a)
  let e' : restrictedExchangeSource P Q L G ≅ restrictedExchangeTarget P Q G hQ :=
    Functor.isoWhiskerRight e P.ι
  have he' (M N : Q.FullSubcategory) : e'.hom.app (op M, N) =
      (adj.homEquiv ⟨_, hH (op M, N)⟩ ⟨_, hQ (op M, N)⟩
        (ObjectProperty.homMk (curry
          ((q M ⟨_, hH (op M, N)⟩).hom ≫
            (F.map (ObjectProperty.homMk ((ihom.ev (L.obj M.obj)).app
              (G.obj N).obj))).hom ≫ (adj.counit.app N).hom)))).hom := by
    change (e.hom.app (op M, N)).hom = _
    rw [he]
    have hh := congrArg (fun a : S.obj (op M, N) ⟶ T.obj (op M, N) ↦ a.hom)
      (exchangeHomEquiv_apply adj ht hQ hH q (S.obj (op M, N)) (op M, N) (𝟙 _))
    dsimp [S, ObjectProperty.lift] at hh ⊢
    simp only [uncurry_id_eq_ev, adj.homEquiv_counit,
      ObjectProperty.FullSubcategory.comp_hom] at hh
    convert hh using 1; rfl
  refine ⟨e', he', ?_⟩
  intro e'' he''
  apply Iso.ext
  apply NatTrans.ext
  funext j
  exact (he'' j.1.unop j.2).trans (he' j.1.unop j.2).symm

end CategoryTheory
