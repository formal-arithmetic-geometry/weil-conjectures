/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor
public import Mathlib.Order.Directed
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# The pair category of a directed system of categories

Let `ι` be a directed preorder and `F : LocallyDiscrete ι ⥤ᵖ Cat` a pseudofunctor: categories
`F i` with transition functors `T_{j/i} : F i ⥤ F j` for `i ≤ j`, together with the coherent
isomorphisms `T_{i/i} ≅ 𝟭` and `T_{k/i} ≅ T_{k/j} ∘ T_{j/i}`. The *pair category*
`PairCategory F` is the filtered `2`-colimit of `F`, described explicitly:

* an object is a pair `(i, A)` with `A : F i`;
* a *representative* of a morphism `(i, A) ⟶ (j, B)` is a stage `k ≥ i, j` with a morphism
  `u : T_{k/i} A ⟶ T_{k/j} B` of `F k`;
* a representative is *transported* to a further stage `k ≤ k'` by conjugating `T_{k'/k} u` by
  the composition isomorphisms, and two representatives are equivalent if their transports to
  some common stage agree;
* morphisms are the equivalence classes, composed after transport to a common stage.

This is blueprint `def-weil-pbc-finite-stage-pair-category`, for `ι` the poset of finite
subextensions `ℚ_ℓ ⊆ E ⊆ ℚ̄_ℓ` and `F E = D(T, E)`. The facts that the relation is an
equivalence relation, that transport is compatible with composition (`(u_N)_P = u_P`), and that
every finite diagram is represented at one stage are the first part of blueprint
`prop-weil-pbc-common-stage-calculus`.

## Main definitions

- `CategoryTheory.PairCategory F` : the pair category.
- `CategoryTheory.PairCategory.Rep` : morphism representatives, `Rep.toStage` their transport.
- `CategoryTheory.PairCategory.homMk` : the class of a representative.
- `CategoryTheory.PairCategory.ι F i : F i ⥤ PairCategory F` : the inclusion of a stage.
- `CategoryTheory.PairCategory.isoToStage` : `(i, A) ≅ (k, T_{k/i} A)`.

## Main results

- `CategoryTheory.PairCategory.homMk_eq_homMk_iff` : two representatives define the same
  morphism iff their transports to some common stage agree.
- `CategoryTheory.PairCategory.homMk_comp_homMk` : composition is computed at any common stage.
- `CategoryTheory.PairCategory.exists_eq_homMk` : every morphism is represented at every large
  enough stage.
-/

@[expose] public section

universe w v u

open CategoryTheory Category Bicategory

namespace CategoryTheory

variable {ι : Type w} [Preorder ι] (F : Pseudofunctor (LocallyDiscrete ι) Cat.{v, u})

namespace Pseudofunctor

/-- The transition functor `T_{j/i} : F i ⥤ F j` of a pseudofunctor from a preorder, for
`i ≤ j`. -/
abbrev transition {i j : ι} (h : i ≤ j) : F.obj ⟨i⟩ ⥤ F.obj ⟨j⟩ :=
  (F.map (homOfLE h).toLoc).toFunctor

/-- The composition isomorphism `T_{k/i} ≅ T_{j/i} ⋙ T_{k/j}` for `i ≤ j ≤ k`. -/
def transitionComp {i j k : ι} (h₁ : i ≤ j) (h₂ : j ≤ k) (h : i ≤ k) :
    F.transition h ≅ F.transition h₁ ⋙ F.transition h₂ :=
  Cat.Hom.toNatIso (F.mapComp' (homOfLE h₁).toLoc (homOfLE h₂).toLoc (homOfLE h).toLoc rfl)

/-- The unit isomorphism `T_{i/i} ≅ 𝟭`. -/
def transitionId (i : ι) (h : i ≤ i) : F.transition h ≅ 𝟭 _ :=
  Cat.Hom.toNatIso (F.mapId' (homOfLE h).toLoc rfl)

@[reassoc (attr := simp)]
lemma transitionComp_hom_naturality {i j k : ι} (h₁ : i ≤ j) (h₂ : j ≤ k) (h : i ≤ k)
    {A B : F.obj ⟨i⟩} (u : A ⟶ B) :
    (F.transition h).map u ≫ (F.transitionComp h₁ h₂ h).hom.app B =
      (F.transitionComp h₁ h₂ h).hom.app A ≫
        (F.transition h₂).map ((F.transition h₁).map u) :=
  (F.transitionComp h₁ h₂ h).hom.naturality u

@[reassoc (attr := simp)]
lemma transitionComp_inv_naturality {i j k : ι} (h₁ : i ≤ j) (h₂ : j ≤ k) (h : i ≤ k)
    {A B : F.obj ⟨i⟩} (u : A ⟶ B) :
    (F.transition h₂).map ((F.transition h₁).map u) ≫ (F.transitionComp h₁ h₂ h).inv.app B =
      (F.transitionComp h₁ h₂ h).inv.app A ≫ (F.transition h).map u :=
  (F.transitionComp h₁ h₂ h).inv.naturality u

@[reassoc (attr := simp)]
lemma transitionComp_hom_inv_id_app {i j k : ι} (h₁ : i ≤ j) (h₂ : j ≤ k) (h : i ≤ k)
    (A : F.obj ⟨i⟩) :
    (F.transitionComp h₁ h₂ h).hom.app A ≫ (F.transitionComp h₁ h₂ h).inv.app A = 𝟙 _ :=
  (F.transitionComp h₁ h₂ h).hom_inv_id_app A

@[reassoc (attr := simp)]
lemma transitionComp_inv_hom_id_app {i j k : ι} (h₁ : i ≤ j) (h₂ : j ≤ k) (h : i ≤ k)
    (A : F.obj ⟨i⟩) :
    (F.transitionComp h₁ h₂ h).inv.app A ≫ (F.transitionComp h₁ h₂ h).hom.app A = 𝟙 _ :=
  (F.transitionComp h₁ h₂ h).inv_hom_id_app A

/-- The associativity of the composition isomorphisms, for `i ≤ j ≤ k ≤ l`. -/
@[reassoc]
lemma transitionComp_assoc {i j k l : ι} (h₁ : i ≤ j) (h₂ : j ≤ k) (h₃ : k ≤ l)
    (h₁₂ : i ≤ k) (h₂₃ : j ≤ l) (h : i ≤ l) (A : F.obj ⟨i⟩) :
    (F.transitionComp h₁₂ h₃ h).hom.app A ≫
        (F.transition h₃).map ((F.transitionComp h₁ h₂ h₁₂).hom.app A) =
      (F.transitionComp h₁ h₂₃ h).hom.app A ≫
        (F.transitionComp h₂ h₃ h₂₃).hom.app ((F.transition h₁).obj A) := by
  have := F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app (homOfLE h₁).toLoc (homOfLE h₂).toLoc
    (homOfLE h₃).toLoc (homOfLE h₁₂).toLoc (homOfLE h₂₃).toLoc (homOfLE h).toLoc rfl rfl rfl A
  rw [← cancel_epi ((F.transitionComp h₁₂ h₃ h).inv.app A)]
  simp only [transitionComp_inv_hom_id_app_assoc]
  rw [← reassoc_of% this]
  simp [transitionComp]

/-- The associativity of the inverses of the composition isomorphisms. -/
@[reassoc]
lemma transitionComp_assoc_inv {i j k l : ι} (h₁ : i ≤ j) (h₂ : j ≤ k) (h₃ : k ≤ l)
    (h₁₂ : i ≤ k) (h₂₃ : j ≤ l) (h : i ≤ l) (A : F.obj ⟨i⟩) :
    (F.transition h₃).map ((F.transitionComp h₁ h₂ h₁₂).inv.app A) ≫
        (F.transitionComp h₁₂ h₃ h).inv.app A =
      (F.transitionComp h₂ h₃ h₂₃).inv.app ((F.transition h₁).obj A) ≫
        (F.transitionComp h₁ h₂₃ h).inv.app A := by
  rw [← cancel_epi ((F.transitionComp h₁₂ h₃ h).hom.app A ≫
    (F.transition h₃).map ((F.transitionComp h₁ h₂ h₁₂).hom.app A))]
  conv_rhs => rw [transitionComp_assoc]
  simp [← Functor.map_comp_assoc]

/-- The unit law of the composition isomorphisms, for `i ≤ i ≤ j`. -/
@[reassoc]
lemma transitionComp_id_left {i j : ι} (h₁ : i ≤ i) (h : i ≤ j) (A : F.obj ⟨i⟩) :
    (F.transitionComp h₁ h h).hom.app A =
      (F.transition h).map ((F.transitionId i h₁).inv.app A) := by
  have := F.mapComp'_id_comp_hom_app (homOfLE h).toLoc A
  simpa [transitionComp, transitionId, mapId'_eq_mapId] using this

/-- The unit law of the composition isomorphisms, for `i ≤ j ≤ j`. -/
@[reassoc]
lemma transitionComp_id_right {i j : ι} (h : i ≤ j) (h₂ : j ≤ j) (A : F.obj ⟨i⟩) :
    (F.transitionComp h h₂ h).hom.app A =
      (F.transitionId j h₂).inv.app ((F.transition h).obj A) := by
  have := F.mapComp'_comp_id_hom_app (homOfLE h).toLoc A
  simpa [transitionComp, transitionId, mapId'_eq_mapId] using this

end Pseudofunctor

open Pseudofunctor

/-- Blueprint `def-weil-pbc-finite-stage-pair-category`: the *pair category* of a pseudofunctor
`F` from a directed preorder to categories, i.e. its filtered `2`-colimit. An object is a pair
`(i, A)` with `A : F i`; morphisms are classes of representatives at common stages (see
`CategoryTheory.PairCategory.Rep`). -/
structure PairCategory where
  /-- The stage of the object. -/
  idx : ι
  /-- The object at that stage. -/
  obj : F.obj ⟨idx⟩

namespace PairCategory

variable {F}

/-- The image `T_{k/i} A` of an object `(i, A)` at a stage `k ≥ i`. -/
abbrev at_ (X : PairCategory F) {k : ι} (h : X.idx ≤ k) : F.obj ⟨k⟩ :=
  (F.transition h).obj X.obj

/-- Transport `u_{k'} = γ⁻¹ ∘ T_{k'/k}(u) ∘ γ` of a morphism between images of objects at a stage
`k` to a further stage `k'`. -/
def trHom {X Y : PairCategory F} {k k' : ι} (h : k ≤ k') (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
    (hX' : X.idx ≤ k') (hY' : Y.idx ≤ k') (u : X.at_ hX ⟶ Y.at_ hY) :
    X.at_ hX' ⟶ Y.at_ hY' :=
  (F.transitionComp hX h hX').hom.app X.obj ≫ (F.transition h).map u ≫
    (F.transitionComp hY h hY').inv.app Y.obj

section trHom

variable {X Y Z : PairCategory F} {k k' k'' : ι}

@[simp]
lemma trHom_id (h : k ≤ k') (hX : X.idx ≤ k) (hX' : X.idx ≤ k') :
    trHom h hX hX hX' hX' (𝟙 _) = 𝟙 _ := by
  simp [trHom]

@[reassoc]
lemma trHom_comp (h : k ≤ k') (hX : X.idx ≤ k) (hY : Y.idx ≤ k) (hZ : Z.idx ≤ k)
    (hX' : X.idx ≤ k') (hY' : Y.idx ≤ k') (hZ' : Z.idx ≤ k')
    (u : X.at_ hX ⟶ Y.at_ hY) (v : Y.at_ hY ⟶ Z.at_ hZ) :
    trHom h hX hZ hX' hZ' (u ≫ v) = trHom h hX hY hX' hY' u ≫ trHom h hY hZ hY' hZ' v := by
  simp [trHom]

lemma trHom_refl (h : k ≤ k) (hX : X.idx ≤ k) (hY : Y.idx ≤ k) (u : X.at_ hX ⟶ Y.at_ hY) :
    trHom h hX hY hX hY u = u := by
  simp [trHom, F.transitionComp_id_right]

lemma trHom_trHom (h : k ≤ k') (h' : k' ≤ k'') (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
    (hX' : X.idx ≤ k') (hY' : Y.idx ≤ k') (hX'' : X.idx ≤ k'') (hY'' : Y.idx ≤ k'')
    (u : X.at_ hX ⟶ Y.at_ hY) :
    trHom h' hX' hY' hX'' hY'' (trHom h hX hY hX' hY' u) =
      trHom (h.trans h') hX hY hX'' hY'' u := by
  have hXa := F.transitionComp_assoc hX h h' hX' (h.trans h') hX'' X.obj
  have hYa := F.transitionComp_assoc hY h h' hY' (h.trans h') hY'' Y.obj
  simp only [trHom, Functor.map_comp, assoc]
  have hYa := F.transitionComp_assoc_inv hY h h' hY' (h.trans h') hY'' Y.obj
  simp only [trHom, Functor.map_comp, assoc]
  rw [reassoc_of% hXa, reassoc_of% hYa]
  simp

end trHom

variable (F) in
/-- A *representative* `(k, u)` of a morphism `(i, A) ⟶ (j, B)` of the pair category: a stage
`k ≥ i, j` and a morphism `u : T_{k/i} A ⟶ T_{k/j} B` of `F k`. -/
structure Rep (X Y : PairCategory F) where
  /-- The stage of the representative. -/
  stage : ι
  le₁ : X.idx ≤ stage
  le₂ : Y.idx ≤ stage
  /-- The morphism at that stage. -/
  hom : X.at_ le₁ ⟶ Y.at_ le₂

namespace Rep

variable {X Y Z : PairCategory F}

@[ext]
lemma ext' {r s : Rep X Y} (h : r.stage = s.stage)
    (h' : r.hom = eqToHom (by subst h; rfl) ≫ s.hom ≫ eqToHom (by subst h; rfl)) : r = s := by
  obtain ⟨k, _, _, u⟩ := r
  obtain ⟨k', _, _, v⟩ := s
  obtain rfl : k = k' := h
  simp only [eqToHom_refl, id_comp, comp_id] at h'
  subst h'
  rfl

/-- The transport `u_{k}` of a representative to a further stage `k`. -/
def toStage (r : Rep X Y) (k : ι) (h : r.stage ≤ k) : Rep X Y :=
  ⟨k, r.le₁.trans h, r.le₂.trans h, trHom h r.le₁ r.le₂ _ _ r.hom⟩

@[simp]
lemma toStage_stage (r : Rep X Y) (k : ι) (h : r.stage ≤ k) : (r.toStage k h).stage = k := rfl

lemma toStage_hom (r : Rep X Y) (k : ι) (h : r.stage ≤ k) :
    (r.toStage k h).hom = trHom h r.le₁ r.le₂ _ _ r.hom := rfl

/-- Transport is transitive: `(u_N)_P = u_P`. -/
@[simp]
lemma toStage_toStage (r : Rep X Y) {k k' : ι} (h : r.stage ≤ k) (h' : k ≤ k') :
    (r.toStage k h).toStage k' h' = r.toStage k' (h.trans h') := by
  obtain ⟨s, h₁, h₂, u⟩ := r
  simp only [toStage, trHom_trHom]

@[simp]
lemma toStage_self (r : Rep X Y) (h : r.stage ≤ r.stage) : r.toStage r.stage h = r := by
  obtain ⟨s, h₁, h₂, u⟩ := r
  simp only [toStage, trHom_refl]

/-- Two representatives are equivalent if their transports to some common stage agree. -/
def Rel (r s : Rep X Y) : Prop :=
  ∃ (k : ι) (hr : r.stage ≤ k) (hs : s.stage ≤ k), r.toStage k hr = s.toStage k hs

lemma Rel.toStage_eq {r s : Rep X Y} {k : ι} (hr : r.stage ≤ k) (hs : s.stage ≤ k)
    (h : r.toStage k hr = s.toStage k hs) {k' : ι} (h' : k ≤ k') :
    r.toStage k' (hr.trans h') = s.toStage k' (hs.trans h') := by
  rw [← toStage_toStage r hr h', ← toStage_toStage s hs h', h]

variable [IsDirected ι (· ≤ ·)]

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the relation of having equal transports at
some common stage is an equivalence relation. -/
lemma rel_equivalence : Equivalence (Rel (X := X) (Y := Y)) where
  refl r := ⟨r.stage, le_rfl, le_rfl, rfl⟩
  symm := fun ⟨k, hr, hs, h⟩ ↦ ⟨k, hs, hr, h.symm⟩
  trans := fun ⟨k₁, hr, hs, h₁⟩ ⟨k₂, hs', ht, h₂⟩ ↦ by
    obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) k₁ k₂
    refine ⟨k, hr.trans hk₁, ht.trans hk₂, ?_⟩
    rw [Rel.toStage_eq hr hs h₁ hk₁, ← Rel.toStage_eq hs' ht h₂ hk₂]

instance setoid (X Y : PairCategory F) : Setoid (Rep X Y) :=
  ⟨Rel, rel_equivalence⟩

/-- The composite of two representatives, computed at a common stage `k`. -/
def compAt (r : Rep X Y) (s : Rep Y Z) (k : ι) (hr : r.stage ≤ k) (hs : s.stage ≤ k) :
    Rep X Z :=
  ⟨k, r.le₁.trans hr, s.le₂.trans hs, (r.toStage k hr).hom ≫ (s.toStage k hs).hom⟩

omit [IsDirected ι (· ≤ ·)] in
lemma compAt_toStage (r : Rep X Y) (s : Rep Y Z) {k k' : ι} (hr : r.stage ≤ k)
    (hs : s.stage ≤ k) (h : k ≤ k') :
    (compAt r s k hr hs).toStage k' h = compAt r s k' (hr.trans h) (hs.trans h) := by
  simp only [compAt, toStage, trHom_comp, trHom_trHom]

lemma compAt_rel (r : Rep X Y) (s : Rep Y Z) {k k' : ι} (hr : r.stage ≤ k)
    (hs : s.stage ≤ k) (hr' : r.stage ≤ k') (hs' : s.stage ≤ k') :
    compAt r s k hr hs ≈ compAt r s k' hr' hs' := by
  obtain ⟨k'', h, h'⟩ := directed_of (· ≤ ·) k k'
  exact ⟨k'', h, h', by rw [compAt_toStage, compAt_toStage]⟩

lemma compAt_rel_compAt {r r' : Rep X Y} {s s' : Rep Y Z} (hr : r ≈ r') (hs : s ≈ s')
    {k k' : ι} (h₁ : r.stage ≤ k) (h₂ : s.stage ≤ k) (h₁' : r'.stage ≤ k')
    (h₂' : s'.stage ≤ k') : compAt r s k h₁ h₂ ≈ compAt r' s' k' h₁' h₂' := by
  obtain ⟨k₁, a₁, b₁, e₁⟩ := hr
  obtain ⟨k₂, a₂, b₂, e₂⟩ := hs
  obtain ⟨m, hm₁, hm₂⟩ := directed_of (· ≤ ·) k₁ k₂
  obtain ⟨n, hn₁, hn₂⟩ := directed_of (· ≤ ·) m k
  obtain ⟨p, hp₁, hp₂⟩ := directed_of (· ≤ ·) n k'
  refine (compAt_rel r s h₁ h₂ (h₁.trans (hn₂.trans hp₁)) (h₂.trans (hn₂.trans hp₁))).trans
    ((?_ : _ ≈ _).trans (compAt_rel r' s' _ _ h₁' h₂'))
  · exact b₁.trans (hm₁.trans (hn₁.trans hp₁))
  · exact b₂.trans (hm₂.trans (hn₁.trans hp₁))
  refine ⟨p, le_rfl, le_rfl, ?_⟩
  simp only [toStage_self]
  have e₁' := Rel.toStage_eq a₁ b₁ e₁ (hm₁.trans (hn₁.trans hp₁))
  have e₂' := Rel.toStage_eq a₂ b₂ e₂ (hm₂.trans (hn₁.trans hp₁))
  simp only [compAt, e₁', e₂']

end Rep

variable [IsDirected ι (· ≤ ·)]

/-- The morphisms of the pair category: classes of representatives. -/
def Hom (X Y : PairCategory F) : Type _ := Quotient (Rep.setoid X Y)

/-- The class of a representative. -/
def homMk' {X Y : PairCategory F} (r : Rep X Y) : Hom X Y := Quotient.mk _ r

/-- The composite of two morphisms, computed at a common stage. -/
noncomputable def Hom.comp {X Y Z : PairCategory F} : Hom X Y → Hom Y Z → Hom X Z :=
  Quotient.lift₂
    (fun r s ↦ homMk' (Rep.compAt r s _ (directed_of (· ≤ ·) r.stage s.stage).choose_spec.1
      (directed_of (· ≤ ·) r.stage s.stage).choose_spec.2))
    (fun _ _ _ _ hr hs ↦ Quotient.sound (Rep.compAt_rel_compAt hr hs _ _ _ _))

/-- The identity of `(i, A)`, represented by `𝟙 (T_{i/i} A)`. -/
def Hom.id (X : PairCategory F) : Hom X X := homMk' ⟨X.idx, le_rfl, le_rfl, 𝟙 _⟩

lemma homMk'_comp_homMk' {X Y Z : PairCategory F} (r : Rep X Y) (s : Rep Y Z) (k : ι)
    (hr : r.stage ≤ k) (hs : s.stage ≤ k) :
    Hom.comp (homMk' r) (homMk' s) = homMk' (Rep.compAt r s k hr hs) :=
  Quotient.sound (Rep.compAt_rel r s _ _ _ _)

lemma homMk'_toStage {X Y : PairCategory F} (r : Rep X Y) (k : ι) (h : r.stage ≤ k) :
    homMk' (r.toStage k h) = homMk' r :=
  Quotient.sound ⟨k, le_rfl, h, by simp⟩

lemma homMk'_eq_homMk'_iff {X Y : PairCategory F} (r s : Rep X Y) :
    homMk' r = homMk' s ↔ ∃ (k : ι) (hr : r.stage ≤ k) (hs : s.stage ≤ k),
      r.toStage k hr = s.toStage k hs :=
  Quotient.eq (r := Rep.setoid X Y)

lemma Hom.id_eq (X : PairCategory F) (k : ι) (h : X.idx ≤ k) :
    Hom.id X = homMk' ⟨k, h, h, 𝟙 _⟩ := by
  rw [Hom.id, ← homMk'_toStage _ k h]
  congr 1
  ext <;> simp [Rep.toStage]

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the pair category is a category, with
identities, composition computed after transport to a common stage. -/
noncomputable instance category : Category.{max w v} (PairCategory F) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp {X Y} f := by
    obtain ⟨r, rfl⟩ := Quotient.exists_rep f
    change Hom.comp (Hom.id X) (homMk' r) = homMk' r
    rw [Hom.id_eq X r.stage r.le₁, homMk'_comp_homMk' _ _ r.stage le_rfl le_rfl]
    congr 1
    ext <;> simp [Rep.compAt, Rep.toStage, trHom_refl]
  comp_id {X Y} f := by
    obtain ⟨r, rfl⟩ := Quotient.exists_rep f
    change Hom.comp (homMk' r) (Hom.id Y) = homMk' r
    rw [Hom.id_eq Y r.stage r.le₂, homMk'_comp_homMk' _ _ r.stage le_rfl le_rfl]
    congr 1
    ext <;> simp [Rep.compAt, Rep.toStage, trHom_refl]
  assoc {W X Y Z} f g h := by
    obtain ⟨r, rfl⟩ := Quotient.exists_rep f
    obtain ⟨s, rfl⟩ := Quotient.exists_rep g
    obtain ⟨t, rfl⟩ := Quotient.exists_rep h
    obtain ⟨k₁, h₁, h₂⟩ := directed_of (· ≤ ·) r.stage s.stage
    obtain ⟨k, h₃, h₄⟩ := directed_of (· ≤ ·) k₁ t.stage
    change Hom.comp (Hom.comp (homMk' r) (homMk' s)) (homMk' t) =
      Hom.comp (homMk' r) (Hom.comp (homMk' s) (homMk' t))
    rw [homMk'_comp_homMk' r s k (h₁.trans h₃) (h₂.trans h₃),
      homMk'_comp_homMk' s t k (h₂.trans h₃) h₄,
      homMk'_comp_homMk' _ _ k le_rfl h₄, homMk'_comp_homMk' _ _ k (h₁.trans h₃) le_rfl]
    congr 1
    ext <;> simp [Rep.compAt, Rep.toStage, trHom_refl]

/-- The morphism of the pair category defined by a representative `(k, u)`. -/
noncomputable def homMk {X Y : PairCategory F} {k : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
    (u : X.at_ hX ⟶ Y.at_ hY) : X ⟶ Y :=
  homMk' ⟨k, hX, hY, u⟩

lemma exists_rep {X Y : PairCategory F} (f : X ⟶ Y) :
    ∃ (k : ι) (hX : X.idx ≤ k) (hY : Y.idx ≤ k) (u : X.at_ hX ⟶ Y.at_ hY), f = homMk hX hY u := by
  obtain ⟨⟨k, hX, hY, u⟩, rfl⟩ := Quotient.exists_rep f
  exact ⟨k, hX, hY, u, rfl⟩

/-- A representative can be transported to any further stage. -/
lemma homMk_trHom {X Y : PairCategory F} {k k' : ι} (h : k ≤ k') (hX : X.idx ≤ k)
    (hY : Y.idx ≤ k) (hX' : X.idx ≤ k') (hY' : Y.idx ≤ k') (u : X.at_ hX ⟶ Y.at_ hY) :
    homMk hX' hY' (trHom h hX hY hX' hY' u) = homMk hX hY u :=
  homMk'_toStage ⟨k, hX, hY, u⟩ k' h

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: every morphism is represented at every
large enough stage. -/
lemma exists_eq_homMk {X Y : PairCategory F} (f : X ⟶ Y) :
    ∃ k₀, ∀ (k : ι) (_ : k₀ ≤ k), ∃ (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
      (u : X.at_ hX ⟶ Y.at_ hY), f = homMk hX hY u := by
  obtain ⟨k₀, hX, hY, u, rfl⟩ := exists_rep f
  exact ⟨k₀, fun k h ↦ ⟨hX.trans h, hY.trans h, _, (homMk_trHom h hX hY _ _ u).symm⟩⟩

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: two representatives at a common stage define
the same morphism iff they agree after transport to some further stage. -/
lemma homMk_eq_homMk_iff {X Y : PairCategory F} {k : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
    (u v : X.at_ hX ⟶ Y.at_ hY) :
    homMk hX hY u = homMk hX hY v ↔ ∃ (k' : ι) (h : k ≤ k'),
      trHom h hX hY (hX.trans h) (hY.trans h) u = trHom h hX hY (hX.trans h) (hY.trans h) v := by
  refine (homMk'_eq_homMk'_iff _ _).trans ⟨fun ⟨k', h, _, e⟩ ↦ ⟨k', h, ?_⟩,
    fun ⟨k', h, e⟩ ↦ ⟨k', h, h, ?_⟩⟩
  · exact congrArg Rep.hom e
  · simp only [Rep.toStage, e]

@[reassoc]
lemma homMk_comp_homMk {X Y Z : PairCategory F} {k : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
    (hZ : Z.idx ≤ k) (u : X.at_ hX ⟶ Y.at_ hY) (v : Y.at_ hY ⟶ Z.at_ hZ) :
    homMk hX hY u ≫ homMk hY hZ v = homMk hX hZ (u ≫ v) := by
  refine (homMk'_comp_homMk' _ _ k le_rfl le_rfl).trans ?_
  congr 1
  ext <;> simp [Rep.compAt, Rep.toStage, trHom_refl]

@[simp]
lemma homMk_id {X : PairCategory F} {k : ι} (hX : X.idx ≤ k) : homMk hX hX (𝟙 _) = 𝟙 X :=
  (Hom.id_eq X k hX).symm

lemma id_eq_homMk (X : PairCategory F) : 𝟙 X = homMk (le_refl X.idx) le_rfl (𝟙 _) := rfl

lemma homMk_eq_homMk_iff' {X Y : PairCategory F} {k k' : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
    (hX' : X.idx ≤ k') (hY' : Y.idx ≤ k') (u : X.at_ hX ⟶ Y.at_ hY)
    (v : X.at_ hX' ⟶ Y.at_ hY') :
    homMk hX hY u = homMk hX' hY' v ↔ ∃ (m : ι) (h : k ≤ m) (h' : k' ≤ m),
      trHom h hX hY (hX.trans h) (hY.trans h) u = trHom h' hX' hY' (hX.trans h) (hY.trans h) v := by
  refine (homMk'_eq_homMk'_iff _ _).trans ⟨fun ⟨m, h, h', e⟩ ↦ ⟨m, h, h', ?_⟩,
    fun ⟨m, h, h', e⟩ ↦ ⟨m, h, h', ?_⟩⟩
  · exact congrArg Rep.hom e
  · simp only [Rep.toStage, e]

variable (F) in
/-- The inclusion `j_i : F i ⥤ PairCategory F` of a stage, `A ↦ (i, A)`. -/
noncomputable def ι (i : ι) : F.obj ⟨i⟩ ⥤ PairCategory F where
  obj A := ⟨i, A⟩
  map {A B} u := homMk (X := ⟨i, A⟩) (Y := ⟨i, B⟩) le_rfl le_rfl
    ((F.transitionId i le_rfl).hom.app A ≫ u ≫ (F.transitionId i le_rfl).inv.app B)
  map_id A := by simp
  map_comp u v := by simp [homMk_comp_homMk]

@[simp]
lemma ι_obj_idx (i : ι) (A : F.obj ⟨i⟩) : ((ι F i).obj A).idx = i := rfl

@[simp]
lemma ι_obj_obj (i : ι) (A : F.obj ⟨i⟩) : ((ι F i).obj A).obj = A := rfl

/-- An object `(i, A)` is isomorphic to its image `(k, T_{k/i} A)` at any further stage. -/
noncomputable def isoToStage (X : PairCategory F) {k : ι} (h : X.idx ≤ k) :
    X ≅ ⟨k, X.at_ h⟩ where
  hom := homMk (Y := ⟨k, X.at_ h⟩) h le_rfl ((F.transitionId k le_rfl).inv.app _)
  inv := homMk (X := ⟨k, X.at_ h⟩) le_rfl h ((F.transitionId k le_rfl).hom.app _)
  hom_inv_id := by simp [homMk_comp_homMk]
  inv_hom_id := by simp [homMk_comp_homMk]

/-- Every morphism is conjugate to the image of a morphism of a stage: the morphism represented
by `(k, u)` is `(isoToStage X) ≫ j_k(u) ≫ (isoToStage Y)⁻¹`. -/
lemma homMk_eq {X Y : PairCategory F} {k : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
    (u : X.at_ hX ⟶ Y.at_ hY) :
    homMk hX hY u = (isoToStage X hX).hom ≫ (ι F k).map u ≫ (isoToStage Y hY).inv := by
  simp [isoToStage, ι, homMk_comp_homMk]

end PairCategory

end CategoryTheory
