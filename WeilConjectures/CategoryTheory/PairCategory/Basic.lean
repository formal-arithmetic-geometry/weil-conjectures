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
- `CategoryTheory.PairCategory.incl F i : F i ⥤ PairCategory F` : the inclusion of a stage.
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
  change (F.transitionComp h₁₂ h₃ h).inv.app A ≫ (F.transitionComp h₁ h₂₃ h).hom.app A =
    (F.transition h₃).map ((F.transitionComp h₁ h₂ h₁₂).hom.app A) ≫
      (F.transitionComp h₂ h₃ h₂₃).inv.app ((F.transition h₁).obj A) at this
  rw [← cancel_mono ((F.transitionComp h₂ h₃ h₂₃).inv.app ((F.transition h₁).obj A))]
  simp only [assoc, transitionComp_hom_inv_id_app]
  rw [← this, transitionComp_hom_inv_id_app_assoc]
  exact (comp_id _).symm

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
  conv_rhs => rw [transitionComp_assoc F h₁ h₂ h₃ h₁₂ h₂₃ h A]
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

/-- The unit law of the composition isomorphisms, for `i ≤ j ≤ j`, inverse form. -/
@[reassoc]
lemma transitionComp_id_right_inv {i j : ι} (h : i ≤ j) (h₂ : j ≤ j) (A : F.obj ⟨i⟩) :
    (F.transitionComp h h₂ h).inv.app A =
      (F.transitionId j h₂).hom.app ((F.transition h).obj A) := by
  rw [← cancel_epi ((F.transitionComp h h₂ h).hom.app A), transitionComp_hom_inv_id_app,
    transitionComp_id_right]
  exact ((F.transitionId j h₂).inv_hom_id_app _).symm

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
  rw [trHom, F.transitionComp_id_right, F.transitionComp_id_right_inv,
    (F.transitionId k h).hom.naturality u]
  simp

lemma trHom_trHom (h : k ≤ k') (h' : k' ≤ k'') (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
    (hX' : X.idx ≤ k') (hY' : Y.idx ≤ k') (hX'' : X.idx ≤ k'') (hY'' : Y.idx ≤ k'')
    (u : X.at_ hX ⟶ Y.at_ hY) :
    trHom h' hX' hY' hX'' hY'' (trHom h hX hY hX' hY' u) =
      trHom (h.trans h') hX hY hX'' hY'' u := by
  have hXa := F.transitionComp_assoc hX h h' hX' (h.trans h') hX'' X.obj
  have hYa := F.transitionComp_assoc_inv hY h h' hY' (h.trans h') hY'' Y.obj
  simp only [trHom, Functor.map_comp, assoc]
  rw [reassoc_of% hXa, hYa]
  simp

end trHom

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

lemma mk_hom_congr {k : ι} {h₁ h₁' : X.idx ≤ k} {h₂ h₂' : Y.idx ≤ k} {u : X.at_ h₁ ⟶ Y.at_ h₂}
    {v : X.at_ h₁' ⟶ Y.at_ h₂'} (e : u = v) : (⟨k, h₁, h₂, u⟩ : Rep X Y) = ⟨k, h₁', h₂', v⟩ := by
  subst e
  rfl

/-- The transport `u_k` of a representative `(s, u)` to a further stage `k`. -/
def homAt (r : Rep X Y) (k : ι) (h : r.stage ≤ k) :
    X.at_ (r.le₁.trans h) ⟶ Y.at_ (r.le₂.trans h) :=
  trHom h r.le₁ r.le₂ _ _ r.hom

/-- Transport is transitive: `(u_N)_P = u_P`. -/
lemma trHom_homAt (r : Rep X Y) {k k' : ι} (h : r.stage ≤ k) (h' : k ≤ k') :
    trHom h' _ _ _ _ (r.homAt k h) = r.homAt k' (h.trans h') :=
  trHom_trHom _ _ _ _ _ _ _ _ _

@[simp]
lemma homAt_self (r : Rep X Y) (h : r.stage ≤ r.stage) : r.homAt r.stage h = r.hom :=
  trHom_refl _ _ _ _

/-- The transport of a representative to a further stage `k`, as a representative. -/
def toStage (r : Rep X Y) (k : ι) (h : r.stage ≤ k) : Rep X Y :=
  ⟨k, r.le₁.trans h, r.le₂.trans h, r.homAt k h⟩

@[simp]
lemma toStage_stage (r : Rep X Y) (k : ι) (h : r.stage ≤ k) : (r.toStage k h).stage = k := rfl

@[simp]
lemma toStage_hom (r : Rep X Y) (k : ι) (h : r.stage ≤ k) : (r.toStage k h).hom = r.homAt k h :=
  rfl

/-- Two representatives are equivalent if their transports to some common stage agree. -/
def Rel (r s : Rep X Y) : Prop :=
  ∃ (k : ι) (hr : r.stage ≤ k) (hs : s.stage ≤ k), r.homAt k hr = s.homAt k hs

lemma homAt_eq_of_le {r s : Rep X Y} {k : ι} (hr : r.stage ≤ k) (hs : s.stage ≤ k)
    (h : r.homAt k hr = s.homAt k hs) {k' : ι} (h' : k ≤ k') :
    r.homAt k' (hr.trans h') = s.homAt k' (hs.trans h') := by
  rw [← trHom_homAt r hr h', ← trHom_homAt s hs h', h]

variable [IsDirected ι (· ≤ ·)]

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the relation of having equal transports at
some common stage is an equivalence relation. -/
lemma rel_equivalence : _root_.Equivalence (Rel (X := X) (Y := Y)) where
  refl r := ⟨r.stage, le_rfl, le_rfl, rfl⟩
  symm := fun ⟨k, hr, hs, h⟩ ↦ ⟨k, hs, hr, h.symm⟩
  trans := fun ⟨k₁, hr, hs, h₁⟩ ⟨k₂, hs', ht, h₂⟩ ↦ by
    obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) k₁ k₂
    exact ⟨k, hr.trans hk₁, ht.trans hk₂,
      (homAt_eq_of_le hr hs h₁ hk₁).trans (homAt_eq_of_le hs' ht h₂ hk₂)⟩

instance setoid (X Y : PairCategory F) : Setoid (Rep X Y) :=
  ⟨Rel, rel_equivalence⟩

lemma rel_iff (r s : Rep X Y) :
    r ≈ s ↔ ∃ (k : ι) (hr : r.stage ≤ k) (hs : s.stage ≤ k), r.homAt k hr = s.homAt k hs :=
  Iff.rfl

omit [IsDirected ι (· ≤ ·)] in
lemma toStage_rel (r : Rep X Y) (k : ι) (h : r.stage ≤ k) : Rel (r.toStage k h) r :=
  ⟨k, le_rfl, h, homAt_self (r.toStage k h) le_rfl⟩

/-- The composite of two representatives, computed at a common stage `k`. -/
def compAt (r : Rep X Y) (s : Rep Y Z) (k : ι) (hr : r.stage ≤ k) (hs : s.stage ≤ k) :
    Rep X Z :=
  ⟨k, r.le₁.trans hr, s.le₂.trans hs, r.homAt k hr ≫ s.homAt k hs⟩

omit [IsDirected ι (· ≤ ·)] in
lemma compAt_homAt (r : Rep X Y) (s : Rep Y Z) {k k' : ι} (hr : r.stage ≤ k)
    (hs : s.stage ≤ k) (h : k ≤ k') :
    (compAt r s k hr hs).homAt k' h = r.homAt k' (hr.trans h) ≫ s.homAt k' (hs.trans h) := by
  change trHom h _ _ _ _ (r.homAt k hr ≫ s.homAt k hs) = _
  rw [trHom_comp h _ (r.le₂.trans hr) _ _ (r.le₂.trans (hr.trans h)), trHom_homAt, trHom_homAt]

lemma compAt_rel (r : Rep X Y) (s : Rep Y Z) {k k' : ι} (hr : r.stage ≤ k)
    (hs : s.stage ≤ k) (hr' : r.stage ≤ k') (hs' : s.stage ≤ k') :
    compAt r s k hr hs ≈ compAt r s k' hr' hs' := by
  obtain ⟨k'', h, h'⟩ := directed_of (· ≤ ·) k k'
  exact ⟨k'', h, h', by rw [compAt_homAt, compAt_homAt]⟩

lemma compAt_rel_compAt {r r' : Rep X Y} {s s' : Rep Y Z} (hr : r ≈ r') (hs : s ≈ s')
    {k k' : ι} (h₁ : r.stage ≤ k) (h₂ : s.stage ≤ k) (h₁' : r'.stage ≤ k')
    (h₂' : s'.stage ≤ k') : compAt r s k h₁ h₂ ≈ compAt r' s' k' h₁' h₂' := by
  obtain ⟨k₁, a₁, b₁, e₁⟩ := hr
  obtain ⟨k₂, a₂, b₂, e₂⟩ := hs
  obtain ⟨m, hm₁, hm₂⟩ := directed_of (· ≤ ·) k₁ k₂
  obtain ⟨n, hn₁, hn₂⟩ := directed_of (· ≤ ·) m k
  obtain ⟨p, hp₁, hp₂⟩ := directed_of (· ≤ ·) n k'
  refine ⟨p, hn₂.trans hp₁, hp₂, ?_⟩
  rw [compAt_homAt, compAt_homAt, homAt_eq_of_le a₁ b₁ e₁ (hm₁.trans (hn₁.trans hp₁)),
    homAt_eq_of_le a₂ b₂ e₂ (hm₂.trans (hn₁.trans hp₁))]

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
  Quotient.sound (Rep.toStage_rel r k h)

lemma homMk'_eq_homMk'_iff {X Y : PairCategory F} (r s : Rep X Y) :
    homMk' r = homMk' s ↔ ∃ (k : ι) (hr : r.stage ≤ k) (hs : s.stage ≤ k),
      r.homAt k hr = s.homAt k hs :=
  Quotient.eq (r := Rep.setoid X Y)

lemma homMk'_mk_trHom {X Y : PairCategory F} {k k' : ι} (h : k ≤ k') (hX : X.idx ≤ k)
    (hY : Y.idx ≤ k) (hX' : X.idx ≤ k') (hY' : Y.idx ≤ k') (u : X.at_ hX ⟶ Y.at_ hY) :
    homMk' (⟨k', hX', hY', trHom h hX hY hX' hY' u⟩ : Rep X Y) = homMk' ⟨k, hX, hY, u⟩ :=
  homMk'_toStage ⟨k, hX, hY, u⟩ k' h

lemma homMk'_mk_comp {X Y Z : PairCategory F} {k : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
    (hZ : Z.idx ≤ k) (u : X.at_ hX ⟶ Y.at_ hY) (v : Y.at_ hY ⟶ Z.at_ hZ) :
    Hom.comp (homMk' ⟨k, hX, hY, u⟩) (homMk' ⟨k, hY, hZ, v⟩) = homMk' ⟨k, hX, hZ, u ≫ v⟩ := by
  rw [homMk'_comp_homMk' _ _ k le_rfl le_rfl]
  exact congrArg homMk' (Rep.mk_hom_congr
    (congrArg₂ (· ≫ ·) (trHom_refl le_rfl hX hY u) (trHom_refl le_rfl hY hZ v)))

lemma Hom.id_eq (X : PairCategory F) (k : ι) (h : X.idx ≤ k) :
    Hom.id X = homMk' ⟨k, h, h, 𝟙 _⟩ := by
  rw [Hom.id, ← homMk'_mk_trHom h le_rfl le_rfl h h (𝟙 _), trHom_id]

lemma Hom.exists_mk {X Y : PairCategory F} (f : Hom X Y) (k₀ : ι) :
    ∃ (k : ι) (_ : k₀ ≤ k) (hX : X.idx ≤ k) (hY : Y.idx ≤ k) (u : X.at_ hX ⟶ Y.at_ hY),
      f = homMk' ⟨k, hX, hY, u⟩ := by
  obtain ⟨⟨s, hX, hY, u⟩, rfl⟩ := Quotient.exists_rep f
  obtain ⟨k, h₁, h₂⟩ := directed_of (· ≤ ·) k₀ s
  exact ⟨k, h₁, hX.trans h₂, hY.trans h₂, _, (homMk'_mk_trHom h₂ hX hY _ _ u).symm⟩

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the pair category is a category, with
identities, composition computed after transport to a common stage. -/
noncomputable instance category : Category.{max w v} (PairCategory F) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp {X Y} f := by
    obtain ⟨k, -, hX, hY, u, rfl⟩ := Hom.exists_mk f X.idx
    change Hom.comp (Hom.id X) _ = _
    rw [Hom.id_eq X k hX, homMk'_mk_comp, id_comp]
  comp_id {X Y} f := by
    obtain ⟨k, -, hX, hY, u, rfl⟩ := Hom.exists_mk f X.idx
    change Hom.comp _ (Hom.id Y) = _
    rw [Hom.id_eq Y k hY, homMk'_mk_comp, comp_id]
  assoc {W X Y Z} f g h := by
    obtain ⟨k₁, -, hW, hX, u, rfl⟩ := Hom.exists_mk f W.idx
    obtain ⟨k₂, h₁₂, hX₂, hY₂, v, rfl⟩ := Hom.exists_mk g k₁
    obtain ⟨k, h₂, hY, hZ, w, rfl⟩ := Hom.exists_mk h k₂
    change Hom.comp (Hom.comp _ _) _ = Hom.comp _ (Hom.comp _ _)
    rw [← homMk'_mk_trHom (h₁₂.trans h₂) hW hX (hW.trans (h₁₂.trans h₂)) (hX.trans
        (h₁₂.trans h₂)) u, ← homMk'_mk_trHom h₂ hX₂ hY₂ (hX₂.trans h₂) hY v,
      homMk'_mk_comp, homMk'_mk_comp, homMk'_mk_comp, homMk'_mk_comp, assoc]

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
  homMk'_mk_trHom h hX hY hX' hY' u

/-- A morphism is represented at a stage above any given stage. -/
lemma exists_homMk_ge {X Y : PairCategory F} (f : X ⟶ Y) (k₀ : ι) :
    ∃ (k : ι) (_ : k₀ ≤ k) (hX : X.idx ≤ k) (hY : Y.idx ≤ k) (u : X.at_ hX ⟶ Y.at_ hY),
      f = homMk hX hY u :=
  Hom.exists_mk f k₀

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: every morphism is represented at every
large enough stage. -/
lemma exists_eq_homMk {X Y : PairCategory F} (f : X ⟶ Y) :
    ∃ k₀, ∀ (k : ι) (_ : k₀ ≤ k), ∃ (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
      (u : X.at_ hX ⟶ Y.at_ hY), f = homMk hX hY u := by
  obtain ⟨k₀, hX, hY, u, rfl⟩ := exists_rep f
  exact ⟨k₀, fun k h ↦ ⟨hX.trans h, hY.trans h, _, (homMk_trHom h hX hY _ _ u).symm⟩⟩

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: two representatives define the same morphism
iff they agree after transport to some common stage. -/
lemma homMk_eq_homMk_iff' {X Y : PairCategory F} {k k' : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
    (hX' : X.idx ≤ k') (hY' : Y.idx ≤ k') (u : X.at_ hX ⟶ Y.at_ hY)
    (v : X.at_ hX' ⟶ Y.at_ hY') :
    homMk hX hY u = homMk hX' hY' v ↔ ∃ (m : ι) (h : k ≤ m) (h' : k' ≤ m),
      trHom h hX hY (hX.trans h) (hY.trans h) u =
        trHom h' hX' hY' (hX.trans h) (hY.trans h) v :=
  homMk'_eq_homMk'_iff _ _

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: two representatives at a common stage define
the same morphism iff they agree after transport to some further stage. -/
lemma homMk_eq_homMk_iff {X Y : PairCategory F} {k : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
    (u v : X.at_ hX ⟶ Y.at_ hY) :
    homMk hX hY u = homMk hX hY v ↔ ∃ (k' : ι) (h : k ≤ k'),
      trHom h hX hY (hX.trans h) (hY.trans h) u = trHom h hX hY (hX.trans h) (hY.trans h) v :=
  (homMk_eq_homMk_iff' hX hY hX hY u v).trans
    ⟨fun ⟨m, h, _, e⟩ ↦ ⟨m, h, e⟩, fun ⟨m, h, e⟩ ↦ ⟨m, h, h, e⟩⟩

@[reassoc]
lemma homMk_comp_homMk {X Y Z : PairCategory F} {k : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
    (hZ : Z.idx ≤ k) (u : X.at_ hX ⟶ Y.at_ hY) (v : Y.at_ hY ⟶ Z.at_ hZ) :
    homMk hX hY u ≫ homMk hY hZ v = homMk hX hZ (u ≫ v) :=
  homMk'_mk_comp hX hY hZ u v

@[simp]
lemma homMk_id {X : PairCategory F} {k : ι} (hX : X.idx ≤ k) : homMk hX hX (𝟙 _) = 𝟙 X :=
  (Hom.id_eq X k hX).symm

lemma id_eq_homMk (X : PairCategory F) : 𝟙 X = homMk (le_refl X.idx) le_rfl (𝟙 _) := rfl

/-- Any two parallel morphisms are represented at a common stage. -/
lemma exists_homMk₂ {X Y : PairCategory F} (f g : X ⟶ Y) :
    ∃ (k : ι) (hX : X.idx ≤ k) (hY : Y.idx ≤ k) (u v : X.at_ hX ⟶ Y.at_ hY), f = homMk hX hY u ∧ g = homMk hX hY v := by
  obtain ⟨k₁, -, hX, hY, u, rfl⟩ := exists_homMk_ge f X.idx
  obtain ⟨k, h, hX', hY', v, rfl⟩ := exists_homMk_ge g k₁
  exact ⟨k, hX', hY', _, v, (homMk_trHom h hX hY hX' hY' u).symm, rfl⟩

/-- Any three morphisms `f, g : X ⟶ Y`, `h : Y ⟶ Z` are represented at a common stage. -/
lemma exists_homMk₃ {X Y Z : PairCategory F} (f g : X ⟶ Y) (h : Y ⟶ Z) :
    ∃ (k : ι) (hX : X.idx ≤ k) (hY : Y.idx ≤ k) (hZ : Z.idx ≤ k) (u v : X.at_ hX ⟶ Y.at_ hY) (w : Y.at_ hY ⟶ Z.at_ hZ),
      f = homMk hX hY u ∧ g = homMk hX hY v ∧ h = homMk hY hZ w := by
  obtain ⟨k₁, hX, hY, u, v, rfl, rfl⟩ := exists_homMk₂ f g
  obtain ⟨k, hk, hY', hZ, w, rfl⟩ := exists_homMk_ge h k₁
  exact ⟨k, hX.trans hk, hY', hZ, _, _, w, (homMk_trHom hk hX hY _ hY' u).symm,
    (homMk_trHom hk hX hY _ hY' v).symm, rfl⟩

/-- Any three morphisms `f : X ⟶ Y`, `g h : Y ⟶ Z` are represented at a common stage. -/
lemma exists_homMk₃' {X Y Z : PairCategory F} (f : X ⟶ Y) (g h : Y ⟶ Z) :
    ∃ (k : ι) (hX : X.idx ≤ k) (hY : Y.idx ≤ k) (hZ : Z.idx ≤ k) (u : X.at_ hX ⟶ Y.at_ hY) (v w : Y.at_ hY ⟶ Z.at_ hZ),
      f = homMk hX hY u ∧ g = homMk hY hZ v ∧ h = homMk hY hZ w := by
  obtain ⟨k₁, hY, hZ, v, w, rfl, rfl⟩ := exists_homMk₂ g h
  obtain ⟨k, hk, hX, hY', u, rfl⟩ := exists_homMk_ge f k₁
  exact ⟨k, hX, hY', hZ.trans hk, u, _, _, rfl, (homMk_trHom hk hY hZ hY' _ v).symm,
    (homMk_trHom hk hY hZ hY' _ w).symm⟩

variable (F) in
/-- The inclusion `j_i : F i ⥤ PairCategory F` of a stage, `A ↦ (i, A)`. -/
noncomputable def incl (i : ι) : F.obj ⟨i⟩ ⥤ PairCategory F where
  obj A := ⟨i, A⟩
  map {A B} u := homMk (X := ⟨i, A⟩) (Y := ⟨i, B⟩) le_rfl le_rfl
    ((F.transitionId i le_rfl).hom.app A ≫ u ≫ (F.transitionId i le_rfl).inv.app B)
  map_id A := by
    convert homMk_id (X := (⟨i, A⟩ : PairCategory F)) le_rfl using 2
    simp
  map_comp u v := by simp [homMk_comp_homMk]

@[simp]
lemma incl_obj_idx (i : ι) (A : F.obj ⟨i⟩) : ((incl F i).obj A).idx = i := rfl

@[simp]
lemma incl_obj_obj (i : ι) (A : F.obj ⟨i⟩) : ((incl F i).obj A).obj = A := rfl

/-- An object `(i, A)` is isomorphic to its image `(k, T_{k/i} A)` at any further stage. -/
noncomputable def isoToStage (X : PairCategory F) {k : ι} (h : X.idx ≤ k) :
    X ≅ ⟨k, X.at_ h⟩ where
  hom := homMk (Y := ⟨k, X.at_ h⟩) h le_rfl ((F.transitionId k le_rfl).inv.app _)
  inv := homMk (X := ⟨k, X.at_ h⟩) le_rfl h ((F.transitionId k le_rfl).hom.app _)
  hom_inv_id := by
    rw [homMk_comp_homMk]
    convert homMk_id h using 2
    simp
  inv_hom_id := by
    rw [homMk_comp_homMk]
    convert homMk_id (X := (⟨k, X.at_ h⟩ : PairCategory F)) le_rfl using 2
    simp

/-- Every morphism is conjugate to the image of a morphism of a stage: the morphism represented
by `(k, u)` is `(isoToStage X) ≫ j_k(u) ≫ (isoToStage Y)⁻¹`. -/
lemma homMk_eq {X Y : PairCategory F} {k : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
    (u : X.at_ hX ⟶ Y.at_ hY) :
    homMk hX hY u = (isoToStage X hX).hom ≫ (incl F k).map u ≫ (isoToStage Y hY).inv := by
  simp [isoToStage, incl, homMk_comp_homMk]

end PairCategory

end CategoryTheory
