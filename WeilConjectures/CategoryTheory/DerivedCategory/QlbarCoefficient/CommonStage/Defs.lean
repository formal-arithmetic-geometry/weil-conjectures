/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.Order.Directed
public import Mathlib.Tactic.CategoryTheory.Slice

/-!
# The common-stage category of a filtered system of categories

This file contains the purely category-theoretic core of the construction of the
`ℚ̄_ℓ`-coefficient derived category. It is deliberately kept free of any `ℓ`-adic
arithmetic: the only input is a preorder `I`, a family of categories `C i` and a coherent
family of *transition functors* `T h : C i ⥤ C j` for `h : i ≤ j`.

## Main definitions

- `CategoryTheory.TransitionSystem`: the data of a family of categories indexed by a
  preorder `I`, together with transition functors `T h : C i ⥤ C j` for `h : i ≤ j`, and
  unit and associativity comparison isomorphisms. This is exactly a pseudofunctor from `I`,
  viewed as a locally discrete bicategory, to `Cat`, spelled out in elementary terms.
- `CategoryTheory.TransitionSystem.CommonStage`: the type of pairs `(i, X)` with `X : C i`.
- `CategoryTheory.TransitionSystem.CommonStage.transport`: the transport of a morphism
  defined at a stage `k` to a larger stage `l`, using the associativity comparisons.
- `CategoryTheory.TransitionSystem.CommonStage.Hom.Rep`: a representative of a morphism,
  i.e. a stage `k` above both stages of definition together with a morphism
  `T k/i X ⟶ T k/j Y` in `C k`.
- `CategoryTheory.TransitionSystem.CommonStage.category`: the category structure on
  `CommonStage S`, whose `Hom` types are the quotients of the types of representatives by
  the relation "become equal after transport to a common larger stage". Over a directed
  preorder this is the filtered colimit `colim_k Hom_{C k} (T k/i X, T k/j Y)`.

## Implementation notes

Since `i ≤ j` is a `Prop`, any two proofs of it are definitionally equal, so `T` really
only depends on the pair `(i, j)`. This is used throughout: for instance the source of
`transport hkl u` is stated as `X.extend (hX.trans hkl)`, which is definitionally the same
type as `X.extend hXl` for any other proof `hXl : X.stage ≤ l`.

Morphism representatives are never compared as structures, only their underlying morphism
components are, so no heterogeneous equalities appear.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category

variable {I : Type w} [Preorder I]

/-- A `TransitionSystem` on a family of categories `C i` indexed by a preorder `I` is the
data of transition functors `T h : C i ⥤ C j` for every `h : i ≤ j`, together with
comparison isomorphisms `T (le_refl i) ≅ 𝟭 (C i)` and `T h₁ ⋙ T h₂ ≅ T (h₁.trans h₂)`
satisfying the usual unit and associativity coherences.

This is the elementary spelling of a pseudofunctor from `I`, viewed as a locally discrete
bicategory, to `Cat`. In the intended application `I` is the poset of finite subextensions
`E` of `ℚ̄_ℓ / ℚ_ℓ`, `C E` is `Dᵇ_c(Y, E)` and `T` is scalar extension `- ⊗_E F`. -/
structure TransitionSystem (C : I → Type u) [∀ i, Category.{v} (C i)] where
  /-- The transition functor attached to `h : i ≤ j`. -/
  T : ∀ {i j : I}, i ≤ j → C i ⥤ C j
  /-- The transition functor along `le_refl i` is isomorphic to the identity. It is
  deliberately *not* required to be equal to it. -/
  unitIso (i : I) : T (le_refl i) ≅ 𝟭 (C i)
  /-- The associativity comparison. -/
  assoc {i j k : I} (h₁ : i ≤ j) (h₂ : j ≤ k) : T h₁ ⋙ T h₂ ≅ T (h₁.trans h₂)
  /-- Compatibility of `assoc` with `unitIso` on the right. -/
  assoc_unitIso_right {i j : I} (h : i ≤ j) (X : C i) :
    (assoc h (le_refl j)).hom.app X = (unitIso j).hom.app ((T h).obj X)
  /-- Compatibility of `assoc` with `unitIso` on the left. -/
  assoc_unitIso_left {i j : I} (h : i ≤ j) (X : C i) :
    (assoc (le_refl i) h).hom.app X = (T h).map ((unitIso i).hom.app X)
  /-- The associativity coherence for a chain `i ≤ j ≤ k ≤ l`. -/
  assoc_assoc {i j k l : I} (h₁ : i ≤ j) (h₂ : j ≤ k) (h₃ : k ≤ l) (X : C i) :
    (T h₃).map ((assoc h₁ h₂).hom.app X) ≫ (assoc (h₁.trans h₂) h₃).hom.app X =
      (assoc h₂ h₃).hom.app ((T h₁).obj X) ≫ (assoc h₁ (h₂.trans h₃)).hom.app X

namespace TransitionSystem

variable {C : I → Type u} [∀ i, Category.{v} (C i)]

/-- An object of the common-stage category: an object of `C i` for some stage `i`, which
records a *stage of definition* rather than extra structure. -/
structure CommonStage (S : TransitionSystem C) where
  /-- The stage over which the object is defined. -/
  stage : I
  /-- The object at that stage. -/
  obj : C stage

namespace CommonStage

variable {S : TransitionSystem C}

/-- The image of `X` under the transition functor to a larger stage `k`. -/
abbrev extend (X : CommonStage S) {k : I} (h : X.stage ≤ k) : C k := (S.T h).obj X.obj

section UpperBound

variable (I) in
/-- A chosen common upper bound of two stages in a directed preorder. -/
noncomputable def ub [IsDirectedOrder I] (i j : I) : I := (exists_ge_ge i j).choose

variable [IsDirectedOrder I]

lemma le_ub_left (i j : I) : i ≤ ub I i j := (exists_ge_ge i j).choose_spec.1

lemma le_ub_right (i j : I) : j ≤ ub I i j := (exists_ge_ge i j).choose_spec.2

end UpperBound

section Transport

variable {X Y Z : CommonStage S} {k l m : I}

/-- Transport of a morphism between the extensions of `X` and `Y` at stage `k` to a larger
stage `l`, conjugating `(S.T hkl).map u` by the associativity comparisons. -/
def transport {hX : X.stage ≤ k} {hY : Y.stage ≤ k} (hkl : k ≤ l)
    (u : X.extend hX ⟶ Y.extend hY) :
    X.extend (hX.trans hkl) ⟶ Y.extend (hY.trans hkl) :=
  (S.assoc hX hkl).inv.app X.obj ≫ (S.T hkl).map u ≫ (S.assoc hY hkl).hom.app Y.obj

/-- The associativity comparison along `le_refl` agrees with the unit comparison. -/
lemma assocIso_le_refl (h : X.stage ≤ k) :
    (S.assoc h (le_refl k)).app X.obj = (S.unitIso k).app (X.extend h) :=
  Iso.ext (S.assoc_unitIso_right h X.obj)

@[simp]
lemma transport_le_refl {hX : X.stage ≤ k} {hY : Y.stage ≤ k}
    (u : X.extend hX ⟶ Y.extend hY) : transport (le_refl k) u = u := by
  have hX' : (S.assoc hX (le_refl k)).inv.app X.obj = (S.unitIso k).inv.app (X.extend hX) :=
    congrArg Iso.inv (assocIso_le_refl hX)
  rw [transport, hX', S.assoc_unitIso_right hY Y.obj, (S.unitIso k).hom.naturality u]
  simp

lemma transport_id (X : CommonStage S) (hX : X.stage ≤ k) (hkl : k ≤ l) :
    transport (X := X) (Y := X) (hX := hX) (hY := hX) hkl (𝟙 (X.extend hX)) =
      𝟙 (X.extend (hX.trans hkl)) := by
  simp [transport]

lemma transport_comp {hX : X.stage ≤ k} {hY : Y.stage ≤ k} {hZ : Z.stage ≤ k} (hkl : k ≤ l)
    (u : X.extend hX ⟶ Y.extend hY) (v : Y.extend hY ⟶ Z.extend hZ) :
    transport hkl (u ≫ v) = transport hkl u ≫ transport hkl v := by
  simp [transport]

/-- The inverse form of the associativity coherence. -/
lemma assoc_assoc_inv (hX : X.stage ≤ k) (hkl : k ≤ l) (hlm : l ≤ m) :
    (S.assoc (hX.trans hkl) hlm).inv.app X.obj ≫
        (S.T hlm).map ((S.assoc hX hkl).inv.app X.obj) =
      (S.assoc hX (hkl.trans hlm)).inv.app X.obj ≫
        (S.assoc hkl hlm).inv.app (X.extend hX) := by
  have h : (S.T hlm).mapIso ((S.assoc hX hkl).app X.obj) ≪≫
        (S.assoc (hX.trans hkl) hlm).app X.obj =
      (S.assoc hkl hlm).app (X.extend hX) ≪≫ (S.assoc hX (hkl.trans hlm)).app X.obj :=
    Iso.ext (S.assoc_assoc hX hkl hlm X.obj)
  simpa using congrArg Iso.inv h

lemma transport_transport {hX : X.stage ≤ k} {hY : Y.stage ≤ k} (hkl : k ≤ l) (hlm : l ≤ m)
    (u : X.extend hX ⟶ Y.extend hY) :
    transport hlm (transport hkl u) = transport (hkl.trans hlm) u := by
  have nat : ∀ (a b : C k) (f : a ⟶ b),
      (S.T hlm).map ((S.T hkl).map f) ≫ (S.assoc hkl hlm).hom.app b =
        (S.assoc hkl hlm).hom.app a ≫ (S.T (hkl.trans hlm)).map f :=
    fun _ _ f ↦ (S.assoc hkl hlm).hom.naturality f
  simp only [transport, Functor.map_comp]
  slice_lhs 1 2 => rw [assoc_assoc_inv hX hkl hlm]
  slice_lhs 4 5 => rw [S.assoc_assoc hY hkl hlm Y.obj]
  slice_lhs 3 4 => rw [nat]
  simp

end Transport

section Hom

variable (X Y : CommonStage S)

/-- A representative of a morphism `X ⟶ Y` in the common-stage category: a stage `k` above
the stages of definition of `X` and `Y`, and a morphism between their extensions to `k`. -/
structure Hom.Rep where
  /-- The stage at which the morphism is represented. -/
  stage : I
  /-- The source is defined at a smaller stage. -/
  leLeft : X.stage ≤ stage
  /-- The target is defined at a smaller stage. -/
  leRight : Y.stage ≤ stage
  /-- The underlying morphism at that stage. -/
  hom : X.extend leLeft ⟶ Y.extend leRight

namespace Hom

variable {X Y}

/-- Transport a representative to a larger stage. -/
def Rep.transport (u : Rep X Y) {k : I} (h : u.stage ≤ k) : Rep X Y where
  stage := k
  leLeft := u.leLeft.trans h
  leRight := u.leRight.trans h
  hom := CommonStage.transport h u.hom

@[simp]
lemma Rep.transport_hom (u : Rep X Y) {k : I} (h : u.stage ≤ k) :
    (u.transport h).hom = CommonStage.transport h u.hom := rfl

@[simp]
lemma Rep.transport_stage (u : Rep X Y) {k : I} (h : u.stage ≤ k) :
    (u.transport h).stage = k := rfl

/-- Two representatives are equivalent when they become equal after transport to a common
larger stage. -/
def Rel (u v : Rep X Y) : Prop :=
  ∃ (k : I) (hu : u.stage ≤ k) (hv : v.stage ≤ k),
    CommonStage.transport hu u.hom = CommonStage.transport hv v.hom

lemma Rel.refl (u : Rep X Y) : Rel u u := ⟨u.stage, le_refl _, le_refl _, rfl⟩

lemma Rel.symm {u v : Rep X Y} (h : Rel u v) : Rel v u :=
  let ⟨k, hu, hv, e⟩ := h; ⟨k, hv, hu, e.symm⟩

variable [IsDirectedOrder I]

/-- Two equivalent representatives agree after transport to a sufficiently large stage
above any prescribed common stage. -/
lemma Rel.exists_ge {u v : Rep X Y} (h : Rel u v) {k : I} (hu : u.stage ≤ k)
    (hv : v.stage ≤ k) :
    ∃ (l : I) (hkl : k ≤ l), CommonStage.transport (hu.trans hkl) u.hom =
      CommonStage.transport (hv.trans hkl) v.hom := by
  obtain ⟨p, hup, hvp, e⟩ := h
  obtain ⟨l, hkl, hpl⟩ := exists_ge_ge k p
  refine ⟨l, hkl, ?_⟩
  rw [← CommonStage.transport_transport hup hpl, e, CommonStage.transport_transport]

lemma Rel.trans {u v w : Rep X Y} (h₁ : Rel u v) (h₂ : Rel v w) : Rel u w := by
  obtain ⟨k₁, hu₁, hv₁, e₁⟩ := h₁
  obtain ⟨k₂, hv₂, hw₂, e₂⟩ := h₂
  obtain ⟨k, hk₁, hk₂⟩ := exists_ge_ge k₁ k₂
  refine ⟨k, hu₁.trans hk₁, hw₂.trans hk₂, ?_⟩
  rw [← CommonStage.transport_transport hu₁ hk₁, e₁, CommonStage.transport_transport,
    ← CommonStage.transport_transport hw₂ hk₂, ← e₂, CommonStage.transport_transport]

instance setoid : Setoid (Rep X Y) where
  r := Rel
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

end Hom

/-- The morphisms of the common-stage category: representatives modulo the relation of
becoming equal at a larger stage. Equivalently, the filtered colimit
`colim_k Hom_{C k} (T k/i X, T k/j Y)`. -/
def Hom [IsDirectedOrder I] : Type max w v := Quotient (Hom.setoid (X := X) (Y := Y))

end Hom

namespace Hom

variable [IsDirectedOrder I] {X Y Z W : CommonStage S}

/-- The morphism represented by `u`. -/
def mk (u : Rep X Y) : Hom X Y := Quotient.mk _ u

lemma mk_surjective (f : Hom X Y) : ∃ u : Rep X Y, mk u = f := Quotient.exists_rep f

lemma mk_eq_mk_iff (u v : Rep X Y) : mk u = mk v ↔ Rel u v := Quotient.eq_iff_equiv

/-- Transporting a representative does not change the morphism it represents. -/
lemma mk_transport (u : Rep X Y) {k : I} (h : u.stage ≤ k) : mk (u.transport h) = mk u :=
  (mk_eq_mk_iff _ _).2 ⟨k, le_refl _, h, by rw [Rep.transport_hom,
    CommonStage.transport_le_refl]⟩

/-- The identity morphism, represented at the stage of definition of `X`. -/
def id (X : CommonStage S) : Hom X X :=
  mk ⟨X.stage, le_refl _, le_refl _, 𝟙 (X.extend (le_refl _))⟩

/-- Composition of two representatives at a chosen common stage. -/
def Rep.compAt (u : Rep X Y) (v : Rep Y Z) {k : I} (hu : u.stage ≤ k) (hv : v.stage ≤ k) :
    Rep X Z where
  stage := k
  leLeft := u.leLeft.trans hu
  leRight := v.leRight.trans hv
  hom := CommonStage.transport hu u.hom ≫ CommonStage.transport hv v.hom

omit [IsDirectedOrder I] in
@[simp]
lemma Rep.compAt_hom (u : Rep X Y) (v : Rep Y Z) {k : I} (hu : u.stage ≤ k)
    (hv : v.stage ≤ k) :
    (u.compAt v hu hv).hom = CommonStage.transport hu u.hom ≫ CommonStage.transport hv v.hom :=
  rfl

omit [IsDirectedOrder I] in
@[simp]
lemma Rep.compAt_stage (u : Rep X Y) (v : Rep Y Z) {k : I} (hu : u.stage ≤ k)
    (hv : v.stage ≤ k) : (u.compAt v hu hv).stage = k := rfl

/-- The class of `Rep.compAt` does not depend on the chosen common stage. -/
lemma mk_compAt_eq (u : Rep X Y) (v : Rep Y Z) {k k' : I} (hu : u.stage ≤ k)
    (hv : v.stage ≤ k) (hu' : u.stage ≤ k') (hv' : v.stage ≤ k') :
    mk (u.compAt v hu hv) = mk (u.compAt v hu' hv') := by
  obtain ⟨l, hl, hl'⟩ := exists_ge_ge k k'
  refine (mk_eq_mk_iff _ _).2 ⟨l, hl, hl', ?_⟩
  simp only [Rep.compAt_hom, CommonStage.transport_comp, CommonStage.transport_transport]

lemma mk_compAt_congr {u u' : Rep X Y} {v v' : Rep Y Z} (hu : Rel u u') (hv : Rel v v')
    {k : I} (h₁ : u.stage ≤ k) (h₂ : v.stage ≤ k) (h₁' : u'.stage ≤ k) (h₂' : v'.stage ≤ k) :
    mk (u.compAt v h₁ h₂) = mk (u'.compAt v' h₁' h₂') := by
  obtain ⟨l₁, hl₁, e₁⟩ := hu.exists_ge h₁ h₁'
  obtain ⟨l₂, hl₂, e₂⟩ := hv.exists_ge h₂ h₂'
  obtain ⟨l, hl, hl'⟩ := exists_ge_ge l₁ l₂
  refine (mk_eq_mk_iff _ _).2 ⟨l, hl₁.trans hl, hl₂.trans hl', ?_⟩
  simp only [Rep.compAt_hom, CommonStage.transport_comp, CommonStage.transport_transport]
  have E₁ : CommonStage.transport (h₁.trans (hl₁.trans hl)) u.hom =
      CommonStage.transport (h₁'.trans (hl₁.trans hl)) u'.hom := by
    rw [← CommonStage.transport_transport (h₁.trans hl₁) hl, e₁,
      CommonStage.transport_transport]
  have E₂ : CommonStage.transport (h₂.trans (hl₂.trans hl')) v.hom =
      CommonStage.transport (h₂'.trans (hl₂.trans hl')) v'.hom := by
    rw [← CommonStage.transport_transport (h₂.trans hl₂) hl', e₂,
      CommonStage.transport_transport]
  rw [E₁, E₂]

/-- Composition in the common-stage category. -/
noncomputable def comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  Quotient.liftOn₂ f g
    (fun u v ↦ mk (u.compAt v (le_ub_left u.stage v.stage) (le_ub_right u.stage v.stage)))
    (fun u v u' v' hu hv ↦ by
      obtain ⟨k, hk, hk'⟩ := exists_ge_ge (ub I u.stage v.stage) (ub I u'.stage v'.stage)
      rw [mk_compAt_eq u v _ _ ((le_ub_left u.stage v.stage).trans hk)
          ((le_ub_right u.stage v.stage).trans hk),
        mk_compAt_eq u' v' _ _ ((le_ub_left u'.stage v'.stage).trans hk')
          ((le_ub_right u'.stage v'.stage).trans hk')]
      exact mk_compAt_congr hu hv _ _ _ _)

/-- Composition is computed by `Rep.compAt` at any common stage. -/
lemma comp_mk_mk (u : Rep X Y) (v : Rep Y Z) {k : I} (hu : u.stage ≤ k) (hv : v.stage ≤ k) :
    comp (mk u) (mk v) = mk (u.compAt v hu hv) :=
  mk_compAt_eq u v _ _ hu hv

end Hom

variable [IsDirectedOrder I]

open Hom in
/-- The common-stage category associated to a transition system over a directed preorder.

Objects are pairs `(i, X)` with `X : C i`; morphisms are represented at a common stage
above both stages of definition, and identified when they agree after passing to a still
larger stage. -/
noncomputable instance category : Category.{max w v} (CommonStage S) where
  Hom X Y := Hom X Y
  id X := Hom.id X
  comp f g := Hom.comp f g
  id_comp {X Y} f := by
    obtain ⟨u, rfl⟩ := mk_surjective f
    rw [Hom.id, comp_mk_mk _ u u.leLeft (le_refl u.stage)]
    refine (mk_eq_mk_iff _ _).2 ⟨u.stage, le_refl _, le_refl _, ?_⟩
    simp [CommonStage.transport_id]
  comp_id {X Y} f := by
    obtain ⟨u, rfl⟩ := mk_surjective f
    rw [Hom.id, comp_mk_mk u _ (le_refl u.stage) u.leRight]
    refine (mk_eq_mk_iff _ _).2 ⟨u.stage, le_refl _, le_refl _, ?_⟩
    simp [CommonStage.transport_id]
  assoc {X Y Z W} f g h := by
    obtain ⟨u, rfl⟩ := mk_surjective f
    obtain ⟨v, rfl⟩ := mk_surjective g
    obtain ⟨w, rfl⟩ := mk_surjective h
    obtain ⟨k, hk₁, hk₂⟩ := exists_ge_ge u.stage v.stage
    obtain ⟨p, hp₁, hp₂⟩ := exists_ge_ge k w.stage
    rw [comp_mk_mk u v hk₁ hk₂, comp_mk_mk _ w hp₁ hp₂,
      comp_mk_mk v w (hk₂.trans hp₁) hp₂, comp_mk_mk u _ (hk₁.trans hp₁) (le_refl p)]
    refine (mk_eq_mk_iff _ _).2 ⟨p, le_refl _, le_refl _, ?_⟩
    simp only [Rep.compAt_hom, Rep.compAt_stage, CommonStage.transport_le_refl,
      CommonStage.transport_comp, CommonStage.transport_transport, Category.assoc]

section API

/-!
### Working with morphisms represented at a fixed stage

The lemmas in this section are the interface that should be used in the sequel; the
quotient presentation is never unfolded again. The key statements are `exists_homMk₂` and
`exists_homMk₃`, the *common-stage principle*: any finite family of parallel or composable
morphisms is represented at one single stage.
-/

variable {X Y Z : CommonStage S} {k l : I}

/-- The morphism of `CommonStage S` represented by a morphism `u` at the stage `k`. -/
def homMk (hX : X.stage ≤ k) (hY : Y.stage ≤ k) (u : X.extend hX ⟶ Y.extend hY) : X ⟶ Y :=
  Hom.mk ⟨k, hX, hY, u⟩

lemma homMk_eq_homMk_iff {k' : I} (hX : X.stage ≤ k) (hY : Y.stage ≤ k) (hX' : X.stage ≤ k')
    (hY' : Y.stage ≤ k') (u : X.extend hX ⟶ Y.extend hY) (v : X.extend hX' ⟶ Y.extend hY') :
    homMk hX hY u = homMk hX' hY' v ↔
      ∃ (p : I) (h : k ≤ p) (h' : k' ≤ p), transport h u = transport h' v := by
  rw [homMk, homMk, Hom.mk_eq_mk_iff]
  rfl

/-- Transporting the representative to a larger stage does not change the morphism. -/
@[simp]
lemma homMk_transport (hX : X.stage ≤ k) (hY : Y.stage ≤ k) (hkl : k ≤ l)
    (u : X.extend hX ⟶ Y.extend hY) :
    homMk (hX.trans hkl) (hY.trans hkl) (transport hkl u) = homMk hX hY u :=
  Hom.mk_transport ⟨k, hX, hY, u⟩ hkl

/-- Every morphism is represented at some stage. -/
lemma exists_homMk (f : X ⟶ Y) :
    ∃ (k : I) (hX : X.stage ≤ k) (hY : Y.stage ≤ k) (u : X.extend hX ⟶ Y.extend hY),
      f = homMk hX hY u := by
  obtain ⟨u, rfl⟩ := Hom.mk_surjective f
  exact ⟨u.stage, u.leLeft, u.leRight, u.hom, rfl⟩

/-- Any two parallel morphisms are represented at one common stage. -/
lemma exists_homMk₂ (f g : X ⟶ Y) :
    ∃ (k : I) (hX : X.stage ≤ k) (hY : Y.stage ≤ k) (u v : X.extend hX ⟶ Y.extend hY),
      f = homMk hX hY u ∧ g = homMk hX hY v := by
  obtain ⟨k₁, hX₁, hY₁, u, rfl⟩ := exists_homMk f
  obtain ⟨k₂, hX₂, hY₂, v, rfl⟩ := exists_homMk g
  obtain ⟨k, h₁, h₂⟩ := exists_ge_ge k₁ k₂
  exact ⟨k, hX₁.trans h₁, hY₁.trans h₁, transport h₁ u, transport h₂ v,
    (homMk_transport _ _ h₁ u).symm, (homMk_transport _ _ h₂ v).symm⟩

/-- Any three parallel morphisms are represented at one common stage. -/
lemma exists_homMk₃ (f g h : X ⟶ Y) :
    ∃ (k : I) (hX : X.stage ≤ k) (hY : Y.stage ≤ k) (u v w : X.extend hX ⟶ Y.extend hY),
      f = homMk hX hY u ∧ g = homMk hX hY v ∧ h = homMk hX hY w := by
  obtain ⟨k₁, hX₁, hY₁, u, v, rfl, rfl⟩ := exists_homMk₂ f g
  obtain ⟨k₂, hX₂, hY₂, w, rfl⟩ := exists_homMk h
  obtain ⟨k, h₁, h₂⟩ := exists_ge_ge k₁ k₂
  exact ⟨k, hX₁.trans h₁, hY₁.trans h₁, transport h₁ u, transport h₁ v, transport h₂ w,
    (homMk_transport _ _ h₁ u).symm, (homMk_transport _ _ h₁ v).symm,
    (homMk_transport _ _ h₂ w).symm⟩

/-- Any two composable morphisms are represented at one common stage. -/
lemma exists_homMk_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃ (k : I) (hX : X.stage ≤ k) (hY : Y.stage ≤ k) (hZ : Z.stage ≤ k)
      (u : X.extend hX ⟶ Y.extend hY) (v : Y.extend hY ⟶ Z.extend hZ),
      f = homMk hX hY u ∧ g = homMk hY hZ v := by
  obtain ⟨k₁, hX₁, hY₁, u, rfl⟩ := exists_homMk f
  obtain ⟨k₂, hY₂, hZ₂, v, rfl⟩ := exists_homMk g
  obtain ⟨k, h₁, h₂⟩ := exists_ge_ge k₁ k₂
  exact ⟨k, hX₁.trans h₁, hY₁.trans h₁, hZ₂.trans h₂, transport h₁ u, transport h₂ v,
    (homMk_transport _ _ h₁ u).symm, (homMk_transport _ _ h₂ v).symm⟩

@[simp]
lemma id_eq_homMk (X : CommonStage S) :
    𝟙 X = homMk (le_refl X.stage) (le_refl X.stage) (𝟙 (X.extend (le_refl X.stage))) := rfl

/-- Composition of two morphisms represented at the *same* stage is computed there. -/
@[simp]
lemma homMk_comp_homMk (hX : X.stage ≤ k) (hY : Y.stage ≤ k) (hZ : Z.stage ≤ k)
    (u : X.extend hX ⟶ Y.extend hY) (v : Y.extend hY ⟶ Z.extend hZ) :
    homMk hX hY u ≫ homMk hY hZ v = homMk hX hZ (u ≫ v) := by
  have h := Hom.comp_mk_mk (X := X) (Y := Y) (Z := Z) ⟨k, hX, hY, u⟩ ⟨k, hY, hZ, v⟩
    (le_refl k) (le_refl k)
  refine h.trans ((Hom.mk_eq_mk_iff _ _).2 ⟨k, le_refl _, le_refl _, ?_⟩)
  simp only [Hom.Rep.compAt_hom, transport_le_refl]

@[simp]
lemma homMk_id (hX : X.stage ≤ k) : homMk hX hX (𝟙 (X.extend hX)) = 𝟙 X := by
  rw [id_eq_homMk, ← homMk_transport (le_refl X.stage) (le_refl X.stage) hX, transport_id]

end API

section StageFunctor

/-!
### The functors from the finite stages

The stage `i` recorded by an object `(i, X)` is a *stage of definition*, not extra
structure: `stageIso` identifies `(i, X)` with `(j, T j/i X)` for any `j ≥ i`.
-/

variable (S) in
/-- The canonical functor from the category at the stage `i` to the common-stage
category. -/
noncomputable def stageFunctor (i : I) : C i ⥤ CommonStage S where
  obj X := ⟨i, X⟩
  map f := homMk (le_refl i) (le_refl i) ((S.T (le_refl i)).map f)
  map_id X := by
    simp only [Functor.map_id]
    exact homMk_id (X := (⟨i, X⟩ : CommonStage S)) (le_refl i)
  map_comp f g := by rw [homMk_comp_homMk, Functor.map_comp]

/-- An object of `C i` and its scalar extension to a larger stage `j` define canonically
isomorphic objects of the common-stage category. -/
@[simps]
noncomputable def stageIso {i j : I} (h : i ≤ j) (X : C i) :
    (stageFunctor S i).obj X ≅ (stageFunctor S j).obj ((S.T h).obj X) where
  hom := homMk h (le_refl j) ((S.unitIso j).inv.app ((S.T h).obj X))
  inv := homMk (le_refl j) h ((S.unitIso j).hom.app ((S.T h).obj X))
  hom_inv_id := by
    rw [homMk_comp_homMk, Iso.inv_hom_id_app]
    exact homMk_id (X := (⟨i, X⟩ : CommonStage S)) h
  inv_hom_id := by
    rw [homMk_comp_homMk, Iso.hom_inv_id_app]
    exact homMk_id (X := (⟨j, (S.T h).obj X⟩ : CommonStage S)) (le_refl j)

end StageFunctor

section Lift

/-!
### Lifting stagewise operations on morphisms

Any operation on morphisms which is defined at every stage and commutes with transport
descends to the common-stage category. This is used to define the additive and the linear
structure; the same pattern also produces functors out of `CommonStage S`.
-/

variable {X Y : CommonStage S}

/-- An operation on morphisms defined at every stage and commuting with transport. -/
structure StageUnop (X Y : CommonStage S) where
  /-- The operation at a given stage. -/
  op : ∀ {k : I} (hX : X.stage ≤ k) (hY : Y.stage ≤ k),
    (X.extend hX ⟶ Y.extend hY) → (X.extend hX ⟶ Y.extend hY)
  /-- Commutation with transport. -/
  transport_op : ∀ {k l : I} (hX : X.stage ≤ k) (hY : Y.stage ≤ k) (hkl : k ≤ l)
    (u : X.extend hX ⟶ Y.extend hY),
    transport hkl (op hX hY u) = op (hX.trans hkl) (hY.trans hkl) (transport hkl u)

/-- A binary operation on parallel morphisms defined at every stage and commuting with
transport. -/
structure StageBinop (X Y : CommonStage S) where
  /-- The operation at a given stage. -/
  op : ∀ {k : I} (hX : X.stage ≤ k) (hY : Y.stage ≤ k),
    (X.extend hX ⟶ Y.extend hY) → (X.extend hX ⟶ Y.extend hY) → (X.extend hX ⟶ Y.extend hY)
  /-- Commutation with transport. -/
  transport_op : ∀ {k l : I} (hX : X.stage ≤ k) (hY : Y.stage ≤ k) (hkl : k ≤ l)
    (u v : X.extend hX ⟶ Y.extend hY),
    transport hkl (op hX hY u v) =
      op (hX.trans hkl) (hY.trans hkl) (transport hkl u) (transport hkl v)

/-- The morphism obtained by applying a stagewise unary operation. -/
noncomputable def StageUnop.lift (F : StageUnop X Y) (f : X ⟶ Y) : X ⟶ Y :=
  Quotient.liftOn (f : Hom X Y) (fun u ↦ homMk u.leLeft u.leRight (F.op _ _ u.hom))
    (fun u u' h ↦ by
      obtain ⟨p, hu, hu', e⟩ := h
      rw [← homMk_transport u.leLeft u.leRight hu, ← homMk_transport u'.leLeft u'.leRight hu',
        F.transport_op, F.transport_op, e])

@[simp]
lemma StageUnop.lift_homMk (F : StageUnop X Y) {k : I} (hX : X.stage ≤ k) (hY : Y.stage ≤ k)
    (u : X.extend hX ⟶ Y.extend hY) : F.lift (homMk hX hY u) = homMk hX hY (F.op hX hY u) :=
  rfl

/-- The morphism obtained by applying a stagewise binary operation. -/
noncomputable def StageBinop.lift (F : StageBinop X Y) (f g : X ⟶ Y) : X ⟶ Y :=
  Quotient.liftOn₂ (f : Hom X Y) (g : Hom X Y)
    (fun u v ↦ homMk (u.leLeft.trans (le_ub_left u.stage v.stage))
      (u.leRight.trans (le_ub_left u.stage v.stage))
      (F.op _ _ (transport (le_ub_left u.stage v.stage) u.hom)
        (transport (le_ub_right u.stage v.stage) v.hom)))
    (fun u v u' v' hu hv ↦ by
      obtain ⟨p₀, hp₀, hp₀'⟩ :=
        exists_ge_ge (ub I u.stage v.stage) (ub I u'.stage v'.stage)
      obtain ⟨p₁, hp₁, eu⟩ := hu.exists_ge ((le_ub_left u.stage v.stage).trans hp₀)
        ((le_ub_left u'.stage v'.stage).trans hp₀')
      obtain ⟨p, hp, ev⟩ := hv.exists_ge (((le_ub_right u.stage v.stage).trans hp₀).trans hp₁)
        (((le_ub_right u'.stage v'.stage).trans hp₀').trans hp₁)
      have eu' : transport ((((le_ub_left u.stage v.stage).trans hp₀).trans hp₁).trans hp) u.hom
          = transport ((((le_ub_left u'.stage v'.stage).trans hp₀').trans hp₁).trans hp)
            u'.hom := by
        rw [← transport_transport (((le_ub_left u.stage v.stage).trans hp₀).trans hp₁) hp,
          eu, transport_transport]
      rw [← homMk_transport _ _ (hp₀.trans (hp₁.trans hp)),
        ← homMk_transport _ _ (hp₀'.trans (hp₁.trans hp)),
        F.transport_op, F.transport_op]
      simp only [transport_transport]
      rw [eu', ev])

@[simp]
lemma StageBinop.lift_homMk (F : StageBinop X Y) {k : I} (hX : X.stage ≤ k) (hY : Y.stage ≤ k)
    (u v : X.extend hX ⟶ Y.extend hY) :
    F.lift (homMk hX hY u) (homMk hX hY v) = homMk hX hY (F.op hX hY u v) := by
  have h : F.lift (homMk hX hY u) (homMk hX hY v) =
      homMk (hX.trans (le_ub_left k k)) (hY.trans (le_ub_left k k))
        (F.op _ _ (transport (le_ub_left k k) u) (transport (le_ub_right k k) v)) := rfl
  rw [h, ← F.transport_op, homMk_transport]

end Lift

end CommonStage

end TransitionSystem

end CategoryTheory
