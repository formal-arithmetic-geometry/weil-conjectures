/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Order.Directed

/-!
# The common-stage category of a directed system of categories

Let `S` be a directed preorder and `E ↦ C E` a system of categories with transition functors
`T h : C E ⥤ C L` for `h : E ≤ L`, and composition isomorphisms `T h ⋙ T h' ≅ T (h.trans h')`
satisfying the cocycle condition (`CategoryTheory.TwoColimitData`). Given an object property
`P E` on each `C E`, the *common-stage category* has objects the pairs `(E, K)` with `K ∈ P E`,
and morphisms `(E, K) ⟶ (E', K')` the filtered colimit

`colim_{L ⊇ E, E'} Hom_{C L}(T K, T K')`

(`CategoryTheory.TwoColimitData.Hom`): composition and identities are represented over a common
stage. This is the construction of blueprint `def-weil-algebraically-closed-coefficients`.

A compatible system of functors `F E : C E ⥤ D E` (`CategoryTheory.TwoColimitData.Morphism`)
induces a functor between the common-stage categories
(`CategoryTheory.TwoColimitData.Morphism.functor`), which is fully faithful as soon as every `F E`
is (`CategoryTheory.TwoColimitData.Morphism.full_functor`,
`CategoryTheory.TwoColimitData.Morphism.faithful_functor`): a filtered colimit of bijections is a
bijection.
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace CategoryTheory

set_option linter.checkUnivs false in
/-- A directed system of categories over a preorder `S`, with transition functors and composition
isomorphisms satisfying the cocycle condition. -/
structure TwoColimitData (S : Type w) [Preorder S] where
  /-- The categories. -/
  C : S → Type u
  [cat : ∀ E, Category.{v} (C E)]
  /-- The transition functors. -/
  T : ∀ {E L : S}, E ≤ L → C E ⥤ C L
  /-- The composition isomorphisms. -/
  comp : ∀ {E L L' : S} (h : E ≤ L) (h' : L ≤ L'), T h ⋙ T h' ≅ T (h.trans h')
  cocycle : ∀ {E L L' L'' : S} (h : E ≤ L) (h' : L ≤ L') (h'' : L' ≤ L''),
    Functor.whiskerRight (comp h h').hom (T h'') ≫ (comp (h.trans h') h'').hom =
      Functor.whiskerLeft (T h) (comp h' h'').hom ≫ (comp h (h'.trans h'')).hom

attribute [instance] TwoColimitData.cat

namespace TwoColimitData

variable {S : Type w} [Preorder S] (D : TwoColimitData.{w, v, u} S)

/-- The transport of a morphism between images of objects of `C E` and `C E'` at the stage `L`
to a later stage `M`. -/
def transport {E E' L M : S} {hE : E ≤ L} {hE' : E' ≤ L} {K : D.C E} {K' : D.C E'}
    (f : (D.T hE).obj K ⟶ (D.T hE').obj K') (hLM : L ≤ M) :
    (D.T (hE.trans hLM)).obj K ⟶ (D.T (hE'.trans hLM)).obj K' :=
  (D.comp hE hLM).inv.app K ≫ (D.T hLM).map f ≫ (D.comp hE' hLM).hom.app K'

lemma transport_comp {E E' E'' L M : S} {hE : E ≤ L} {hE' : E' ≤ L} {hE'' : E'' ≤ L}
    {K : D.C E} {K' : D.C E'} {K'' : D.C E''} (f : (D.T hE).obj K ⟶ (D.T hE').obj K')
    (g : (D.T hE').obj K' ⟶ (D.T hE'').obj K'') (hLM : L ≤ M) :
    D.transport (f ≫ g) hLM = D.transport f hLM ≫ D.transport g hLM := by
  simp [transport]

lemma transport_id {E L M : S} {hE : E ≤ L} {K : D.C E} (hLM : L ≤ M) :
    D.transport (𝟙 ((D.T hE).obj K)) hLM = 𝟙 _ := by
  simp [transport]

lemma comp_hom_app_cocycle {E L L' L'' : S} (h : E ≤ L) (h' : L ≤ L') (h'' : L' ≤ L'')
    (K : D.C E) :
    (D.T h'').map ((D.comp h h').hom.app K) ≫ (D.comp (h.trans h') h'').hom.app K =
      (D.comp h' h'').hom.app ((D.T h).obj K) ≫ (D.comp h (h'.trans h'')).hom.app K :=
  congr_app (D.cocycle h h' h'') K

/-- Transports compose. -/
lemma transport_transport {E E' L M N : S} {hE : E ≤ L} {hE' : E' ≤ L} {K : D.C E}
    {K' : D.C E'} (f : (D.T hE).obj K ⟶ (D.T hE').obj K') (hLM : L ≤ M) (hMN : M ≤ N) :
    D.transport (D.transport f hLM) hMN = D.transport f (hLM.trans hMN) := by
  have h₁ := D.comp_hom_app_cocycle hE hLM hMN K
  have h₂ := D.comp_hom_app_cocycle hE' hLM hMN K'
  have hn := (D.comp hLM hMN).hom.naturality f
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [transport, Functor.map_comp, Category.assoc]
  rw [← cancel_epi ((D.comp (hE.trans hLM) hMN).hom.app K)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← cancel_epi ((D.T hMN).map ((D.comp hE hLM).hom.app K)), ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% h₁]
  rw [Iso.hom_inv_id_app_assoc, h₂, reassoc_of% hn]

/-- An object of the common-stage category: an object `K` of some stage `C E` with `P E K`. -/
structure Obj (P : ∀ E, ObjectProperty (D.C E)) where
  /-- The stage. -/
  E : S
  /-- The object. -/
  K : D.C E
  prop : P E K

variable {D} {P : ∀ E, ObjectProperty (D.C E)}

/-- A representative of a morphism of the common-stage category: a morphism at a common stage. -/
structure PreHom (A B : D.Obj P) where
  /-- The common stage. -/
  L : S
  hA : A.E ≤ L
  hB : B.E ≤ L
  /-- The morphism at the common stage. -/
  f : (D.T hA).obj A.K ⟶ (D.T hB).obj B.K

namespace PreHom

variable {A B C : D.Obj P}

/-- The transport of a representative to a later stage. -/
def push (x : PreHom A B) {M : S} (h : x.L ≤ M) : PreHom A B :=
  ⟨M, x.hA.trans h, x.hB.trans h, D.transport x.f h⟩

/-- Two representatives are related if they agree at some common later stage. -/
def Rel (x y : PreHom A B) : Prop :=
  ∃ (M : S) (hx : x.L ≤ M) (hy : y.L ≤ M), D.transport x.f hx = D.transport y.f hy

lemma rel_of_le {x y : PreHom A B} {M : S} {hx : x.L ≤ M} {hy : y.L ≤ M}
    (h : D.transport x.f hx = D.transport y.f hy) {N : S} (hMN : M ≤ N) :
    D.transport x.f (hx.trans hMN) = D.transport y.f (hy.trans hMN) := by
  rw [← D.transport_transport x.f hx hMN, h, D.transport_transport]

variable [IsDirected S (· ≤ ·)]

lemma rel_equivalence : Equivalence (@Rel S _ D P A B) where
  refl x := ⟨x.L, le_rfl, le_rfl, rfl⟩
  symm := fun ⟨M, hx, hy, h⟩ ↦ ⟨M, hy, hx, h.symm⟩
  trans := fun ⟨M, hx, hy, h⟩ ⟨M', hy', hz, h'⟩ ↦ by
    obtain ⟨N, hM, hM'⟩ := directed_of (· ≤ ·) M M'
    exact ⟨N, hx.trans hM, hz.trans hM', (rel_of_le h hM).trans (rel_of_le h' hM')⟩

omit [IsDirected S (· ≤ ·)] in
lemma rel_push (x : PreHom A B) {M : S} (h : x.L ≤ M) : Rel x (x.push h) :=
  ⟨M, h, le_rfl, by simp [push, D.transport_transport]⟩

end PreHom

variable (D P) [IsDirected S (· ≤ ·)]

instance PreHom.setoid (A B : D.Obj P) : Setoid (PreHom A B) :=
  ⟨PreHom.Rel, PreHom.rel_equivalence⟩

variable {D P}

namespace PreHom

variable {A B C Z : D.Obj P}

/-- A common upper bound. -/
noncomputable def upper (L L' : S) : S := (directed_of (· ≤ ·) L L').choose

lemma le_upper_left (L L' : S) : L ≤ upper L L' := (directed_of (· ≤ ·) L L').choose_spec.1

lemma le_upper_right (L L' : S) : L' ≤ upper L L' := (directed_of (· ≤ ·) L L').choose_spec.2

/-- The composite of two representatives, at a common later stage. -/
noncomputable def comp (x : PreHom A B) (y : PreHom B C) : PreHom A C :=
  ⟨upper x.L y.L, x.hA.trans (le_upper_left _ _), y.hB.trans (le_upper_right _ _),
    D.transport x.f (le_upper_left _ _) ≫ D.transport y.f (le_upper_right _ _)⟩

lemma comp_transport (x : PreHom A B) (y : PreHom B C) {N : S} (h : (comp x y).L ≤ N) :
    D.transport (comp x y).f h =
      D.transport x.f ((le_upper_left _ _).trans h) ≫
        D.transport y.f ((le_upper_right _ _).trans h) := by
  simp [comp, D.transport_comp, D.transport_transport]

lemma comp_rel {x x' : PreHom A B} {y y' : PreHom B C} (hx : Rel x x') (hy : Rel y y') :
    Rel (comp x y) (comp x' y') := by
  obtain ⟨N₁, hx₁, hx₂, hxx⟩ := hx
  obtain ⟨N₂, hy₁, hy₂, hyy⟩ := hy
  obtain ⟨P₁, h₁, h₂⟩ := directed_of (· ≤ ·) (comp x y).L (comp x' y').L
  obtain ⟨P₂, h₃, h₄⟩ := directed_of (· ≤ ·) N₁ N₂
  obtain ⟨Q, h₅, h₆⟩ := directed_of (· ≤ ·) P₁ P₂
  refine ⟨Q, h₁.trans h₅, h₂.trans h₅, ?_⟩
  rw [comp_transport, comp_transport]
  exact congrArg₂ (· ≫ ·) ((rel_of_le hxx (h₃.trans h₆)))
    ((rel_of_le hyy (h₄.trans h₆)))

end PreHom

variable (D P)

/-- The common-stage category of a directed system of categories, on the objects satisfying `P`:
morphisms are represented at a common stage, and identified when they agree at a later stage. -/
noncomputable instance category : Category (D.Obj P) where
  Hom A B := Quotient (PreHom.setoid D P A B)
  id A := Quotient.mk _ (⟨A.E, le_rfl, le_rfl, 𝟙 _⟩ : PreHom A A)
  comp := Quotient.map₂ PreHom.comp (fun _ _ hx _ _ hy ↦ PreHom.comp_rel hx hy)
  id_comp := by
    rintro A B ⟨y⟩
    refine Quotient.sound (Setoid.symm ?_)
    refine ⟨_, PreHom.le_upper_right _ _, le_rfl, ?_⟩
    simp [PreHom.comp, D.transport_id, D.transport_transport]
  comp_id := by
    rintro A B ⟨x⟩
    refine Quotient.sound (Setoid.symm ?_)
    refine ⟨_, PreHom.le_upper_left _ _, le_rfl, ?_⟩
    simp [PreHom.comp, D.transport_id, D.transport_transport]
  assoc := by
    rintro A B C Z ⟨x⟩ ⟨y⟩ ⟨z⟩
    refine Quotient.sound ?_
    obtain ⟨Q, h₁, h₂⟩ := directed_of (· ≤ ·) (PreHom.comp (PreHom.comp x y) z).L
      (PreHom.comp x (PreHom.comp y z)).L
    refine ⟨Q, h₁, h₂, ?_⟩
    rw [PreHom.comp_transport, PreHom.comp_transport, PreHom.comp_transport,
      PreHom.comp_transport, Category.assoc]

/-- A morphism of directed systems of categories: functors `F E : C E ⥤ C' E` commuting with the
transition functors through isomorphisms `κ`, compatibly with the composition isomorphisms. -/
structure Morphism (D' : TwoColimitData.{w, v, u} S) where
  /-- The functors. -/
  F : ∀ E, D.C E ⥤ D'.C E
  /-- The compatibility with the transition functors. -/
  κ : ∀ {E L : S} (h : E ≤ L), F E ⋙ D'.T h ≅ D.T h ⋙ F L
  hexagon : ∀ {E L L' : S} (h : E ≤ L) (h' : L ≤ L'),
    Functor.whiskerLeft (F E) (D'.comp h h').hom ≫ (κ (h.trans h')).hom =
      Functor.whiskerRight (κ h).hom (D'.T h') ≫ Functor.whiskerLeft (D.T h) (κ h').hom ≫
        Functor.whiskerRight (D.comp h h').hom (F L')

namespace Morphism

variable {D P} {D' : TwoColimitData.{w, v, u} S} (Φ : D.Morphism D')
  {P' : ∀ E, ObjectProperty (D'.C E)} (hP : ∀ E K, P E K → P' E ((Φ.F E).obj K))

/-- The image of an object. -/
def mapObj (A : D.Obj P) : D'.Obj P' := ⟨A.E, (Φ.F A.E).obj A.K, hP _ _ A.prop⟩

/-- The image of a representative of a morphism. -/
def mapPre {A B : D.Obj P} (x : PreHom A B) : PreHom (Φ.mapObj hP A) (Φ.mapObj hP B) :=
  ⟨x.L, x.hA, x.hB, (Φ.κ x.hA).hom.app A.K ≫ (Φ.F x.L).map x.f ≫ (Φ.κ x.hB).inv.app B.K⟩

omit [IsDirected S (· ≤ ·)] in
lemma κ_trans_hom_app {E L M : S} (h₁ : E ≤ L) (h₂ : L ≤ M) (K : D.C E) :
    (Φ.κ (h₁.trans h₂)).hom.app K = (D'.comp h₁ h₂).inv.app ((Φ.F E).obj K) ≫
      (D'.T h₂).map ((Φ.κ h₁).hom.app K) ≫ (Φ.κ h₂).hom.app ((D.T h₁).obj K) ≫
        (Φ.F M).map ((D.comp h₁ h₂).hom.app K) := by
  have := congr_app (Φ.hexagon h₁ h₂) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at this
  rw [← this, Iso.inv_hom_id_app_assoc]

omit [IsDirected S (· ≤ ·)] in
lemma map_transport {A B : D.Obj P} (x : PreHom A B) {M : S} (h : x.L ≤ M) :
    D'.transport (Φ.mapPre hP x).f h = (Φ.mapPre hP (x.push h)).f := by
  have hn := (Φ.κ h).hom.naturality x.f
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [mapPre, PreHom.push, transport, Functor.map_comp, Category.assoc]
  rw [← cancel_mono ((Φ.κ (x.hB.trans h)).hom.app B.K)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [κ_trans_hom_app Φ x.hB h, κ_trans_hom_app Φ x.hA h]
  erw [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc (D'.T h) ((Φ.κ x.hB).inv.app B.K),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hn]
  simp only [Category.assoc]
  congr 3
  erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

omit [IsDirected S (· ≤ ·)] in
lemma mapPre_rel {A B : D.Obj P} {x y : PreHom A B} (hxy : PreHom.Rel x y) :
    PreHom.Rel (Φ.mapPre hP x) (Φ.mapPre hP y) := by
  obtain ⟨M, hx, hy, h⟩ := hxy
  refine ⟨M, hx, hy, ?_⟩
  rw [map_transport, map_transport]
  simp only [mapPre, PreHom.push, h]

/-- The functor between common-stage categories induced by a morphism of directed systems. -/
noncomputable def functor : D.Obj P ⥤ D'.Obj P' where
  obj := Φ.mapObj hP
  map := Quotient.map (Φ.mapPre hP) (fun _ _ ↦ Φ.mapPre_rel hP)
  map_id A := Quotient.sound ⟨A.E, le_rfl, le_rfl, by simp [mapPre]; rfl⟩
  map_comp := by
    rintro A B C ⟨x⟩ ⟨y⟩
    refine Quotient.sound ⟨PreHom.upper x.L y.L, le_rfl, le_rfl, ?_⟩
    have hx := Φ.map_transport hP x (PreHom.le_upper_left x.L y.L)
    have hy := Φ.map_transport hP y (PreHom.le_upper_right x.L y.L)
    change D'.transport (Φ.mapPre hP (PreHom.comp x y)).f le_rfl =
      D'.transport (PreHom.comp (Φ.mapPre hP x) (Φ.mapPre hP y)).f le_rfl
    congr 1
    change _ = D'.transport (Φ.mapPre hP x).f _ ≫ D'.transport (Φ.mapPre hP y).f _
    rw [hx, hy]
    simp [mapPre, PreHom.push, PreHom.comp]

lemma functor_map_mk {A B : D.Obj P} (x : PreHom A B) :
    (Φ.functor hP).map (Quotient.mk _ x) = Quotient.mk _ (Φ.mapPre hP x) :=
  rfl

/-- The induced functor is faithful when every `F E` is: a filtered colimit of injections is an
injection. -/
instance faithful_functor [∀ E, (Φ.F E).Faithful] : (Φ.functor hP).Faithful where
  map_injective {A B} := by
    rintro ⟨x⟩ ⟨y⟩ hxy
    obtain ⟨M, hx, hy, h⟩ := Quotient.exact hxy
    refine Quotient.sound ⟨M, hx, hy, ?_⟩
    rw [map_transport, map_transport] at h
    simp only [mapPre, PreHom.push, cancel_epi, cancel_mono] at h
    exact (Φ.F M).map_injective h

/-- The induced functor is full when every `F E` is fully faithful. -/
instance full_functor [∀ E, (Φ.F E).Full] : (Φ.functor hP).Full where
  map_surjective {A B} := by
    rintro ⟨y⟩
    refine ⟨Quotient.mk _ ⟨y.L, y.hA, y.hB, (Φ.F y.L).preimage
      ((Φ.κ y.hA).inv.app A.K ≫ y.f ≫ (Φ.κ y.hB).hom.app B.K)⟩, ?_⟩
    refine Quotient.sound ⟨y.L, le_rfl, le_rfl, ?_⟩
    congr 1
    simp only [mapPre, Functor.map_preimage, Category.assoc, Iso.hom_inv_id_app_assoc,
      Iso.hom_inv_id_app]
    exact Category.comp_id y.f

end Morphism

section Restrict

variable (Q : ∀ E, ObjectProperty (D.C E))
  (hT : ∀ {E L : S} (h : E ≤ L) (K : D.C E), Q E K → Q L ((D.T h).obj K))

/-- The restriction of a directed system of categories to full subcategories stable under the
transition functors. -/
noncomputable def restrict : TwoColimitData.{w, v, u} S where
  C E := (Q E).FullSubcategory
  T h := (Q _).lift ((Q _).ι ⋙ D.T h) (fun K ↦ hT h K.1 K.2)
  comp h h' := NatIso.ofComponents
    (fun K ↦ (ObjectProperty.fullyFaithfulι _).preimageIso ((D.comp h h').app K.1))
    (fun f ↦ (ObjectProperty.fullyFaithfulι _).map_injective ((D.comp h h').hom.naturality
      ((Q _).ι.map f)))
  cocycle h h' h'' := by
    ext K
    exact congr_app (D.cocycle h h' h'') K.1

variable {D} {D' : TwoColimitData.{w, v, u} S} (Φ : D.Morphism D')
  (Q' : ∀ E, ObjectProperty (D'.C E))
  (hT' : ∀ {E L : S} (h : E ≤ L) (K : D'.C E), Q' E K → Q' L ((D'.T h).obj K))
  (hF : ∀ E (K : D.C E), Q E K → Q' E ((Φ.F E).obj K))

/-- The restriction of a morphism of directed systems to full subcategories. -/
noncomputable def Morphism.restrict : (D.restrict Q hT).Morphism (D'.restrict Q' hT') where
  F E := (Q' E).lift ((Q E).ι ⋙ Φ.F E) (fun K ↦ hF E K.1 K.2)
  κ h := NatIso.ofComponents
    (fun K ↦ (ObjectProperty.fullyFaithfulι _).preimageIso ((Φ.κ h).app K.1))
    (fun f ↦ (ObjectProperty.fullyFaithfulι _).map_injective ((Φ.κ h).hom.naturality
      ((Q _).ι.map f)))
  hexagon h h' := by
    ext K
    exact (Q' _).ι.map_injective (congr_app (Φ.hexagon h h') K.1)

instance Morphism.full_restrict_F [∀ E, (Φ.F E).Full] (E : S) :
    ((Φ.restrict Q hT Q' hT' hF).F E).Full :=
  have : ((Φ.restrict Q hT Q' hT' hF).F E ⋙ (Q' E).ι).Full :=
    inferInstanceAs ((Q E).ι ⋙ Φ.F E).Full
  have := (ObjectProperty.fullyFaithfulι (Q' E)).faithful
  Functor.Full.of_comp_faithful _ (Q' E).ι

instance Morphism.faithful_restrict_F [∀ E, (Φ.F E).Faithful] (E : S) :
    ((Φ.restrict Q hT Q' hT' hF).F E).Faithful :=
  have : ((Φ.restrict Q hT Q' hT' hF).F E ⋙ (Q' E).ι).Faithful :=
    inferInstanceAs ((Q E).ι ⋙ Φ.F E).Faithful
  Functor.Faithful.of_comp _ (Q' E).ι

end Restrict

section Transport

variable (T' : ∀ {E L : S}, E ≤ L → D.C E ⥤ D.C L) (e : ∀ {E L : S} (h : E ≤ L), T' h ≅ D.T h)

/-- The directed system with transition functors replaced by isomorphic ones `T'`, the
composition isomorphisms being transported along `e`. -/
noncomputable def transportIso : TwoColimitData.{w, v, u} S where
  C := D.C
  T := T'
  comp h h' := Functor.isoWhiskerRight (e h) _ ≪≫ Functor.isoWhiskerLeft _ (e h') ≪≫
    D.comp h h' ≪≫ (e (h.trans h')).symm
  cocycle h h' h'' := by
    ext K
    have := congr_app (D.cocycle h h' h'') K
    simp only [Functor.comp_obj, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at this
    simp only [Functor.comp_obj, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc (T' h'') ((e (h.trans h')).inv.app K), Iso.inv_hom_id_app,
      Functor.map_id, Category.id_comp, (e h'').hom.naturality_assoc, reassoc_of% this,
      ← (e (h'.trans h'')).inv.naturality_assoc, Iso.inv_hom_id_app_assoc,
      ← (D.comp h' h'').hom.naturality_assoc, Functor.comp_map,
      ← (e h'').hom.naturality_assoc, ← Functor.map_comp_assoc,
      ← Functor.map_comp_assoc, (e h').hom.naturality]

variable {D} {D' : TwoColimitData.{w, v, u} S} (Φ : D.Morphism D')
  (T'' : ∀ {E L : S}, E ≤ L → D'.C E ⥤ D'.C L) (e' : ∀ {E L : S} (h : E ≤ L), T'' h ≅ D'.T h)

/-- A morphism of directed systems, transported to the systems with isomorphic transition
functors. -/
noncomputable def Morphism.transportIso :
    (D.transportIso T' e).Morphism (D'.transportIso T'' e') where
  F := Φ.F
  κ h := Functor.isoWhiskerLeft (Φ.F _) (e' h) ≪≫ Φ.κ h ≪≫ Functor.isoWhiskerRight (e h).symm _
  hexagon h h' := by
    ext K
    have := congr_app (Φ.hexagon h h') K
    simp only [Functor.comp_obj, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at this
    change _ = _
    simp only [TwoColimitData.transportIso, Functor.comp_obj, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
    rw [Iso.inv_hom_id_app_assoc, reassoc_of% this]
    have n1 := (e' h').hom.naturality
    have n2 := (Φ.κ h').hom.naturality
    have n3 := (e h').hom.naturality
    simp only [Functor.comp_obj, Functor.comp_map] at n1 n2 n3
    simp only [← Functor.map_comp_assoc, reassoc_of% n3, Iso.inv_hom_id_app_assoc]
    simp only [Functor.map_comp, Category.assoc, ← reassoc_of% n2, ← reassoc_of% n1]
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    erw [Category.id_comp]

end Transport

end TwoColimitData

end CategoryTheory
