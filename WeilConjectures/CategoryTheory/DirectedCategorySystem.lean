/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Order.Lattice

/-!
# The common-stage category of a directed system of categories

A *directed system of categories* over a join-semilattice `ι` (`DirectedCategorySystem ι`) is a
family of categories `C i` with transition functors `F_{ij} : C i ⥤ C j` for `i ≤ j`, together
with coherent isomorphisms `F_{ii} ≅ 𝟭` and `F_{ij} ⋙ F_{jk} ≅ F_{ik}`: a pseudofunctor from the
preorder `ι` to categories, written out by hand.

Its *common-stage category* `DirectedCategorySystem.Colimit` has as objects the pairs `(i, X)`
with `X : C i`, and as morphisms `(i, X) ⟶ (j, Y)` the colimit, over the stages `k ≥ i, j`, of the
morphisms `F_{ik} X ⟶ F_{jk} Y`, two such morphisms being identified when they agree at a common
larger stage. Composition is computed at a common stage. This is the `2`-colimit of the system,
used for the category `Dᵇc(Y, ℚ̄_ℓ)` of the blueprint
(`def-weil-algebraically-closed-coefficients`),
whose stages are the rationalized categories `Dᵇc(Y, E)` for the finite extensions `E` of `ℚ_ℓ`
inside `ℚ̄_ℓ`.

## Main definitions

- `CategoryTheory.DirectedCategorySystem`: a directed system of categories.
- `CategoryTheory.DirectedCategorySystem.Colimit`: its common-stage category.
- `CategoryTheory.DirectedCategorySystem.Colimit.homMk`: the morphism of the common-stage category
  represented by a morphism at a given stage.

## Main statements

- `CategoryTheory.DirectedCategorySystem.Colimit.homMk_eq_homMk_iff`: two representatives define
  the same morphism if and only if they agree at a common larger stage.
- `CategoryTheory.DirectedCategorySystem.Colimit.exists_iso_homMk`: an isomorphism of the
  common-stage category is represented by an isomorphism at some finite stage.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category CategoryTheory.Functor

/-- A directed system of categories over a join-semilattice `ι`: categories `obj i`, transition
functors `map h : obj i ⥤ obj j` for `h : i ≤ j`, and coherent isomorphisms
`map (le_refl i) ≅ 𝟭` and `map hij ⋙ map hjk ≅ map (hij.trans hjk)` (a pseudofunctor from `ι`
to categories). -/
structure DirectedCategorySystem (ι : Type w) [SemilatticeSup ι] where
  /-- The category at the stage `i`. -/
  obj : ι → Type u
  /-- The categories of the system. -/
  category (i : ι) : Category.{v} (obj i)
  /-- The transition functor from the stage `i` to a stage `j ≥ i`. -/
  map {i j : ι} (hij : i ≤ j) : obj i ⥤ obj j
  /-- The transition functor of `i ≤ i` is the identity. -/
  mapId (i : ι) : map (le_refl i) ≅ 𝟭 (obj i)
  /-- The composition of two transition functors is the transition functor. -/
  mapComp {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) : map hij ⋙ map hjk ≅ map (hij.trans hjk)
  mapComp_assoc {i j k l : ι} (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    isoWhiskerLeft (map hij) (mapComp hjk hkl) ≪≫ mapComp hij (hjk.trans hkl) =
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (mapComp hij hjk) (map hkl) ≪≫
        mapComp (hij.trans hjk) hkl
  mapComp_id {i j : ι} (hij : i ≤ j) :
    mapComp hij (le_refl j) = isoWhiskerLeft (map hij) (mapId j) ≪≫ Functor.rightUnitor _
  id_mapComp {i j : ι} (hij : i ≤ j) :
    mapComp (le_refl i) hij = isoWhiskerRight (mapId i) (map hij) ≪≫ Functor.leftUnitor _

namespace DirectedCategorySystem

attribute [instance] category

variable {ι : Type w} [SemilatticeSup ι] (S : DirectedCategorySystem.{w, v, u} ι)

/-- An object of the common-stage category of `S`: a stage `i` and an object of the category at
the stage `i`. -/
structure Colimit where
  /-- The stage at which the object is defined. -/
  stage : ι
  /-- The object at that stage. -/
  pt : S.obj stage

namespace Colimit

variable {S}

/-- The incarnation `F_{ij} X` at a stage `j ≥ i` of an object `(i, X)` of the common-stage
category. -/
abbrev «at» (x : S.Colimit) {j : ι} (h : x.stage ≤ j) : S.obj j :=
  (S.map h).obj x.pt

/-- The transport `F_{jk} f`, a morphism at the stage `k`, of a morphism `f` between
incarnations at the stage `j ≤ k`. -/
def transport {x y : S.Colimit} {j k : ι} (hjk : j ≤ k) {hx : x.stage ≤ j}
    {hy : y.stage ≤ j} (f : x.at hx ⟶ y.at hy) :
    x.at (hx.trans hjk) ⟶ y.at (hy.trans hjk) :=
  (S.mapComp hx hjk).inv.app x.pt ≫ (S.map hjk).map f ≫ (S.mapComp hy hjk).hom.app y.pt

@[simp]
lemma transport_id {x : S.Colimit} {j k : ι} (hjk : j ≤ k) (hx : x.stage ≤ j) :
    transport hjk (𝟙 (x.at hx)) = 𝟙 _ := by
  simp [transport]

@[simp]
lemma transport_comp {x y z : S.Colimit} {j k : ι} (hjk : j ≤ k) {hx : x.stage ≤ j}
    {hy : y.stage ≤ j} {hz : z.stage ≤ j} (f : x.at hx ⟶ y.at hy) (g : y.at hy ⟶ z.at hz) :
    transport hjk (f ≫ g) = transport hjk f ≫ transport hjk g := by
  simp [transport]

lemma transport_refl {x y : S.Colimit} {j : ι} {hx : x.stage ≤ j} {hy : y.stage ≤ j}
    (f : x.at hx ⟶ y.at hy) : transport (le_refl j) f = f := by
  have h (z : S.Colimit) (hz : z.stage ≤ j) :
      (S.mapComp hz (le_refl j)).hom.app z.pt = (S.mapId j).hom.app (z.at hz) := by
    simp [S.mapComp_id hz]
  have h' (z : S.Colimit) (hz : z.stage ≤ j) :
      (S.mapComp hz (le_refl j)).inv.app z.pt = (S.mapId j).inv.app (z.at hz) := by
    simp [S.mapComp_id hz]
  simp only [transport, h, h']
  rw [← (S.mapId j).inv.naturality_assoc]
  simp

/-- The associativity of the transition isomorphisms, at an object. -/
@[reassoc]
lemma mapComp_hom_app_comp {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (z : S.Colimit)
    (hz : z.stage ≤ i) :
    (S.mapComp hij hjk).hom.app (z.at hz) ≫ (S.mapComp hz (hij.trans hjk)).hom.app z.pt =
      (S.map hjk).map ((S.mapComp hz hij).hom.app z.pt) ≫
        (S.mapComp (hz.trans hij) hjk).hom.app z.pt := by
  have := congrArg (fun e ↦ e.hom.app z.pt) (S.mapComp_assoc hz hij hjk)
  simpa using this

lemma transport_trans {x y : S.Colimit} {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    {hx : x.stage ≤ i} {hy : y.stage ≤ i} (f : x.at hx ⟶ y.at hy) :
    transport hjk (transport hij f) = transport (hij.trans hjk) f := by
  simp only [transport]
  rw [← cancel_epi ((S.map hjk).map ((S.mapComp hx hij).hom.app x.pt) ≫
    (S.mapComp (hx.trans hij) hjk).hom.app x.pt)]
  simp only [assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, id_comp,
    ← mapComp_hom_app_comp hij hjk y hy, ← mapComp_hom_app_comp_assoc hij hjk x hx,
    Iso.hom_inv_id_app_assoc]
  exact (S.mapComp hij hjk).hom.naturality_assoc f _

variable (x y : S.Colimit)

/-- A representative of a morphism `x ⟶ y` of the common-stage category: a morphism between the
incarnations of `x` and `y` at some stage. -/
structure PreHom where
  /-- The stage of the representative. -/
  stage : ι
  le_left : x.stage ≤ stage
  le_right : y.stage ≤ stage
  /-- The representative itself. -/
  hom : x.at le_left ⟶ y.at le_right

variable {x y}

/-- Two representatives are equivalent if they agree at a common larger stage. -/
def PreHom.Rel (f g : PreHom x y) : Prop :=
  ∃ (k : ι) (hf : f.stage ≤ k) (hg : g.stage ≤ k), transport hf f.hom = transport hg g.hom

lemma PreHom.Rel.refl (f : PreHom x y) : f.Rel f :=
  ⟨f.stage, le_rfl, le_rfl, rfl⟩

lemma PreHom.Rel.symm {f g : PreHom x y} (h : f.Rel g) : g.Rel f := by
  obtain ⟨k, hf, hg, h⟩ := h
  exact ⟨k, hg, hf, h.symm⟩

lemma PreHom.Rel.trans {f g h : PreHom x y} (h₁ : f.Rel g) (h₂ : g.Rel h) : f.Rel h := by
  obtain ⟨k, hf, hg, e₁⟩ := h₁
  obtain ⟨k', hg', hh, e₂⟩ := h₂
  refine ⟨k ⊔ k', hf.trans le_sup_left, hh.trans le_sup_right, ?_⟩
  rw [← transport_trans hf le_sup_left, e₁, transport_trans,
    ← transport_trans hh le_sup_right, ← e₂, transport_trans]

/-- The setoid of representatives of morphisms `x ⟶ y`. -/
instance PreHom.setoid : Setoid (PreHom x y) where
  r := PreHom.Rel
  iseqv := ⟨PreHom.Rel.refl, PreHom.Rel.symm, PreHom.Rel.trans⟩

/-- The transport of a representative to a larger stage. -/
def PreHom.transport (f : PreHom x y) {k : ι} (hk : f.stage ≤ k) : PreHom x y :=
  ⟨k, f.le_left.trans hk, f.le_right.trans hk, Colimit.transport hk f.hom⟩

lemma PreHom.rel_transport (f : PreHom x y) {k : ι} (hk : f.stage ≤ k) :
    f.Rel (f.transport hk) :=
  ⟨k, hk, le_rfl, (transport_refl _).symm⟩

/-- The composition of representatives, computed at the join of their stages. -/
def PreHom.comp {z : S.Colimit} (f : PreHom x y) (g : PreHom y z) : PreHom x z :=
  ⟨f.stage ⊔ g.stage, f.le_left.trans le_sup_left, g.le_right.trans le_sup_right,
    Colimit.transport le_sup_left f.hom ≫ Colimit.transport le_sup_right g.hom⟩

lemma PreHom.comp_rel_comp {z : S.Colimit} {f f' : PreHom x y} {g g' : PreHom y z}
    (hf : f.Rel f') (hg : g.Rel g') : (f.comp g).Rel (f'.comp g') := by
  obtain ⟨k, h₁, h₂, e⟩ := hf
  obtain ⟨k', h₁', h₂', e'⟩ := hg
  let K := (f.stage ⊔ g.stage) ⊔ (f'.stage ⊔ g'.stage) ⊔ k ⊔ k'
  have hK₁ : f.stage ⊔ g.stage ≤ K := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hK₂ : f'.stage ⊔ g'.stage ≤ K := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hk : k ≤ K := le_sup_right.trans le_sup_left
  have hk' : k' ≤ K := le_sup_right
  refine ⟨K, hK₁, hK₂, ?_⟩
  simp only [PreHom.comp, transport_comp, transport_trans]
  congr 1
  · rw [← transport_trans h₁ hk, e, transport_trans]
  · rw [← transport_trans h₁' hk', e', transport_trans]

end Colimit

variable {S} in
/-- The common-stage category of a directed system of categories: morphisms are represented at a
common finite stage, and identified when they agree at a common larger stage. -/
instance Colimit.category : Category (S.Colimit) where
  Hom x y := Quotient (Colimit.PreHom.setoid (x := x) (y := y))
  id x := ⟦⟨x.stage, le_rfl, le_rfl, 𝟙 _⟩⟧
  comp f g := Quotient.map₂ Colimit.PreHom.comp
    (fun _ _ hf _ _ hg ↦ Colimit.PreHom.comp_rel_comp hf hg) f g
  id_comp f := by
    induction f using Quotient.inductionOn with | h f
    refine Quotient.sound ⟨_, le_rfl, le_sup_right, ?_⟩
    simp [Colimit.PreHom.comp, Colimit.transport_refl]
  comp_id f := by
    induction f using Quotient.inductionOn with | h f
    refine Quotient.sound ⟨_, le_rfl, le_sup_left, ?_⟩
    simp [Colimit.PreHom.comp, Colimit.transport_refl]
  assoc f g h := by
    induction f using Quotient.inductionOn with | h f
    induction g using Quotient.inductionOn with | h g
    induction h using Quotient.inductionOn with | h h
    refine Quotient.sound ⟨f.stage ⊔ g.stage ⊔ h.stage, le_rfl,
      sup_le (le_sup_left.trans le_sup_left) (sup_le (le_sup_right.trans le_sup_left)
        le_sup_right), ?_⟩
    simp [Colimit.PreHom.comp, Colimit.transport_refl, Colimit.transport_trans]

namespace Colimit

variable {S} {x y z : S.Colimit}

/-- The morphism of the common-stage category represented by a morphism at the stage `k`. -/
def homMk (k : ι) (hx : x.stage ≤ k) (hy : y.stage ≤ k) (f : x.at hx ⟶ y.at hy) : x ⟶ y :=
  ⟦⟨k, hx, hy, f⟩⟧

lemma homMk_eq_homMk_iff {k k' : ι} {hx : x.stage ≤ k} {hy : y.stage ≤ k} {hx' : x.stage ≤ k'}
    {hy' : y.stage ≤ k'} (f : x.at hx ⟶ y.at hy) (f' : x.at hx' ⟶ y.at hy') :
    homMk k hx hy f = homMk k' hx' hy' f' ↔
      ∃ (m : ι) (h : k ≤ m) (h' : k' ≤ m), transport h f = transport h' f' :=
  Quotient.eq (r := PreHom.setoid)

lemma homMk_transport {j k : ι} (hjk : j ≤ k) {hx : x.stage ≤ j} {hy : y.stage ≤ j}
    (f : x.at hx ⟶ y.at hy) : homMk k _ _ (transport hjk f) = homMk j hx hy f :=
  Quotient.sound (PreHom.Rel.symm (PreHom.rel_transport ⟨j, hx, hy, f⟩ hjk))

lemma exists_homMk (φ : x ⟶ y) :
    ∃ (k : ι) (hx : x.stage ≤ k) (hy : y.stage ≤ k) (f : x.at hx ⟶ y.at hy),
      φ = homMk k hx hy f := by
  induction φ using Quotient.inductionOn with | h f
  exact ⟨f.stage, f.le_left, f.le_right, f.hom, rfl⟩

/-- Every morphism is represented at every stage larger than some given stage. -/
lemma exists_homMk_of_le (φ : x ⟶ y) :
    ∃ (k : ι) (hx : x.stage ≤ k) (hy : y.stage ≤ k), ∀ (m : ι) (hkm : k ≤ m),
      ∃ f : x.at (hx.trans hkm) ⟶ y.at (hy.trans hkm), φ = homMk m _ _ f := by
  obtain ⟨k, hx, hy, f, rfl⟩ := exists_homMk φ
  exact ⟨k, hx, hy, fun m hkm ↦ ⟨transport hkm f, (homMk_transport hkm f).symm⟩⟩

lemma id_eq_homMk (k : ι) (hx : x.stage ≤ k) : 𝟙 x = homMk k hx hx (𝟙 _) := by
  have := homMk_transport (x := x) (y := x) hx (hx := le_rfl) (hy := le_rfl) (𝟙 _)
  rw [transport_id] at this
  exact this.symm

/-- The composition of two represented morphisms is represented at the join of their stages. -/
lemma homMk_comp_homMk' {k k' : ι} {hx : x.stage ≤ k} {hy : y.stage ≤ k} {hy' : y.stage ≤ k'}
    {hz : z.stage ≤ k'} (f : x.at hx ⟶ y.at hy) (g : y.at hy' ⟶ z.at hz) :
    homMk k hx hy f ≫ homMk k' hy' hz g =
      homMk (k ⊔ k') _ _ (transport le_sup_left f ≫ transport le_sup_right g) :=
  rfl

@[reassoc]
lemma homMk_comp_homMk (k : ι) (hx : x.stage ≤ k) (hy : y.stage ≤ k) (hz : z.stage ≤ k)
    (f : x.at hx ⟶ y.at hy) (g : y.at hy ⟶ z.at hz) :
    homMk k hx hy f ≫ homMk k hy hz g = homMk k hx hz (f ≫ g) := by
  rw [homMk_comp_homMk', ← transport_comp, homMk_transport]

/-- An isomorphism at some stage gives an isomorphism of the common-stage category. -/
@[simps]
def isoMk (k : ι) (hx : x.stage ≤ k) (hy : y.stage ≤ k) (e : x.at hx ≅ y.at hy) : x ≅ y where
  hom := homMk k hx hy e.hom
  inv := homMk k hy hx e.inv
  hom_inv_id := by rw [homMk_comp_homMk, e.hom_inv_id, ← id_eq_homMk]
  inv_hom_id := by rw [homMk_comp_homMk, e.inv_hom_id, ← id_eq_homMk]

/-- **An isomorphism of the common-stage category is represented by an isomorphism at some finite
stage.** -/
lemma exists_iso_homMk (e : x ≅ y) :
    ∃ (k : ι) (hx : x.stage ≤ k) (hy : y.stage ≤ k) (e' : x.at hx ≅ y.at hy),
      e.hom = homMk k hx hy e'.hom := by
  obtain ⟨k₁, hx₁, hy₁, f, hf⟩ := exists_homMk e.hom
  obtain ⟨k₂, hy₂, hx₂, g, hg⟩ := exists_homMk e.inv
  let k := k₁ ⊔ k₂
  rw [← homMk_transport (le_sup_left : k₁ ≤ k)] at hf
  rw [← homMk_transport (le_sup_right : k₂ ≤ k)] at hg
  set f' := transport (le_sup_left : k₁ ≤ k) f
  set g' := transport (le_sup_right : k₂ ≤ k) g
  have h₁ := e.hom_inv_id
  have h₂ := e.inv_hom_id
  rw [hf, hg, homMk_comp_homMk, id_eq_homMk k, homMk_eq_homMk_iff] at h₁ h₂
  obtain ⟨m₁, a₁, b₁, h₁⟩ := h₁
  obtain ⟨m₂, a₂, b₂, h₂⟩ := h₂
  let m := m₁ ⊔ m₂
  have hm₁ : k ≤ m := a₁.trans le_sup_left
  refine ⟨m, _, _, ⟨transport hm₁ f', transport hm₁ g', ?_, ?_⟩, ?_⟩
  · rw [← transport_comp, ← transport_trans a₁ le_sup_left, h₁, transport_trans,
      transport_id]
  · rw [← transport_comp, ← transport_trans a₂ le_sup_right, h₂, transport_trans,
      transport_id]
  · rw [hf, homMk_transport]

/-- The object of the common-stage category defined by an object at the stage `i`. -/
abbrev ofStage (i : ι) (X : S.obj i) : S.Colimit := ⟨i, X⟩

/-- An object at the stage `i` and its image at a stage `j ≥ i` define isomorphic objects of the
common-stage category. -/
def ofStageIso {i j : ι} (h : i ≤ j) (X : S.obj i) :
    ofStage i X ≅ ofStage j ((S.map h).obj X) :=
  isoMk j h le_rfl ((S.mapId j).symm.app _)

end Colimit

end DirectedCategorySystem

end CategoryTheory
