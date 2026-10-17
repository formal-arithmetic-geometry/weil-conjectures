/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Systems of étale sheaves over an inverse system of schemes

Let `D : I ⥤ Scheme` be an inverse system of schemes with a cone `c` (in the applications a
limit cone). A *system of étale sheaves* over `D` consists of an abelian étale sheaf `Gᵢ` on
every `Dᵢ` together with transition maps `Gⱼ(V) ⟶ Gᵢ(W)` for every morphism `W ⟶ V` of étale
schemes lying over a transition map `Dᵢ ⟶ Dⱼ`, compatible with composition. Such a system is
encoded as a presheaf on the *total category* `AlgebraicGeometry.Etale.LimitSystem.Total D`,
whose objects are pairs of an index `i` and an étale `Dᵢ`-scheme, so that the compatibilities are
the functoriality of the presheaf.

Systems need not be *cartesian*: the transition maps need not identify `Gᵢ` with the pullback of
`Gⱼ`. This flexibility is what allows dimension shifting in the proof of the continuity of
étale cohomology: a system embeds into a system of injective sheaves, whose quotient is again
a system, but in general not a cartesian one.

## Main definitions

- `AlgebraicGeometry.Etale.LimitSystem.Total`: the total category of the small étale sites of
  the `Dᵢ`.
- `AlgebraicGeometry.Etale.LimitSystem.fibre`: the inclusion of the small étale site of `Dᵢ`.
- `AlgebraicGeometry.Etale.LimitSystem.toLimit`: base change to the cone point `c.pt`.
- `AlgebraicGeometry.Etale.LimitSystem.System`: systems of abelian étale sheaves over `D`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale.LimitSystem

open Scheme

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})

/-- The total category of the small étale sites of an inverse system of schemes `D`: an object
is an index `i` together with an étale `Dᵢ`-scheme. -/
structure Total where
  /-- The index. -/
  idx : I
  /-- The étale `D idx`-scheme. -/
  obj : (D.obj idx).Etale

variable {D}

/-- A morphism `(i, W) ⟶ (j, V)` of the total category: a morphism `i ⟶ j` together with a
morphism of schemes `W ⟶ V` over `Dᵢ ⟶ Dⱼ`. -/
@[ext]
structure Total.Hom (a b : Total D) where
  /-- The morphism of indices. -/
  idx : a.idx ⟶ b.idx
  /-- The morphism of schemes. -/
  left : a.obj.left ⟶ b.obj.left
  w : left ≫ b.obj.hom = a.obj.hom ≫ D.map idx := by cat_disch

attribute [reassoc] Total.Hom.w

instance : Category (Total D) where
  Hom := Total.Hom
  id a := { idx := 𝟙 _, left := 𝟙 _ }
  comp f g := { idx := f.idx ≫ g.idx, left := f.left ≫ g.left
                w := by simp [Total.Hom.w, Total.Hom.w_assoc] }

namespace Total

@[ext]
lemma hom_ext {a b : Total D} {f g : a ⟶ b} (h₁ : f.idx = g.idx) (h₂ : f.left = g.left) :
    f = g :=
  Total.Hom.ext h₁ h₂

@[simp]
lemma id_idx (a : Total D) : Total.Hom.idx (𝟙 a) = 𝟙 a.idx := rfl

@[simp]
lemma id_left (a : Total D) : Total.Hom.left (𝟙 a) = 𝟙 a.obj.left := rfl

@[simp, reassoc]
lemma comp_idx {a b c : Total D} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).idx = f.idx ≫ g.idx := rfl

@[simp, reassoc]
lemma comp_left {a b c : Total D} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).left = f.left ≫ g.left := rfl

/-- Constructor for morphisms of the total category. -/
abbrev homMk {a b : Total D} (g : a.idx ⟶ b.idx) (f : a.obj.left ⟶ b.obj.left)
    (w : f ≫ b.obj.hom = a.obj.hom ≫ D.map g := by cat_disch) : a ⟶ b :=
  { idx := g, left := f, w := w }

end Total

variable (D) in
/-- The inclusion of the small étale site of `Dᵢ` into the total category. -/
@[simps]
def fibre (i : I) : (D.obj i).Etale ⥤ Total D where
  obj V := ⟨i, V⟩
  map f := Total.homMk (𝟙 i) f.left (by simp)

/-- The morphism `(j, V ×_{Dᵢ} Dⱼ) ⟶ (i, V)` of the total category over `g : j ⟶ i`. -/
noncomputable def pullbackHom {j i : I} (g : j ⟶ i) (V : (D.obj i).Etale) :
    (⟨j, (MorphismProperty.Over.pullback @Etale ⊤ (D.map g)).obj V⟩ : Total D) ⟶ ⟨i, V⟩ :=
  Total.homMk g (pullback.fst V.hom (D.map g)) pullback.condition

section ToLimit

variable (c : Cone D)

variable (D) in
/-- Base change to the cone point `c.pt`: the functor `(i, V) ↦ V ×_{Dᵢ} c.pt` from the total
category to the small étale site of `c.pt`. -/
@[simps obj]
noncomputable def toLimit : Total D ⥤ c.pt.Etale where
  obj a := (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app a.idx)).obj a.obj
  map {a b} f := MorphismProperty.Over.homMk
    (pullback.map a.obj.hom (c.π.app a.idx) b.obj.hom (c.π.app b.idx) f.left (𝟙 _)
      (D.map f.idx) f.w.symm (by simp)) (by simp) trivial
  map_id a := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext <;> simp [MorphismProperty.Over.homMk]
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext <;> simp [MorphismProperty.Over.homMk, MorphismProperty.Comma.comp_left]

@[reassoc (attr := simp)]
lemma toLimit_map_left_fst {a b : Total D} (f : a ⟶ b) :
    ((toLimit D c).map f).left ≫ pullback.fst b.obj.hom (c.π.app b.idx) =
      pullback.fst a.obj.hom (c.π.app a.idx) ≫ f.left := by
  simp [toLimit]

@[reassoc (attr := simp)]
lemma toLimit_map_left_snd {a b : Total D} (f : a ⟶ b) :
    ((toLimit D c).map f).left ≫ pullback.snd b.obj.hom (c.π.app b.idx) =
      pullback.snd a.obj.hom (c.π.app a.idx) := by
  simp [toLimit]

/-- On a fibre, base change to the cone point is the base change functor along
`c.π.app i`. -/
lemma toLimit_map_fibre_map {i : I} {V V' : (D.obj i).Etale} (f : V ⟶ V') :
    (toLimit D c).map ((fibre D i).map f) =
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app i)).map f := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext <;> simp [MorphismProperty.Over.pullback, MorphismProperty.Over.homMk]

end ToLimit

variable (D) in
/-- A *system of abelian étale sheaves* over the inverse system `D`: a presheaf on the total
category whose restriction to every fibre is a sheaf. -/
structure System where
  /-- The underlying presheaf on the total category. -/
  presheaf : (Total D)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}
  isSheaf (i : I) :
    Presheaf.IsSheaf (D.obj i).smallEtaleTopology ((fibre D i).op ⋙ presheaf)

namespace System

/-- A morphism of systems is a morphism of the underlying presheaves. -/
@[ext]
structure Hom (G H : System D) where
  /-- The morphism of presheaves. -/
  hom : G.presheaf ⟶ H.presheaf

instance : Category (System D) where
  Hom := Hom
  id G := ⟨𝟙 G.presheaf⟩
  comp f g := ⟨f.hom ≫ g.hom⟩

@[ext]
lemma hom_ext {G H : System D} {f g : G ⟶ H} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

@[simp]
lemma id_hom (G : System D) : Hom.hom (𝟙 G) = 𝟙 G.presheaf := rfl

@[simp, reassoc]
lemma comp_hom {G H K : System D} (f : G ⟶ H) (g : H ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

/-- The sheaf `Gᵢ` of a system `G` on the small étale site of `Dᵢ`. -/
def sheaf (G : System D) (i : I) : Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ⟨(fibre D i).op ⋙ G.presheaf, G.isSheaf i⟩

/-- The morphism of sheaves `Gᵢ ⟶ Hᵢ` induced by a morphism of systems. -/
def sheafMap {G H : System D} (f : G ⟶ H) (i : I) : G.sheaf i ⟶ H.sheaf i :=
  ⟨Functor.whiskerLeft (fibre D i).op f.hom⟩

@[simp]
lemma sheafMap_hom_app {G H : System D} (f : G ⟶ H) (i : I) (V : (D.obj i).Etaleᵒᵖ) :
    (sheafMap f i).hom.app V = f.hom.app (op ⟨i, V.unop⟩) := rfl

@[simp]
lemma sheafMap_id (G : System D) (i : I) : sheafMap (𝟙 G) i = 𝟙 _ := rfl

@[simp, reassoc]
lemma sheafMap_comp {G H K : System D} (f : G ⟶ H) (g : H ⟶ K) (i : I) :
    sheafMap (f ≫ g) i = sheafMap f i ≫ sheafMap g i := rfl

/-- The transition map `Gᵢ ⟶ (D g)_* Gⱼ` of a system along `g : j ⟶ i`. -/
noncomputable def transition (G : System D) {j i : I} (g : j ⟶ i) :
    G.sheaf i ⟶ (D.map g)_*[AddCommGrpCat.{u + 1}].obj (G.sheaf j) :=
  ⟨{ app V := G.presheaf.map (pullbackHom g V.unop).op
     naturality {V V'} f := by
       change G.presheaf.map ((fibre D i).map f.unop).op ≫ G.presheaf.map _ =
         G.presheaf.map _ ≫ G.presheaf.map ((fibre D j).map
           ((MorphismProperty.Over.pullback @Etale ⊤ (D.map g)).map f.unop)).op
       rw [← G.presheaf.map_comp, ← G.presheaf.map_comp, ← op_comp, ← op_comp]
       congr 2
       ext
       · simp [pullbackHom]
       · simp [pullbackHom, MorphismProperty.Over.pullback]
       · simp [pullbackHom] }⟩

@[simp]
lemma transition_hom_app (G : System D) {j i : I} (g : j ⟶ i) (V : (D.obj i).Etaleᵒᵖ) :
    (G.transition g).hom.app V = G.presheaf.map (pullbackHom g V.unop).op := rfl

/-- The transition maps are natural in the system. -/
@[reassoc]
lemma sheafMap_transition {G H : System D} (f : G ⟶ H) {j i : I} (g : j ⟶ i) :
    sheafMap f i ≫ H.transition g =
      G.transition g ≫ (D.map g)_*[AddCommGrpCat.{u + 1}].map (sheafMap f j) := by
  ext V : 3
  exact (f.hom.naturality _).symm

end System

end AlgebraicGeometry.Etale.LimitSystem
