/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.Composition
public import WeilConjectures.CategoryTheory.ExchangeFormalism.Cube
public import WeilConjectures.CategoryTheory.ExchangeFormalism.PushforwardBaseChange

/-!
# Morphisms of exchange formalisms and the composition isomorphism

A *morphism* `Θ : F ⟶ F'` of exchange formalisms along a functor `Φ : 𝒞 ⥤ 𝒞'` of the index
categories (`CategoryTheory.ExchangeFormalism.Morphism`) consists of functors
`Θ.pull X : F.obj X ⥤ F'.obj (Φ.obj X)` ("pullback along `π_X`") together with isomorphisms
`f^* ⋙ π_X^* ≅ π_Y^* ⋙ (Φ f)^*` (`Θ.pbIso`) compatible with the composition isomorphisms of the
pullbacks (`Θ.pbIso_comp`). The motivating example is the base change `X ↦ X ×_{k₀} k̄` from the
bounded constructible formalism over a field `k₀` to the one over an algebraic closure `k̄`:
the pullbacks `π_X^*` have no adjoints on bounded constructible complexes, so this situation is
*not* an exchange formalism on a bigger index category, but all the formal base change maps of
the theory still make sense:

- `Θ.shBaseChange j : (Φ j)_! π^* ⟶ π^* j_!` for an open immersion `j`, the mate of `Θ.pbIso j`
  under `j_! ⊣ j^*` and `(Φ j)_! ⊣ (Φ j)^*`;
- `Θ.pfBaseChange f : π^* f_* ⟶ (Φ f)_* π^*`, the mate of `(Θ.pbIso f).inv` under
  `f^* ⊣ f_*` and `(Φ f)^* ⊣ (Φ f)_*`;
- `Θ.shriekBaseChange i p : π^* (p_* i_!) ⟶ ((Φ p)_* (Φ i)_!) π^*`, the compact-support
  exchange map of a factorization `X ⟶[i] Z ⟶[p] Y`, when `Θ.shBaseChange i` is invertible.

The main result, `CategoryTheory.ExchangeFormalism.Morphism.compIso_shriekBaseChange`, is the
compatibility of the compact-support exchange maps with the composition isomorphisms
`CategoryTheory.ExchangeFormalism.compIso` of a triangle of factorizations `T` over `𝒞` and of
its image `T.map Φ` over `𝒞'`. It is the analogue, for a morphism of formalisms, of
`CategoryTheory.ExchangeFormalism.compIso_shriekBaseChange`, and it only inverts the base change
maps `Θ.shBaseChange` of the open immersions of `T` and the exchange maps of the squares of `T`
and `T.map Φ` (all inside `F` and `F'`): no adjoint of `π^*` is ever used.

The pasting laws needed on the way (`Θ.shBaseChange_comp`, `Θ.pfBaseChange_comp`,
`Θ.shBaseChange_cube`, `Θ.exchange_pfBaseChange_cube`) are proved exactly as their
single-formalism counterparts, with the square isomorphism of a square of `𝒞` compared with
the one of its image under `Φ` through `Θ.sqIso_map`.
-/

@[expose] public section

universe w v₁ v u w' v₁' v' u' v₂ v₃ v₄ v₅ u₂ u₃ u₄ u₅

namespace CategoryTheory

open TwoSquare

section Helpers

variable {A : Type u₂} {B : Type u₃} {C : Type u₄} {D : Type u₅}
  [Category.{v₂} A] [Category.{v₃} B] [Category.{v₄} C] [Category.{v₅} D]

/-- The images under a functor of the two components of a natural isomorphism compose to
the identity. -/
@[reassoc (attr := simp)]
lemma Functor.map_hom_inv_id_app_of_iso (G : B ⥤ C) {F₁ F₂ : A ⥤ B} (e : F₁ ≅ F₂) (X : A) :
    G.map (e.hom.app X) ≫ G.map (e.inv.app X) = 𝟙 _ := by
  rw [← G.map_comp, Iso.hom_inv_id_app, G.map_id]

/-- The images under a functor of the two components of a natural isomorphism compose to
the identity. -/
@[reassoc (attr := simp)]
lemma Functor.map_inv_hom_id_app_of_iso (G : B ⥤ C) {F₁ F₂ : A ⥤ B} (e : F₁ ≅ F₂) (X : A) :
    G.map (e.inv.app X) ≫ G.map (e.hom.app X) = 𝟙 _ := by
  rw [← G.map_comp, Iso.inv_hom_id_app, G.map_id]

/-- The mate of a 2-square whiskered at the top is the mate whiskered on the right. -/
lemma mateEquiv_whiskerTop {G G' : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A}
    {L₂ : C ⥤ D} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (w : TwoSquare G L₁ L₂ H)
    (σ : G' ⟶ G) :
    mateEquiv adj₁ adj₂ (w.whiskerTop σ) = (mateEquiv adj₁ adj₂ w).whiskerRight σ := by
  ext d
  simp only [mateEquiv_apply, TwoSquare.whiskerTop, TwoSquare.whiskerRight, NatTrans.comp_app,
    Functor.comp_obj, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp,
    Category.assoc, Functor.rightUnitor_inv_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.comp_map, Category.id_comp,
    Category.comp_id, Functor.id_obj]
  rw [Adjunction.unit_naturality_assoc]

end Helpers

namespace ExchangeFormalism

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  {𝒞' : Type u'} [Category.{v'} 𝒞'] {𝒪' : MorphismProperty 𝒞'}

/-- A commutative square is sent to a commutative square by a functor. -/
lemma map_square (Φ : 𝒞 ⥤ 𝒞') {U' U Z' Z : 𝒞} {t : U' ⟶ U} {l : U' ⟶ Z'} {r : U ⟶ Z}
    {b : Z' ⟶ Z} (w : t ≫ r = l ≫ b) : Φ.map t ≫ Φ.map r = Φ.map l ≫ Φ.map b := by
  rw [← Φ.map_comp, w, Φ.map_comp]

namespace ShriekTriangle

variable (Φ : 𝒞 ⥤ 𝒞') {X Y S : 𝒞} (T : ShriekTriangle 𝒪 X Y S)

/-- **The image of a triangle of factorizations** under a functor `Φ` of the index categories
sending the open immersions of `T` into `𝒪'`. -/
abbrev map [Fact (𝒪' (Φ.map T.i₁))] [Fact (𝒪' (Φ.map T.i₂))] [Fact (𝒪' (Φ.map T.i))]
    [Fact (𝒪' (Φ.map T.q))] : ShriekTriangle 𝒪' (Φ.obj X) (Φ.obj Y) (Φ.obj S) where
  Z₁ := Φ.obj T.Z₁
  Z₂ := Φ.obj T.Z₂
  W := Φ.obj T.W
  i₁ := Φ.map T.i₁
  p₁ := Φ.map T.p₁
  i₂ := Φ.map T.i₂
  p₂ := Φ.map T.p₂
  i := Φ.map T.i
  p := Φ.map T.p
  q := Φ.map T.q
  r := Φ.map T.r
  i_q := by rw [← Φ.map_comp, T.i_q]
  r_p := by rw [← Φ.map_comp, T.r_p]
  w := map_square Φ T.w

variable [Fact (𝒪' (Φ.map T.i₁))] [Fact (𝒪' (Φ.map T.i₂))] [Fact (𝒪' (Φ.map T.i))]
  [Fact (𝒪' (Φ.map T.q))]

@[simp] lemma map_Z₁ : (T.map Φ).Z₁ = Φ.obj T.Z₁ := rfl
@[simp] lemma map_Z₂ : (T.map Φ).Z₂ = Φ.obj T.Z₂ := rfl
@[simp] lemma map_W : (T.map Φ).W = Φ.obj T.W := rfl
@[simp] lemma map_i₁ : (T.map Φ).i₁ = Φ.map T.i₁ := rfl
@[simp] lemma map_p₁ : (T.map Φ).p₁ = Φ.map T.p₁ := rfl
@[simp] lemma map_i₂ : (T.map Φ).i₂ = Φ.map T.i₂ := rfl
@[simp] lemma map_p₂ : (T.map Φ).p₂ = Φ.map T.p₂ := rfl
@[simp] lemma map_i : (T.map Φ).i = Φ.map T.i := rfl
@[simp] lemma map_p : (T.map Φ).p = Φ.map T.p := rfl
@[simp] lemma map_q : (T.map Φ).q = Φ.map T.q := rfl
@[simp] lemma map_r : (T.map Φ).r = Φ.map T.r := rfl

end ShriekTriangle

variable (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪) (F' : ExchangeFormalism.{w', v₁'} 𝒞' 𝒪')
  (Φ : 𝒞 ⥤ 𝒞')

/-- **A morphism of exchange formalisms** `F ⟶ F'` along a functor `Φ` of the index categories:
functors `pull X : F.obj X ⥤ F'.obj (Φ.obj X)` (the pullbacks `π_X^*`) with isomorphisms
`f^* ⋙ π_X^* ≅ π_Y^* ⋙ (Φ f)^*` compatible with the composition isomorphisms of the pullbacks.
No adjoint of `pull X` is required. -/
structure Morphism where
  /-- The pullback `π_X^* : F.obj X ⥤ F'.obj (Φ X)`. -/
  pull (X : 𝒞) : F.obj X ⥤ F'.obj (Φ.obj X)
  /-- The isomorphism `π_X^* f^* ≅ (Φ f)^* π_Y^*`. -/
  pbIso {X Y : 𝒞} (f : X ⟶ Y) : F.pb f ⋙ pull X ≅ pull Y ⋙ F'.pb (Φ.map f)
  /-- Compatibility with the composition isomorphisms of the pullbacks. -/
  pbIso_comp {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (M : F.obj Z) :
    (pbIso (f ≫ g)).hom.app M ≫
        (F'.pbComp' (Φ.map f) (Φ.map g) (Φ.map (f ≫ g)) (Φ.map_comp f g).symm).hom.app
          ((pull Z).obj M) =
      (pull X).map ((F.pbComp f g).hom.app M) ≫ (pbIso f).hom.app ((F.pb g).obj M) ≫
        (F'.pb (Φ.map f)).map ((pbIso g).hom.app M)

namespace Morphism

variable {F F' Φ} (Θ : Morphism F F' Φ)

section Pullback

variable {X Y Z : 𝒞}

/-- `Morphism.pbIso_comp` for a composite `f ≫ g = h`. -/
@[reassoc]
lemma pbIso_comp' (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h) (M : F.obj Z) :
    (Θ.pbIso h).hom.app M ≫
        (F'.pbComp' (Φ.map f) (Φ.map g) (Φ.map h) (by rw [← hfg, Φ.map_comp])).hom.app
          ((Θ.pull Z).obj M) =
      (Θ.pull X).map ((F.pbComp' f g h hfg).hom.app M) ≫
        (Θ.pbIso f).hom.app ((F.pb g).obj M) ≫
        (F'.pb (Φ.map f)).map ((Θ.pbIso g).hom.app M) := by
  subst hfg
  simpa using Θ.pbIso_comp f g M

/-- The component of `Θ.pbIso h` for `f ≫ g = h`, through the composition isomorphisms. -/
lemma pbIso_hom_app_comp' (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)
    (M : F.obj Z) :
    (Θ.pbIso h).hom.app M =
      (Θ.pull X).map ((F.pbComp' f g h hfg).hom.app M) ≫
        (Θ.pbIso f).hom.app ((F.pb g).obj M) ≫
        (F'.pb (Φ.map f)).map ((Θ.pbIso g).hom.app M) ≫
        (F'.pbComp' (Φ.map f) (Φ.map g) (Φ.map h) (by rw [← hfg, Φ.map_comp])).inv.app
          ((Θ.pull Z).obj M) := by
  rw [← Θ.pbIso_comp'_assoc f g h hfg M]
  simp

/-- The inverse of `Θ.pbIso h` for `f ≫ g = h`, as a vertical pasting of 2-squares. -/
lemma pbIso_inv_comp' (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h) :
    (Θ.pbIso h).inv =
      ((TwoSquare.mk _ _ _ _ (Θ.pbIso g).inv ≫ᵥ TwoSquare.mk _ _ _ _ (Θ.pbIso f).inv).whiskerLeft
        (F.pbComp' f g h hfg).inv).whiskerRight
          (F'.pbComp' (Φ.map f) (Φ.map g) (Φ.map h) (by rw [← hfg, Φ.map_comp])).hom := by
  apply Iso.inv_ext
  ext M
  rw [NatTrans.comp_app, Θ.pbIso_hom_app_comp' f g h hfg M]
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc, NatTrans.id_app,
    Functor.comp_obj]
  rw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]

end Pullback

section Square

variable {U' U Z' Z : 𝒞}

/-- **The square isomorphisms and `Φ`**: the square isomorphism of a commutative square of `𝒞`
and the one of its image under `Φ` are intertwined by the isomorphisms `Θ.pbIso`. -/
@[reassoc]
lemma sqIso_map (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z) (w : t ≫ r = l ≫ b)
    (M : F.obj Z) :
    (Θ.pull U').map ((F.sqIso t l r b w).hom.app M) ≫
        (Θ.pbIso l).hom.app ((F.pb b).obj M) ≫
        (F'.pb (Φ.map l)).map ((Θ.pbIso b).hom.app M) =
      (Θ.pbIso t).hom.app ((F.pb r).obj M) ≫
        (F'.pb (Φ.map t)).map ((Θ.pbIso r).hom.app M) ≫
        (F'.sqIso (Φ.map t) (Φ.map l) (Φ.map r) (Φ.map b) (map_square Φ w)).hom.app
          ((Θ.pull Z).obj M) := by
  have e₁ := Θ.pbIso_comp' t r (t ≫ r) rfl M
  have e₂ := Θ.pbIso_comp' l b (t ≫ r) w.symm M
  rw [pbComp'_rfl] at e₁
  rw [F'.sqIso_eq (Φ.map t) (Φ.map l) (Φ.map r) (Φ.map b) (map_square Φ w) (Φ.map (t ≫ r))
    (Φ.map_comp t r).symm (by rw [← Φ.map_comp, w])]
  simp only [sqIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc, pbComp'_rfl]
  rw [← e₂, ← cancel_epi ((Θ.pull U').map ((F.pbComp t r).hom.app M)), ← reassoc_of% e₁]
  simp

end Square

section BaseChange

variable {X Y Z : 𝒞}

/-- **The base change map of the extension by zero along `Θ`**: for an open immersion `j`,
the map `π_X^* ⋙ (Φ j)_! ⟶ j_! ⋙ π_Y^*`, i.e. `(Φ j)_! π^* ⟶ π^* j_!`, the mate of `Θ.pbIso j`
under the adjunctions `j_! ⊣ j^*` and `(Φ j)_! ⊣ (Φ j)^*`. -/
def shBaseChange (j : X ⟶ Y) [Fact (𝒪 j)] [Fact (𝒪' (Φ.map j))] :
    TwoSquare (Θ.pull X) (F.sh j) (F'.sh (Φ.map j)) (Θ.pull Y) :=
  (mateEquiv (F.shAdj j) (F'.shAdj (Φ.map j))).symm (Θ.pbIso j).hom

/-- **The base change map of the pushforwards along `Θ`**: the map
`f_* ⋙ π_Y^* ⟶ π_X^* ⋙ (Φ f)_*`, i.e. `π^* f_* ⟶ (Φ f)_* π^*`, the mate of the inverse of
`Θ.pbIso f` under the adjunctions `f^* ⊣ f_*` and `(Φ f)^* ⊣ (Φ f)_*`. -/
def pfBaseChange (f : X ⟶ Y) :
    TwoSquare (F.pf f) (Θ.pull X) (Θ.pull Y) (F'.pf (Φ.map f)) :=
  mateEquiv (F.adj f) (F'.adj (Φ.map f)) (Θ.pbIso f).inv

/-- **Vertical pasting of the base change maps of the extensions by zero**: for open
immersions `j₁ ≫ j₂ = j`. -/
lemma shBaseChange_comp (j₁ : X ⟶ Y) (j₂ : Y ⟶ Z) (j : X ⟶ Z) [Fact (𝒪 j₁)] [Fact (𝒪 j₂)]
    [Fact (𝒪 j)] [Fact (𝒪' (Φ.map j₁))] [Fact (𝒪' (Φ.map j₂))] [Fact (𝒪' (Φ.map j))]
    (hj : j₁ ≫ j₂ = j) :
    Θ.shBaseChange j =
      ((Θ.shBaseChange j₁ ≫ᵥ Θ.shBaseChange j₂).whiskerLeft
        (F.shComp' j₁ j₂ j hj).inv).whiskerRight
          (F'.shComp' (Φ.map j₁) (Φ.map j₂) (Φ.map j) (by rw [← Φ.map_comp, hj])).hom := by
  apply (mateEquiv (F.shAdj j) (F'.shAdj (Φ.map j))).injective
  rw [mateEquiv_conjugateEquiv_vcomp _ ((F'.shAdj (Φ.map j₁)).comp (F'.shAdj (Φ.map j₂))),
    conjugateEquiv_mateEquiv_vcomp _ ((F.shAdj j₁).comp (F.shAdj j₂)), mateEquiv_hcomp]
  have hr' : conjugateEquiv (F.shAdj j) ((F.shAdj j₁).comp (F.shAdj j₂))
      (F.shComp' j₁ j₂ j hj).inv = (F.pbComp' j₁ j₂ j hj).hom := by
    simp [shComp', conjugateIsoEquiv]
  have hl' : conjugateEquiv ((F'.shAdj (Φ.map j₁)).comp (F'.shAdj (Φ.map j₂)))
      (F'.shAdj (Φ.map j))
      (F'.shComp' (Φ.map j₁) (Φ.map j₂) (Φ.map j) (by rw [← Φ.map_comp, hj])).hom =
      (F'.pbComp' (Φ.map j₁) (Φ.map j₂) (Φ.map j) (by rw [← Φ.map_comp, hj])).inv := by
    simp [shComp', conjugateIsoEquiv]
  rw [hr', hl']
  simp only [Morphism.shBaseChange, Equiv.apply_symm_apply]
  ext M
  simp [Θ.pbIso_hom_app_comp' j₁ j₂ j hj M]

/-- **Vertical pasting of the base change maps of the pushforwards**: for `f ≫ g = h`. -/
lemma pfBaseChange_comp (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h) :
    Θ.pfBaseChange h =
      ((Θ.pfBaseChange f ≫ₕ Θ.pfBaseChange g).whiskerTop
        (F.pfComp' f g h hfg).hom).whiskerBottom
          (F'.pfComp' (Φ.map f) (Φ.map g) (Φ.map h) (by rw [← hfg, Φ.map_comp])).inv := by
  have hP : conjugateEquiv (F.adj h) ((F.adj g).comp (F.adj f)) (F.pbComp' f g h hfg).inv =
      (F.pfComp' f g h hfg).hom := rfl
  have hP' : conjugateEquiv ((F'.adj (Φ.map g)).comp (F'.adj (Φ.map f))) (F'.adj (Φ.map h))
      (F'.pbComp' (Φ.map f) (Φ.map g) (Φ.map h) (by rw [← hfg, Φ.map_comp])).hom =
      (F'.pfComp' (Φ.map f) (Φ.map g) (Φ.map h) (by rw [← hfg, Φ.map_comp])).inv := rfl
  rw [Morphism.pfBaseChange, Θ.pbIso_inv_comp' f g h hfg,
    mateEquiv_conjugateEquiv_vcomp _ ((F'.adj (Φ.map g)).comp (F'.adj (Φ.map f))),
    conjugateEquiv_mateEquiv_vcomp _ ((F.adj g).comp (F.adj f)), mateEquiv_hcomp, hP, hP']
  rfl

/-- The base change map of the pushforwards, transposed along `(Φ f)^* ⊣ (Φ f)_*`. -/
@[reassoc]
lemma pfBaseChange_counit (f : X ⟶ Y) (M : F.obj X) :
    (F'.pb (Φ.map f)).map ((Θ.pfBaseChange f).natTrans.app M) ≫
        (F'.adj (Φ.map f)).counit.app ((Θ.pull X).obj M) =
      (Θ.pbIso f).inv.app ((F.pf f).obj M) ≫ (Θ.pull X).map ((F.adj f).counit.app M) :=
  mateEquiv_counit (F.adj f) (F'.adj (Φ.map f)) _ M

end BaseChange

section Cube

variable {U' U Z' Z : 𝒞}

/-- **The base change maps of the extensions by zero on a square and its image**, as an
equality of 2-squares: pasting the base change map of a square `t ≫ r = l ≫ b` of `𝒞` with
`Θ.shBaseChange l` agrees with pasting `Θ.shBaseChange r` with the base change map of the
image square under `Φ`, through `Θ.pbIso t` and `Θ.pbIso b`. -/
lemma shBaseChange_cube_twoSquare (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z)
    [Fact (𝒪 l)] [Fact (𝒪 r)] [Fact (𝒪' (Φ.map l))] [Fact (𝒪' (Φ.map r))]
    (w : t ≫ r = l ≫ b) :
    (F.baseChange t l r b w ≫ₕ Θ.shBaseChange l).whiskerBottom (Θ.pbIso b).hom =
      (Θ.shBaseChange r ≫ₕ
        F'.baseChange (Φ.map t) (Φ.map l) (Φ.map r) (Φ.map b) (map_square Φ w)).whiskerTop
          (Θ.pbIso t).hom := by
  apply (mateEquiv (F.shAdj r) (F'.shAdj (Φ.map l))).injective
  rw [mateEquiv_whiskerBottom, mateEquiv_whiskerTop, mateEquiv_vcomp _ (F.shAdj l),
    mateEquiv_vcomp _ (F'.shAdj (Φ.map r))]
  simp only [baseChange, Morphism.shBaseChange, Equiv.apply_symm_apply]
  ext M
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc,
    Functor.comp_obj]
  exact Θ.sqIso_map t l r b w M

/-- **The base change maps of the extensions by zero on a square and its image**, in
components. -/
lemma shBaseChange_cube (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z)
    [Fact (𝒪 l)] [Fact (𝒪 r)] [Fact (𝒪' (Φ.map l))] [Fact (𝒪' (Φ.map r))]
    (w : t ≫ r = l ≫ b) (M : F.obj U) :
    (F'.sh (Φ.map l)).map ((Θ.pbIso t).inv.app M) ≫
        (Θ.shBaseChange l).natTrans.app ((F.pb t).obj M) ≫
        (Θ.pull Z').map ((F.baseChange t l r b w).natTrans.app M) ≫
        (Θ.pbIso b).hom.app ((F.sh r).obj M) =
      (F'.baseChange (Φ.map t) (Φ.map l) (Φ.map r) (Φ.map b) (map_square Φ w)).natTrans.app
          ((Θ.pull U).obj M) ≫
        (F'.pb (Φ.map b)).map ((Θ.shBaseChange r).natTrans.app M) := by
  have h := congr_app (Θ.shBaseChange_cube_twoSquare t l r b w) M
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Functor.comp_obj,
    Category.assoc] at h
  rw [h]
  simp

/-- **The exchange maps and the base change maps of the pushforwards along `Θ`.** For a
commutative square `t ≫ r = l ≫ b` of `𝒞` with `l`, `r` open immersions, the exchange maps of
the square and of its image under `Φ` are intertwined by `Θ.pfBaseChange t`, `Θ.pfBaseChange b`,
`Θ.shBaseChange l` and `Θ.shBaseChange r`. -/
lemma exchange_pfBaseChange_cube (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z)
    [Fact (𝒪 l)] [Fact (𝒪 r)] [Fact (𝒪' (Φ.map l))] [Fact (𝒪' (Φ.map r))]
    (w : t ≫ r = l ≫ b) [IsIso (F.baseChange t l r b w).natTrans]
    [IsIso (F'.baseChange (Φ.map t) (Φ.map l) (Φ.map r) (Φ.map b) (map_square Φ w)).natTrans]
    [IsIso (Θ.shBaseChange r).natTrans] (N : F.obj U') :
    inv ((Θ.shBaseChange r).natTrans.app ((F.pf t).obj N)) ≫
        (F'.sh (Φ.map r)).map ((Θ.pfBaseChange t).natTrans.app N) ≫
        (F'.exchange (Φ.map t) (Φ.map l) (Φ.map r) (Φ.map b) (map_square Φ w)).natTrans.app
          ((Θ.pull U').obj N) ≫
        (F'.pf (Φ.map b)).map ((Θ.shBaseChange l).natTrans.app N) =
      (Θ.pull Z).map ((F.exchange t l r b w).natTrans.app N) ≫
        (Θ.pfBaseChange b).natTrans.app ((F.sh l).obj N) := by
  -- the cube relation for the base change maps of the extension by zero, with inverses
  have hc := Θ.shBaseChange_cube t l r b w ((F.pf t).obj N)
  have hc' : (F'.sh (Φ.map l)).map ((Θ.pbIso t).inv.app ((F.pf t).obj N)) ≫
      (Θ.shBaseChange l).natTrans.app ((F.pb t).obj ((F.pf t).obj N)) =
      (F'.baseChange (Φ.map t) (Φ.map l) (Φ.map r) (Φ.map b) (map_square Φ w)).natTrans.app
          ((Θ.pull U).obj ((F.pf t).obj N)) ≫
        (F'.pb (Φ.map b)).map ((Θ.shBaseChange r).natTrans.app ((F.pf t).obj N)) ≫
        (Θ.pbIso b).inv.app ((F.sh r).obj ((F.pf t).obj N)) ≫
        (Θ.pull Z').map (inv ((F.baseChange t l r b w).natTrans.app ((F.pf t).obj N))) := by
    rw [← reassoc_of% hc]
    simp
  have hΞ : (F'.pb (Φ.map b)).map (inv ((Θ.shBaseChange r).natTrans.app ((F.pf t).obj N))) ≫
      inv ((F'.baseChange (Φ.map t) (Φ.map l) (Φ.map r) (Φ.map b)
        (map_square Φ w)).natTrans.app ((Θ.pull U).obj ((F.pf t).obj N))) ≫
      (F'.sh (Φ.map l)).map ((Θ.pbIso t).inv.app ((F.pf t).obj N)) ≫
      (Θ.shBaseChange l).natTrans.app ((F.pb t).obj ((F.pf t).obj N)) =
      (Θ.pbIso b).inv.app ((F.sh r).obj ((F.pf t).obj N)) ≫
        (Θ.pull Z').map (inv ((F.baseChange t l r b w).natTrans.app ((F.pf t).obj N))) := by
    rw [hc']
    simp
  -- transpose along `(Φ b)^* ⊣ (Φ b)_*`
  apply ((F'.adj (Φ.map b)).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hβ' := (inv (F'.baseChange (Φ.map t) (Φ.map l) (Φ.map r) (Φ.map b)
    (map_square Φ w)).natTrans).naturality ((Θ.pfBaseChange t).natTrans.app N)
  have hγ := (Θ.shBaseChange l).natTrans.naturality ((F.adj t).counit.app N)
  have hs := (Θ.pbIso b).inv.naturality ((F.exchange t l r b w).natTrans.app N)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, NatIso.isIso_inv_app]
    at hβ' hγ hs
  erw [(F'.adj (Φ.map b)).counit_naturality]
  rw [F'.exchange_counit_assoc (Φ.map t) (Φ.map l) (Φ.map r) (Φ.map b) (map_square Φ w),
    reassoc_of% hβ', ← Functor.map_comp_assoc (F'.sh (Φ.map l)), Θ.pfBaseChange_counit t,
    Functor.map_comp, Category.assoc, hγ]
  erw [Θ.pfBaseChange_counit b]
  rw [reassoc_of% hs, ← Functor.map_comp (Θ.pull Z'), F.exchange_counit t l r b w,
    Functor.map_comp, reassoc_of% hΞ]

end Cube

section Shriek

variable {X Y Z : 𝒞}

/-- **The compact-support exchange map along `Θ`**: for a factorization `X ⟶[i] Z ⟶[p] Y` with
`i` open and `Θ.shBaseChange i` invertible, the map `π_Y^* (p_* i_!) ⟶ ((Φ p)_* (Φ i)_!) π_X^*`,
the horizontal composite of the inverse of `Θ.shBaseChange i` with `Θ.pfBaseChange p`. -/
noncomputable def shriekBaseChange (i : X ⟶ Z) (p : Z ⟶ Y) [Fact (𝒪 i)] [Fact (𝒪' (Φ.map i))]
    [IsIso (Θ.shBaseChange i).natTrans] :
    TwoSquare (F.shriek i p) (Θ.pull X) (Θ.pull Y) (F'.shriek (Φ.map i) (Φ.map p)) :=
  TwoSquare.mk _ _ _ _ (inv (Θ.shBaseChange i).natTrans) ≫ₕ Θ.pfBaseChange p

lemma shriekBaseChange_app (i : X ⟶ Z) (p : Z ⟶ Y) [Fact (𝒪 i)] [Fact (𝒪' (Φ.map i))]
    [IsIso (Θ.shBaseChange i).natTrans] (K : F.obj X) :
    (Θ.shriekBaseChange i p).natTrans.app K =
      (Θ.pfBaseChange p).natTrans.app ((F.sh i).obj K) ≫
        (F'.pf (Φ.map p)).map (inv ((Θ.shBaseChange i).natTrans.app K)) := by
  simp [Morphism.shriekBaseChange, shriek]

end Shriek

section Composition

variable {X Y S : 𝒞}

/-- **The compact-support exchange maps along `Θ` and the composition isomorphisms.** For a
triangle of factorizations `T` of `X ⟶ Y ⟶ S` whose open immersions are sent into `𝒪'` by `Φ`,
with the base change maps `Θ.shBaseChange` of these open immersions invertible and the
exchange maps of the squares of `T` and `T.map Φ` invertible, the exchange map of the composite
is the horizontal composite of the exchange maps, through the composition isomorphisms of `T`
and `T.map Φ`. -/
theorem compIso_shriekBaseChange (T : ShriekTriangle 𝒪 X Y S)
    [Fact (𝒪' (Φ.map T.i₁))] [Fact (𝒪' (Φ.map T.i₂))] [Fact (𝒪' (Φ.map T.i))]
    [Fact (𝒪' (Φ.map T.q))]
    [IsIso (F.baseChange T.p₁ T.q T.i₂ T.r T.w).natTrans]
    [IsIso (F.exchange T.p₁ T.q T.i₂ T.r T.w).natTrans]
    [IsIso (F'.baseChange (Φ.map T.p₁) (Φ.map T.q) (Φ.map T.i₂) (Φ.map T.r)
      (map_square Φ T.w)).natTrans]
    [IsIso (F'.exchange (Φ.map T.p₁) (Φ.map T.q) (Φ.map T.i₂) (Φ.map T.r)
      (map_square Φ T.w)).natTrans]
    [IsIso (Θ.shBaseChange T.i₁).natTrans] [IsIso (Θ.shBaseChange T.i₂).natTrans]
    [IsIso (Θ.shBaseChange T.i).natTrans] [IsIso (Θ.shBaseChange T.q).natTrans] :
    Functor.whiskerRight (F.compIso T).hom (Θ.pull S) ≫
        (Θ.shriekBaseChange T.i T.p).natTrans =
      (Θ.shriekBaseChange T.i₁ T.p₁ ≫ₕ Θ.shriekBaseChange T.i₂ T.p₂).natTrans ≫
        Functor.whiskerLeft (Θ.pull X) (F'.compIso (T.map Φ)).hom := by
  ext K
  -- the base change map of the extension by zero along `i = i₁ ≫ q`
  have hbc := congr_app (Θ.shBaseChange_comp T.i₁ T.q T.i T.i_q) K
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Functor.comp_obj, Category.assoc] at hbc
  have hA : (Θ.pull T.W).map ((F.shComp' T.i₁ T.q T.i T.i_q).inv.app K) ≫
      inv ((Θ.shBaseChange T.i).natTrans.app K) =
      inv ((Θ.shBaseChange T.q).natTrans.app ((F.sh T.i₁).obj K)) ≫
        (F'.sh (Φ.map T.q)).map (inv ((Θ.shBaseChange T.i₁).natTrans.app K)) ≫
        (F'.shComp' (Φ.map T.i₁) (Φ.map T.q) (Φ.map T.i) (T.map Φ).i_q).inv.app
          ((Θ.pull X).obj K) := by
    rw [IsIso.comp_inv_eq, hbc]
    simp
  -- the cube relating the exchange maps of `T` and `T.map Φ`
  have hC := Θ.exchange_pfBaseChange_cube T.p₁ T.q T.i₂ T.r T.w ((F.sh T.i₁).obj K)
  have hC' : inv ((Θ.shBaseChange T.i₂).natTrans.app
        ((F.pf T.p₁).obj ((F.sh T.i₁).obj K))) ≫
      (F'.sh (Φ.map T.i₂)).map ((Θ.pfBaseChange T.p₁).natTrans.app ((F.sh T.i₁).obj K)) ≫
      (F'.exchange (Φ.map T.p₁) (Φ.map T.q) (Φ.map T.i₂) (Φ.map T.r)
        (map_square Φ T.w)).natTrans.app ((Θ.pull T.Z₁).obj ((F.sh T.i₁).obj K)) =
      (Θ.pull T.Z₂).map ((F.exchange T.p₁ T.q T.i₂ T.r T.w).natTrans.app
        ((F.sh T.i₁).obj K)) ≫
      (Θ.pfBaseChange T.r).natTrans.app ((F.sh T.q).obj ((F.sh T.i₁).obj K)) ≫
      (F'.pf (Φ.map T.r)).map (inv ((Θ.shBaseChange T.q).natTrans.app
        ((F.sh T.i₁).obj K))) := by
    rw [← reassoc_of% hC]
    simp
  -- the base change map of the pushforwards along `p = r ≫ p₂`
  have hv := congr_app (Θ.pfBaseChange_comp T.r T.p₂ T.p T.r_p) ((F.sh T.i).obj K)
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj] at hv
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    compIso_hom_app, compIso_hom_app]
  simp only [Morphism.shriekBaseChange, TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_obj, NatIso.isIso_inv_app, Functor.map_comp,
    Category.assoc, Functor.associator_hom_app, Functor.associator_inv_app,
    ShriekTriangle.map_i₁, ShriekTriangle.map_p₁, ShriekTriangle.map_i₂, ShriekTriangle.map_p₂,
    ShriekTriangle.map_i, ShriekTriangle.map_p, ShriekTriangle.map_q, ShriekTriangle.map_r]
  dsimp only [shriek, Functor.comp_obj, Functor.id_obj, Functor.comp_map]
  erw [hv]
  simp only [Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc, CategoryTheory.Functor.map_id]
  dsimp only [Functor.comp_obj]
  simp only [Category.id_comp]
  have hcancel : (Θ.pull S).map ((F.pfComp' T.r T.p₂ T.p T.r_p).inv.app
      ((F.sh T.i).obj K)) ≫ (Θ.pull S).map ((F.pfComp' T.r T.p₂ T.p T.r_p).hom.app
      ((F.sh T.i).obj K)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have hn₁ := (Θ.pfBaseChange T.p₂).natTrans.naturality
    ((F.exchange T.p₁ T.q T.i₂ T.r T.w).natTrans.app ((F.sh T.i₁).obj K) ≫
      (F.pf T.r).map ((F.shComp' T.i₁ T.q T.i T.i_q).inv.app K))
  have hn₂ := (F'.pfComp' (Φ.map T.r) (Φ.map T.p₂) (Φ.map T.p) (T.map Φ).r_p).inv.naturality
    (inv ((Θ.shBaseChange T.i).natTrans.app K))
  have hn₃ := congrArg (F'.pf (Φ.map T.p₂)).map ((Θ.pfBaseChange T.r).natTrans.naturality
    ((F.shComp' T.i₁ T.q T.i T.i_q).inv.app K))
  have hn₄ := congrArg (F'.pf (Φ.map T.p₂)).map
    ((F'.exchange (Φ.map T.p₁) (Φ.map T.q) (Φ.map T.i₂) (Φ.map T.r)
      (map_square Φ T.w)).natTrans.naturality
      (inv ((Θ.shBaseChange T.i₁).natTrans.app K)))
  have hA' := congrArg (fun φ ↦ (F'.pf (Φ.map T.p₂)).map ((F'.pf (Φ.map T.r)).map φ)) hA
  have hC'' := congrArg (F'.pf (Φ.map T.p₂)).map hC'
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc]
    at hn₁ hn₂ hn₃ hn₄ hA' hC''
  rw [reassoc_of% hcancel, reassoc_of% hn₁, ← hn₂, reassoc_of% hn₃, reassoc_of% hA',
    reassoc_of% hn₄, reassoc_of% hC'']

end Composition

end Morphism

end ExchangeFormalism

end CategoryTheory
