/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.EqToHom

/-!
# An abstract formalism for compactly supported direct images

The compactly supported direct image `Rf_! = Rp_* ∘ i_!` attached to a compactification
`X ⟶[i] Z ⟶[p] Y` is assembled from three kinds of functors: pullbacks `f^*`, their right
adjoints `f_*`, and, for open immersions `j`, the left adjoint `j_!` of `j^*`. All the
comparison isomorphisms of the theory (base change for `j_!`, the exchange `j_! g'_* ⟶ g''_* j'_!`,
the comparison along a refinement of compactifications, the composition law of `Rf_!`) are
mates of the composition isomorphisms of the pullbacks. Their coherence is therefore formal.

This file sets up that formal structure, `AlgebraicGeometry.CompactSupportFormalism`: a
category for each scheme, a pullback pseudofunctor `f ↦ f^*`, right adjoints `f_*` and left
adjoints `j_!` of `j^*` for open immersions `j`. It defines

- `pbComp'`, `pfComp'`, `shComp'`: the flexible composition isomorphisms of `f^*`, `f_*`, `j_!`,
  the last two as conjugates of the first;
- `sqIso`: the isomorphism `r^* ⋙ t^* ≅ b^* ⋙ l^*` of a commutative square;
- `baseChange`: the base change map `g'^* ⋙ j'_! ⟶ j_! ⋙ g''^*` for the extension by zero;
- `exchange`: the exchange map `g'_* ⋙ j_! ⟶ j'_! ⋙ g''_*` of a square whose base change map is
  an isomorphism.

The concrete instance, on the bounded below derived categories of étale sheaves, is used to
prove the composition law of blueprint `sk-thm-sf-comp-composition`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace AlgebraicGeometry

set_option linter.checkUnivs false in
/-- **A formalism for compactly supported direct images**: a category `obj X` for each scheme
`X`, a pullback pseudofunctor `f ↦ pb f`, a right adjoint `pf f` of each `pb f`, and a left
adjoint `sh j` of `pb j` for each open immersion `j`. -/
structure CompactSupportFormalism where
  /-- The category attached to a scheme. -/
  obj : Scheme.{u} → Type w
  /-- The categories attached to schemes. -/
  [category (X : Scheme.{u}) : Category.{v} (obj X)]
  /-- The pullback `f^*`. -/
  pb {X Y : Scheme.{u}} (f : X ⟶ Y) : obj Y ⥤ obj X
  /-- The identity isomorphism `(𝟙 X)^* ≅ 𝟭`. -/
  pbId (X : Scheme.{u}) : pb (𝟙 X) ≅ 𝟭 (obj X)
  /-- The composition isomorphism `(f ≫ g)^* ≅ g^* ⋙ f^*`. -/
  pbComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : pb (f ≫ g) ≅ pb g ⋙ pb f
  pbComp_assoc {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : obj W) :
    (pbComp (f ≫ g) h).hom.app M ≫ (pbComp f g).hom.app ((pb h).obj M) =
      eqToHom (by rw [Category.assoc]) ≫ (pbComp f (g ≫ h)).hom.app M ≫
        (pb f).map ((pbComp g h).hom.app M)
  pbId_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (M : obj Y) :
    (pbComp (𝟙 X) f).hom.app M ≫ (pbId X).hom.app ((pb f).obj M) =
      eqToHom (by simp)
  pbComp_id {X Y : Scheme.{u}} (f : X ⟶ Y) (M : obj Y) :
    (pbComp f (𝟙 Y)).hom.app M ≫ (pb f).map ((pbId Y).hom.app M) =
      eqToHom (by simp)
  /-- The pushforward `f_*`. -/
  pf {X Y : Scheme.{u}} (f : X ⟶ Y) : obj X ⥤ obj Y
  /-- The adjunction `f^* ⊣ f_*`. -/
  adj {X Y : Scheme.{u}} (f : X ⟶ Y) : pb f ⊣ pf f
  /-- The extension by zero `j_!` along an open immersion. -/
  sh {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] : obj X ⥤ obj Y
  /-- The adjunction `j_! ⊣ j^*`. -/
  shAdj {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] : sh j ⊣ pb j

namespace CompactSupportFormalism

attribute [instance] category

variable (F : CompactSupportFormalism.{w, v, u})

section Pullback

variable {X Y Z W : Scheme.{u}}

/-- The composition isomorphism `h^* ≅ g^* ⋙ f^*` for `f ≫ g = h`. -/
def pbComp' (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    F.pb h ≅ F.pb g ⋙ F.pb f :=
  eqToIso (by rw [w]) ≪≫ F.pbComp f g

@[simp]
lemma pbComp'_rfl (f : X ⟶ Y) (g : Y ⟶ Z) : F.pbComp' f g (f ≫ g) rfl = F.pbComp f g := by
  ext; simp [pbComp']

/-- The isomorphism `f^* ≅ g^*` for `f = g`. -/
def pbCongr {f g : X ⟶ Y} (h : f = g) : F.pb f ≅ F.pb g := eqToIso (by rw [h])

@[simp]
lemma pbCongr_rfl (f : X ⟶ Y) : F.pbCongr (rfl : f = f) = Iso.refl _ := rfl

@[reassoc]
lemma pbComp'_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (fg : X ⟶ Z) (gh : Y ⟶ W)
    (fgh : X ⟶ W) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfgh : fg ≫ h = fgh)
    (M : F.obj W) :
    (F.pbComp' fg h fgh hfgh).hom.app M ≫ (F.pbComp' f g fg hfg).hom.app ((F.pb h).obj M) =
      (F.pbComp' f gh fgh (by rw [← hfgh, ← hfg, ← hgh, Category.assoc])).hom.app M ≫
        (F.pb f).map ((F.pbComp' g h gh hgh).hom.app M) := by
  subst hfg hgh hfgh
  rw [pbComp'_rfl, pbComp'_rfl, pbComp'_rfl, F.pbComp_assoc]
  simp [pbComp']

@[reassoc]
lemma pbComp'_id_left (f : X ⟶ Y) (f' : X ⟶ Y) (hf : 𝟙 X ≫ f = f') (M : F.obj Y) :
    (F.pbComp' (𝟙 X) f f' hf).hom.app M ≫ (F.pbId X).hom.app ((F.pb f).obj M) =
      eqToHom (by rw [← hf, Category.id_comp]; rfl) := by
  subst hf
  simpa using F.pbId_comp f M

@[reassoc]
lemma pbComp'_id_right (f : X ⟶ Y) (f' : X ⟶ Y) (hf : f ≫ 𝟙 Y = f') (M : F.obj Y) :
    (F.pbComp' f (𝟙 Y) f' hf).hom.app M ≫ (F.pb f).map ((F.pbId Y).hom.app M) =
      eqToHom (by rw [← hf, Category.comp_id]; rfl) := by
  subst hf
  simpa using F.pbComp_id f M

end Pullback


section Pushforward

variable {X Y Z W : Scheme.{u}}

/-- The composition isomorphism `h_* ≅ f_* ⋙ g_*` for `f ≫ g = h`, conjugate to
`CompactSupportFormalism.pbComp'`. -/
def pfComp' (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    F.pf h ≅ F.pf f ⋙ F.pf g :=
  conjugateIsoEquiv (F.adj h) ((F.adj g).comp (F.adj f)) (F.pbComp' f g h w).symm

/-- The identity isomorphism `(𝟙 X)_* ≅ 𝟭`, conjugate to `CompactSupportFormalism.pbId`. -/
def pfId (X : Scheme.{u}) : F.pf (𝟙 X) ≅ 𝟭 (F.obj X) :=
  conjugateIsoEquiv (F.adj (𝟙 X)) Adjunction.id (F.pbId X).symm

end Pushforward

section ExtensionByZero

variable {X Y Z : Scheme.{u}}

/-- The composition isomorphism `j_! ≅ j₁_! ⋙ j₂_!` for open immersions with `j₁ ≫ j₂ = j`,
conjugate to `CompactSupportFormalism.pbComp'`. -/
def shComp' (j₁ : X ⟶ Y) (j₂ : Y ⟶ Z) (j : X ⟶ Z) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    [IsOpenImmersion j] (w : j₁ ≫ j₂ = j) : F.sh j ≅ F.sh j₁ ⋙ F.sh j₂ :=
  (conjugateIsoEquiv ((F.shAdj j₁).comp (F.shAdj j₂)) (F.shAdj j)).symm (F.pbComp' j₁ j₂ j w).symm

/-- The identity isomorphism `(𝟙 X)_! ≅ 𝟭`, conjugate to `CompactSupportFormalism.pbId`. -/
def shId (X : Scheme.{u}) : F.sh (𝟙 X) ≅ 𝟭 (F.obj X) :=
  (conjugateIsoEquiv Adjunction.id (F.shAdj (𝟙 X))).symm (F.pbId X).symm

end ExtensionByZero

section Square

variable {U' U Z' Z : Scheme.{u}}

/-- The isomorphism `r^* ⋙ t^* ≅ b^* ⋙ l^*` attached to a commutative square `t ≫ r = l ≫ b`. -/
def sqIso (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z) (w : t ≫ r = l ≫ b) :
    F.pb r ⋙ F.pb t ≅ F.pb b ⋙ F.pb l :=
  (F.pbComp' t r (t ≫ r) rfl).symm ≪≫ F.pbComp' l b (t ≫ r) w.symm

/-- **The base change map of the extension by zero**: for a commutative square
`t ≫ r = l ≫ b` with `l` and `r` open immersions, the map `t^* ⋙ l_! ⟶ r_! ⋙ b^*`, i.e.
`l_! t^* ⟶ b^* r_!`, the mate of `CompactSupportFormalism.sqIso` under the adjunctions
`r_! ⊣ r^*` and `l_! ⊣ l^*`.
```
U' --t--> U
|l        |r
Z' --b--> Z
```
-/
def baseChange (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z) [IsOpenImmersion l]
    [IsOpenImmersion r] (w : t ≫ r = l ≫ b) :
    TwoSquare (F.pb t) (F.sh r) (F.sh l) (F.pb b) :=
  (mateEquiv (F.shAdj r) (F.shAdj l)).symm (F.sqIso t l r b w).hom

/-- **The exchange map of an extension by zero and a pushforward**: for a commutative square
`t ≫ r = l ≫ b` with `l` and `r` open immersions whose base change map is an isomorphism, the
map `t_* ⋙ r_! ⟶ l_! ⋙ b_*`, i.e. `r_! t_* ⟶ b_* l_!`, the mate of the inverse of
`CompactSupportFormalism.baseChange` under the adjunctions `t^* ⊣ t_*` and `b^* ⊣ b_*`.
-/
noncomputable def exchange (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z) [IsOpenImmersion l]
    [IsOpenImmersion r] (w : t ≫ r = l ≫ b) [IsIso (F.baseChange t l r b w).natTrans] :
    TwoSquare (F.pf t) (F.sh l) (F.sh r) (F.pf b) :=
  mateEquiv (F.adj t) (F.adj b) (inv (F.baseChange t l r b w).natTrans)

end Square

/-- Base change for the extension by zero: the base change map of a cartesian square is an
isomorphism. -/
class HasBaseChange : Prop where
  isIso_baseChange {U' U Z' Z : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'} {r : U ⟶ Z}
    {b : Z' ⟶ Z} [IsOpenImmersion l] [IsOpenImmersion r] (h : IsPullback t l r b) :
    IsIso (F.baseChange t l r b h.w).natTrans

/-- Proper base change in the form needed for compactly supported direct images: the exchange
map of a cartesian square whose bottom map is proper is an isomorphism. -/
class HasProperExchange extends F.HasBaseChange where
  isIso_exchange {U' U Z' Z : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'} {r : U ⟶ Z}
    {b : Z' ⟶ Z} [IsOpenImmersion l] [IsOpenImmersion r] [IsProper b] (h : IsPullback t l r b) :
    haveI := isIso_baseChange h
    IsIso (F.exchange t l r b h.w).natTrans

end CompactSupportFormalism

end AlgebraicGeometry
