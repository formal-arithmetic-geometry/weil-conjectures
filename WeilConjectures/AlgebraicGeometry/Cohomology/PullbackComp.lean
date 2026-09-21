/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Pullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback

/-!
# The pullback map on the cohomology of an abelian sheaf, and its composition law

For a morphism of schemes `f : Z ⟶ X` and an abelian sheaf `𝒢` on `X`, this file constructs the
pullback map

`H^n(X, 𝒢) ⟶ H^n(Z, f^{-1} 𝒢)`

on sheaf cohomology and proves that it is compatible with the composition of morphisms of
schemes, and then transports that composition law to the pullback map
`H^n(Y, G) ⟶ H^n(X, f^* G)` on the cohomology of a sheaf of *modules*. The abelian-sheaf map is
the shadow of `AlgebraicGeometry.Scheme.Modules.H.pullbackAddHom`, from which the latter is
obtained by composing with the comparison map
`AlgebraicGeometry.Scheme.Modules.pullbackAbComparison`.

Because the pullback of abelian sheaves is only defined as *a* left adjoint of the pushforward,
the pullback along a composite `a ≫ b` is not the composite of the pullbacks, but only
canonically isomorphic to it; the isomorphism is
`AlgebraicGeometry.Scheme.Hom.pullbackAbComp`, the specialisation to `Opens.map` of the
site-theoretic `CategoryTheory.Functor.sheafPullbackComp`, and the composition law is stated
modulo it.

Nothing in the constructions of this file is particular to schemes; everything site-theoretic
lives in the mirror files `WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback` and
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf`, and this file only specialises
those results to `Opens.map f.base` and assembles them into the pullback map on cohomology.

## Main definitions and results

* `AlgebraicGeometry.Scheme.Hom.pullbackAbComp` — the canonical isomorphism
  `(a ≫ b)^{-1} ≅ b^{-1} ⋙ a^{-1}` of pullback functors on abelian sheaves.
* `AlgebraicGeometry.Scheme.Hom.H.pullbackAddHom` — the pullback map on the cohomology of an
  abelian sheaf.
* `AlgebraicGeometry.Scheme.Hom.H.pullbackAddHom_comp` — **the composition law**: pulling back
  along `b` and then along `a` is pulling back along `a ≫ b`, modulo `pullbackAbComp`.
* `AlgebraicGeometry.Scheme.Modules.pullbackAbComparison_comp` — the comparison map between the
  two notions of pullback is compatible with the composition of morphisms of schemes.
* `AlgebraicGeometry.Scheme.Modules.H.pullbackAddHom_comp` — **the composition law for the
  pullback map on the cohomology of a sheaf of modules**, obtained from the two previous
  results, modulo the canonical isomorphism `AlgebraicGeometry.Scheme.Modules.pullbackComp`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace Abelian

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y Z : Scheme.{u}}

/-! ### The pullback of abelian sheaves along a composite -/

/-- `Opens.map (a ≫ b).base` is the composite `Opens.map b.base ⋙ Opens.map a.base`, but only
up to unfolding, so the continuity of the composite has to be supplied by hand. -/
lemma isContinuous_opensMap_comp (a : Z ⟶ X) (b : X ⟶ Y) :
    (Opens.map b.base ⋙ Opens.map a.base).IsContinuous
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology Z) :=
  Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology X) _

attribute [local instance] isContinuous_opensMap_comp

/-- The pushforward of abelian sheaves along `Opens.map b.base ⋙ Opens.map a.base` is a right
adjoint, being the composite of the two pushforwards. -/
lemma isRightAdjoint_sheafPushforwardContinuous_opensMap_comp (a : Z ⟶ X) (b : X ⟶ Y) :
    ((Opens.map b.base ⋙ Opens.map a.base).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology Z)).IsRightAdjoint :=
  (b.pullbackPushforwardAbAdjunction.comp a.pullbackPushforwardAbAdjunction).isRightAdjoint

attribute [local instance] isRightAdjoint_sheafPushforwardContinuous_opensMap_comp

/-- **The pullback of abelian sheaves along a composite**: the canonical isomorphism
`(a ≫ b)^{-1} ≅ b^{-1} ⋙ a^{-1}`, the specialisation to `Opens.map` of
`CategoryTheory.Functor.sheafPullbackComp`.

```
                     pullbackAbComp
Sheaf Y ------------------------------------> Sheaf Z
   |            (a ≫ b)^{-1}                     ^
   |                                             |
   |   b^{-1}                          a^{-1}    |
   +----------> Sheaf X --------------------------+
```
-/
noncomputable def pullbackAbComp (a : Z ⟶ X) (b : X ⟶ Y) :
    (a ≫ b).pullbackAb ≅ b.pullbackAb ⋙ a.pullbackAb :=
  (Opens.map b.base).sheafPullbackComp (Opens.map a.base) AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Z)

/-- `AlgebraicGeometry.Scheme.Hom.pullbackAbComp` is compatible with the units of the
adjunctions `(a ≫ b)^{-1} ⊣ (a ≫ b)_♭` and `b^{-1} ⊣ b_♭`, `a^{-1} ⊣ a_♭`:

```
                             (a ≫ b)_♭ (pullbackAbComp).hom
𝒢 --unit--> (a ≫ b)_♭ (a ≫ b)^{-1} 𝒢 -----------------------> (a ≫ b)_♭ a^{-1} b^{-1} 𝒢
|                                                                          ^
+----unit----> b_♭ b^{-1} 𝒢 ----------b_♭ unit------------> b_♭ a_♭ a^{-1} b^{-1} 𝒢
```

the two rows landing in the same object because `(a ≫ b)_♭ = a_♭ ⋙ b_♭`
(`AlgebraicGeometry.Scheme.Hom.pushforwardAb_comp_map`). -/
lemma unit_pullbackAbComp_hom_app (a : Z ⟶ X) (b : X ⟶ Y)
    (𝒢 : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) :
    (a ≫ b).pullbackPushforwardAbAdjunction.unit.app 𝒢 ≫
        (a ≫ b).pushforwardAb.map ((pullbackAbComp a b).hom.app 𝒢) =
      b.pullbackPushforwardAbAdjunction.unit.app 𝒢 ≫
        b.pushforwardAb.map
          (a.pullbackPushforwardAbAdjunction.unit.app (b.pullbackAb.obj 𝒢)) :=
  (Opens.map b.base).unit_sheafPullbackComp_hom_app (Opens.map a.base) AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Z) 𝒢

/-- **The identification `f^{-1} ℤ_X ≅ ℤ_Z` of the pullback of a constant sheaf is compatible
with composition**, read backwards:

```
A_Z --((a ≫ b)-iso)⁻¹--> (a ≫ b)^{-1} A_Y
 |                                  ^
 +--(a-iso)⁻¹--> a^{-1} A_X --a^{-1} (b-iso)⁻¹--> a^{-1} b^{-1} A_Y --(pullbackAbComp)⁻¹--+
```

This is the specialisation to `Opens.map` of
`CategoryTheory.Functor.constantSheafsheafPullbackIso_inv_app_comp`. -/
lemma pullbackAbConstantSheafIso_inv_comp (a : Z ⟶ X) (b : X ⟶ Y) (A : AddCommGrpCat.{u}) :
    ((a ≫ b).pullbackAbConstantSheafIso A).inv =
      (a.pullbackAbConstantSheafIso A).inv ≫
        a.pullbackAb.map (b.pullbackAbConstantSheafIso A).inv ≫
          (pullbackAbComp a b).inv.app ((constantSheafAb Y).obj A) :=
  (Opens.map b.base).constantSheafsheafPullbackIso_inv_app_comp (Opens.map a.base)
    AddCommGrpCat.{u} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Z) isTerminalTop isTerminalTop isTerminalTop A

/-! ### The pullback map on the cohomology of an abelian sheaf -/

namespace H

/-- **The pullback map on the cohomology of an abelian sheaf** along a morphism of schemes
`f : Z ⟶ X`: apply the exact functor `f^{-1}` to a class in `Ext^n(ℤ_X, 𝒢)` and precompose with
the identification `ℤ_Z ≅ f^{-1} ℤ_X`.

```
Ext^n(ℤ_X, 𝒢) --mapExactFunctor f^{-1}--> Ext^n(f^{-1} ℤ_X, f^{-1} 𝒢)
              --precompose with (iso)⁻¹--> Ext^n(ℤ_Z, f^{-1} 𝒢)
```
-/
noncomputable def pullbackAddHom (f : Z ⟶ X)
    (𝒢 : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    𝒢.H n →+ (f.pullbackAb.obj 𝒢).H n where
  toFun e := (Ext.mk₀ (f.pullbackAbConstantSheafIso _).inv).comp
    (e.mapExactFunctor f.pullbackAb) (zero_add n)
  map_zero' := by simp
  map_add' e e' := by simp [Ext.comp_add]

@[simp]
lemma pullbackAddHom_apply (f : Z ⟶ X)
    (𝒢 : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) (e : 𝒢.H n) :
    pullbackAddHom f 𝒢 n e = (Ext.mk₀ (f.pullbackAbConstantSheafIso _).inv).comp
      (e.mapExactFunctor f.pullbackAb) (zero_add n) :=
  rfl

/-- The pullback map on cohomology is natural in the abelian sheaf:

```
H^n(X, 𝒢) ----- - ∘ φ ------> H^n(X, 𝒢')
    |                              |
pullbackAddHom             pullbackAddHom
    v                              v
H^n(Z, f^{-1} 𝒢) -- - ∘ f^{-1} φ --> H^n(Z, f^{-1} 𝒢')
```
-/
lemma pullbackAddHom_comp_mk₀ (f : Z ⟶ X)
    {𝒢 𝒢' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (φ : 𝒢 ⟶ 𝒢') (n : ℕ)
    (e : 𝒢.H n) :
    pullbackAddHom f 𝒢' n (e.comp (Ext.mk₀ φ) (add_zero n)) =
      (pullbackAddHom f 𝒢 n e).comp (Ext.mk₀ (f.pullbackAb.map φ)) (add_zero n) := by
  rw [pullbackAddHom_apply, pullbackAddHom_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by lia)]

/-- **The composition law for the pullback map on cohomology**: pulling back along `b` and then
along `a` is pulling back along `a ≫ b`, followed by the identification
`AlgebraicGeometry.Scheme.Hom.pullbackAbComp` of `(a ≫ b)^{-1} 𝒢` with `a^{-1} b^{-1} 𝒢`.

```
H^n(Y, 𝒢) --pullbackAddHom b--> H^n(X, b^{-1} 𝒢) --pullbackAddHom a--> H^n(Z, a^{-1} b^{-1} 𝒢)
    |                                                                          ^
    +----pullbackAddHom (a ≫ b)----> H^n(Z, (a ≫ b)^{-1} 𝒢) --- ∘ pullbackAbComp ----+
```
-/
lemma pullbackAddHom_comp (a : Z ⟶ X) (b : X ⟶ Y)
    (𝒢 : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) (n : ℕ) (e : 𝒢.H n) :
    pullbackAddHom a (b.pullbackAb.obj 𝒢) n (pullbackAddHom b 𝒢 n e) =
      (pullbackAddHom (a ≫ b) 𝒢 n e).comp
        (Ext.mk₀ ((pullbackAbComp a b).hom.app 𝒢)) (add_zero n) := by
  rw [pullbackAddHom_apply, pullbackAddHom_apply, pullbackAddHom_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.mapExactFunctor_comp_functor,
    Ext.mapExactFunctor_natIso (pullbackAbComp a b) e,
    pullbackAbConstantSheafIso_inv_comp a b]
  simp only [Ext.comp_assoc_of_third_deg_zero]
  rw [← Ext.mk₀_comp_mk₀, ← Ext.mk₀_comp_mk₀]
  simp only [Ext.comp_assoc_of_second_deg_zero]

/-- The pullback map on cohomology transported along an equality `c₁ = c₂` of morphisms of
schemes:

```
H^n(Y, 𝒢) --pullbackAddHom c₁--> H^n(Z, c₁^{-1} 𝒢) -- ∘ eqToHom --> H^n(Z, c₂^{-1} 𝒢)
    |                                                                     ^
    +---------------------pullbackAddHom c₂-------------------------------+
```
-/
lemma pullbackAddHom_eqToHom {c₁ c₂ : Z ⟶ Y} (h : c₁ = c₂)
    (𝒢 : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) (n : ℕ) (e : 𝒢.H n) :
    (pullbackAddHom c₁ 𝒢 n e).comp
        (Ext.mk₀ (eqToHom (congrArg (fun m : Z ⟶ Y ↦ m.pullbackAb.obj 𝒢) h))) (add_zero n) =
      pullbackAddHom c₂ 𝒢 n e := by
  subst h
  simp

end H

end Scheme.Hom

namespace Scheme.Modules

variable {X Y Z : Scheme.{u}}

attribute [local instance] Scheme.Hom.isContinuous_opensMap_comp
attribute [local instance] Scheme.Hom.isRightAdjoint_sheafPushforwardContinuous_opensMap_comp

/-! ### The comparison map and composition -/

/-- **The comparison map `f^{-1}(G^♭) ⟶ (f^* G)^♭` is compatible with the composition** of
morphisms of schemes:

```
(a ≫ b)^{-1} (M^♭) --pullbackAbComp--> a^{-1} b^{-1} (M^♭) --a^{-1} comparison--> a^{-1} ((b^* M)^♭)
       |                                                                                  |
  comparison                                                                         comparison
       v                                                                                  v
 ((a ≫ b)^* M)^♭ ------------------- (pullbackComp a b)⁻¹ ---------------> (a^* b^* M)^♭
```
-/
lemma pullbackAbComparison_comp (a : Z ⟶ X) (b : X ⟶ Y) (M : Y.Modules) :
    (a.pullbackAbComp b).hom.app ((toSheafAb Y).obj M) ≫
        a.pullbackAb.map ((pullbackAbComparison b).app M) ≫
          (pullbackAbComparison a).app ((pullback b).obj M) =
      (pullbackAbComparison (a ≫ b)).app M ≫
        (toSheafAb Z).map ((pullbackComp a b).inv.app M) := by
  refine ((a ≫ b).pullbackPushforwardAbAdjunction.homEquiv _ _).injective ?_
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc ((Scheme.Hom.pullbackPushforwardAbAdjunction (a ≫ b)).unit.app _),
    Scheme.Hom.unit_pullbackAbComp_hom_app, Category.assoc,
    Scheme.Hom.pushforwardAb_comp_map, Scheme.Hom.pushforwardAb_comp_map]
  simp only [← Functor.map_comp]
  dsimp only [Functor.comp_obj]
  have hinner : a.pullbackPushforwardAbAdjunction.unit.app
        (b.pullbackAb.obj ((toSheafAb Y).obj M)) ≫
        a.pushforwardAb.map (a.pullbackAb.map ((pullbackAbComparison b).app M) ≫
          (pullbackAbComparison a).app ((pullback b).obj M)) =
      (pullbackAbComparison b).app M ≫ (toSheafAb X).map
        ((pullbackPushforwardAdjunction a).unit.app ((pullback b).obj M)) := by
    have h := a.pullbackPushforwardAbAdjunction.unit.naturality ((pullbackAbComparison b).app M)
    dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at h
    rw [Functor.map_comp, ← Category.assoc, ← h, Category.assoc,
      unit_comp_map_pullbackAbComparison]
  have hid : (pushforwardComp a b).hom.app ((pullback a).obj ((pullback b).obj M)) = 𝟙 _ := by
    ext U
    simp
  have hmod : (pullbackPushforwardAdjunction b).unit.app M ≫
        (pushforward b).map ((pullbackPushforwardAdjunction a).unit.app ((pullback b).obj M)) =
      (pullbackPushforwardAdjunction (a ≫ b)).unit.app M ≫
        (pushforward (a ≫ b)).map ((pullbackComp a b).inv.app M) := by
    have h := unit_pushforwardPullbackComp a b M
    rw [← h, pushforwardPullbackComp]
    simp only [hid, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [hinner, unit_comp_map_pullbackAbComparison_comp,
    unit_comp_map_pullbackAbComparison_comp]
  exact congrArg (toSheafAb Y).map hmod

/-! ### The pullback map on cohomology, through the comparison map -/

/-- **The pullback map on the cohomology of a sheaf of modules factors through the pullback map
on the cohomology of the underlying abelian sheaf**, followed by the comparison map:

```
H^n(Y, G) --Hom.H.pullbackAddHom--> H^n(X, f^{-1}(G^♭)) -- ∘ comparison --> H^n(X, (f^* G)^♭)
    |                                                                             ^
    +---------------------------Modules.H.pullbackAddHom--------------------------+
```
-/
lemma H.pullbackAddHom_eq_comp_pullbackAbComparison (f : X ⟶ Y) (G : Y.Modules) (n : ℕ)
    (e : G.H n) :
    H.pullbackAddHom f G n e =
      (Scheme.Hom.H.pullbackAddHom f ((toSheafAb Y).obj G) n e).comp
        (Ext.mk₀ ((pullbackAbComparison f).app G)) (add_zero n) := by
  simp only [H.pullbackAddHom_apply, Scheme.Hom.H.pullbackAddHom_apply,
    Ext.comp_assoc_of_third_deg_zero]

/-- **The composition law for the pullback map on the cohomology of a sheaf of modules**:
pulling back along `b` and then along `a` is pulling back along `a ≫ b`, followed by the
inverse of the canonical identification `a^* b^* G ≅ (a ≫ b)^* G` of
`AlgebraicGeometry.Scheme.Modules.pullbackComp` (note the orientation, opposite to that of
`AlgebraicGeometry.Scheme.Hom.pullbackAbComp`):

```
H^n(Y, G) --pullbackAddHom b--> H^n(X, b^* G) --pullbackAddHom a--> H^n(Z, a^* b^* G)
    |                                                                       ^
    +---pullbackAddHom (a ≫ b)---> H^n(Z, (a ≫ b)^* G) --H.map (pullbackComp)⁻¹---+
```
-/
lemma H.pullbackAddHom_comp (a : Z ⟶ X) (b : X ⟶ Y) (G : Y.Modules) (n : ℕ) (e : G.H n) :
    H.pullbackAddHom a ((pullback b).obj G) n (H.pullbackAddHom b G n e) =
      H.map ((pullbackComp a b).inv.app G) n (H.pullbackAddHom (a ≫ b) G n e) := by
  rw [H.pullbackAddHom_eq_comp_pullbackAbComparison a,
    H.pullbackAddHom_eq_comp_pullbackAbComparison b, Scheme.Hom.H.pullbackAddHom_comp_mk₀,
    Scheme.Hom.H.pullbackAddHom_comp, H.map_apply, H.mapAddHom_apply,
    H.pullbackAddHom_eq_comp_pullbackAbComparison]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc]
  rw [pullbackAbComparison_comp a b G]

end Scheme.Modules

end AlgebraicGeometry
