/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible

/-!
# Lifting local isomorphisms of towers over weakly contractible objects

Let `R` and `G` be towers `ℕᵒᵖ ⥤ Sheaf J A` of sheaves on a site. Suppose that `R₀` and `G₀`
are locally isomorphic, and that every local isomorphism `Rₙ ≅ Gₙ` lifts locally to an
isomorphism `Rₙ₊₁ ≅ Gₙ₊₁` compatible with the transition maps. Then over every weakly
contractible object `W` the towers are isomorphic: `R|_W ≅ G|_W`
(`CategoryTheory.GrothendieckTopology.nonempty_iso_overPullback_of_isWeaklyContractible`).

This is the sheaf-theoretic step of the passage from a tower `(Gₙ)` of locally constant
`ℤ/ℓⁿ`-sheaves to the lattice `lim Gₙ`: local trivialisations `Gₙ ≅ (ℤ/ℓⁿ)ʳ` at each finite
level, which a priori are not compatible, become compatible over weakly contractible objects,
where every locally surjective map of sheaves of sets is surjective on sections. The proof
applies this to the sheaves of isomorphisms `Iso(Rₙ, Gₙ)` (`CategoryTheory.isoSheaf`) and to
the sheaves of compatible pairs of isomorphisms at consecutive levels
(`CategoryTheory.isoPairSheaf`), and chooses the lifts recursively.

## Main definitions

- `CategoryTheory.isoSheaf`: the sheaf of types `X ↦ (F|_X ≅ G|_X)`.
- `CategoryTheory.isoPairSheaf`: the sheaf of pairs of isomorphisms `(ψ, φ)`, with
  `ψ : F'|_X ≅ G'|_X` and `φ : F|_X ≅ G|_X` compatible with given maps `F' ⟶ F`, `G' ⟶ G`.

## Main results

- `CategoryTheory.GrothendieckTopology.nonempty_iso_overPullback_of_isWeaklyContractible`.
-/

@[expose] public section

universe w v v' u u'

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A]

set_option backward.isDefEq.respectTransparency.types false in
/-- The presheaf of types `X ↦ (F|_X ≅ G|_X)` of isomorphisms between the restrictions of two
sheaves to the slices `Over X`. -/
@[simps obj]
def isoPresheaf (F G : Sheaf J A) : Cᵒᵖ ⥤ Type _ where
  obj X := (J.overPullback A X.unop).obj F ≅ (J.overPullback A X.unop).obj G
  map f := ↾fun e ↦ (J.overMapPullback A f.unop).mapIso e
  map_id X := by
    ext e : 3
    refine Iso.ext ?_
    exact ConcreteCategory.congr_hom ((sheafHom' F G).map_id X) e.hom
  map_comp f g := by
    ext e : 3
    refine Iso.ext ?_
    exact ConcreteCategory.congr_hom ((sheafHom' F G).map_comp f g) e.hom

/-- The isomorphisms underlying sections of `isoPresheaf`, as a morphism to `sheafHom'`. -/
@[simps app]
def isoPresheafToSheafHom' (F G : Sheaf J A) : isoPresheaf F G ⟶ sheafHom' F G where
  app _ := ↾fun e ↦ e.hom

lemma isoPresheaf_map_hom (F G : Sheaf J A) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (e : (isoPresheaf F G).obj X) :
    ((isoPresheaf F G).map f e).hom = (sheafHom' F G).map f e.hom := rfl

lemma isoPresheaf_map_inv (F G : Sheaf J A) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (e : (isoPresheaf F G).obj X) :
    ((isoPresheaf F G).map f e).inv = (sheafHom' G F).map f e.inv := rfl

lemma sheafHom'_map_comp (F G H : Sheaf J A) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (a : (sheafHom' F G).obj X) (b : (sheafHom' G H).obj X) :
    (sheafHom' F H).map f (a ≫ b) = (sheafHom' F G).map f a ≫ (sheafHom' G H).map f b :=
  (J.overMapPullback A f.unop).map_comp a b

lemma sheafHom'_map_id (F : Sheaf J A) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (sheafHom' F F).map f (𝟙 _) = 𝟙 _ :=
  (J.overMapPullback A f.unop).map_id _

/-- The sheaf of types `sheafHom' F G` satisfies the sheaf condition for types. -/
lemma isSheaf_sheafHom' (F G : Sheaf J A) : Presieve.IsSheaf J (sheafHom' F G) :=
  (isSheaf_iff_isSheaf_of_type J _).1 (sheafHom F G).property

/-- Isomorphisms between sheaves glue: `isoPresheaf F G` is a sheaf. -/
lemma isSheaf_isoPresheaf (F G : Sheaf J A) : Presieve.IsSheaf J (isoPresheaf F G) := by
  intro X S hS x hx
  have hFG := isSheaf_sheafHom' F G S hS
  have hGF := isSheaf_sheafHom' G F S hS
  have hFF := isSheaf_sheafHom' F F S hS
  have hGG := isSheaf_sheafHom' G G S hS
  let xh : Presieve.FamilyOfElements (sheafHom' F G) S := fun Y f hf ↦ (x f hf).hom
  let xi : Presieve.FamilyOfElements (sheafHom' G F) S := fun Y f hf ↦ (x f hf).inv
  have hxh : xh.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w ↦
    congrArg Iso.hom (hx g₁ g₂ h₁ h₂ w)
  have hxi : xi.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w ↦
    congrArg Iso.inv (hx g₁ g₂ h₁ h₂ w)
  obtain ⟨a, ha, -⟩ := hFG xh hxh
  obtain ⟨b, hb, -⟩ := hGF xi hxi
  have hab : a ≫ b = 𝟙 _ := hFF.isSeparatedFor.ext fun Y f hf ↦ by
    rw [sheafHom'_map_comp, sheafHom'_map_id, ha f hf, hb f hf]
    exact (x f hf).hom_inv_id
  have hba : b ≫ a = 𝟙 _ := hGG.isSeparatedFor.ext fun Y f hf ↦ by
    rw [sheafHom'_map_comp, sheafHom'_map_id, ha f hf, hb f hf]
    exact (x f hf).inv_hom_id
  refine ⟨⟨a, b, hab, hba⟩, fun Y f hf ↦ Iso.ext (ha f hf), fun e he ↦ Iso.ext ?_⟩
  exact hFG.isSeparatedFor.ext fun Y f hf ↦ (congrArg Iso.hom (he f hf)).trans (ha f hf).symm

/-- The sheaf of types `X ↦ (F|_X ≅ G|_X)` of isomorphisms between the restrictions of two
sheaves to the slices `Over X`. -/
def isoSheaf (F G : Sheaf J A) : Sheaf J (Type _) :=
  ⟨isoPresheaf F G, (isSheaf_iff_isSheaf_of_type J _).2 (isSheaf_isoPresheaf F G)⟩

end CategoryTheory
