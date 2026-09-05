/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.QlbarCoefficient.CommonStage.Defs

/-!
# Descent of coefficient-compatible functors

A family of functors `F i : C i ⥤ D i` between the categories of two transition systems,
equipped with compatibility isomorphisms `F i ⋙ T' j/i ≅ T j/i ⋙ F j` for `i ≤ j` which are
coherent with the unit and associativity comparisons, induces a functor between the
common-stage categories. This is the mechanism by which every stagewise operation (the
shift, the six functors, ...) is transported to `ℚ̄_ℓ` coefficients.

## Main definitions

- `CategoryTheory.TransitionSystem.CompatibleFunctor`: a coefficient-compatible family of
  functors.
- `CategoryTheory.TransitionSystem.CompatibleFunctor.mapAt`: the effect on a morphism
  represented at a fixed stage.
- `CategoryTheory.TransitionSystem.CompatibleFunctor.functor`: the induced functor between
  the common-stage categories.
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category

variable {I : Type w} [Preorder I] {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
  {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]

namespace TransitionSystem

/-- A coefficient-compatible family of functors between two transition systems on the same
index preorder: functors `F i : C i ⥤ D i` together with compatibility isomorphisms with
the transition functors, coherent with the unit and associativity comparisons. -/
structure CompatibleFunctor (S : TransitionSystem C) (S' : TransitionSystem D) where
  /-- The functor at the stage `i`. -/
  F (i : I) : C i ⥤ D i
  /-- The compatibility isomorphism with scalar extension. -/
  comm {i j : I} (h : i ≤ j) : F i ⋙ S'.T h ≅ S.T h ⋙ F j
  /-- Coherence with the unit comparisons. -/
  comm_unitIso (i : I) (X : C i) :
    (comm (le_refl i)).hom.app X ≫ (F i).map ((S.unitIso i).hom.app X) =
      (S'.unitIso i).hom.app ((F i).obj X)
  /-- Coherence with the associativity comparisons. -/
  comm_assoc {i j k : I} (h₁ : i ≤ j) (h₂ : j ≤ k) (X : C i) :
    (comm (h₁.trans h₂)).hom.app X =
      (S'.assoc h₁ h₂).inv.app ((F i).obj X) ≫ (S'.T h₂).map ((comm h₁).hom.app X) ≫
        (comm h₂).hom.app ((S.T h₁).obj X) ≫ (F k).map ((S.assoc h₁ h₂).hom.app X)

namespace CompatibleFunctor

open CommonStage

variable {S : TransitionSystem C} {S' : TransitionSystem D} (Φ : CompatibleFunctor S S')

/-- The associativity coherence, as an equality of isomorphisms. -/
lemma commIso_assoc {i j k : I} (h₁ : i ≤ j) (h₂ : j ≤ k) (X : C i) :
    (Φ.comm (h₁.trans h₂)).app X =
      ((S'.assoc h₁ h₂).app ((Φ.F i).obj X)).symm ≪≫ (S'.T h₂).mapIso ((Φ.comm h₁).app X) ≪≫
        (Φ.comm h₂).app ((S.T h₁).obj X) ≪≫ (Φ.F k).mapIso ((S.assoc h₁ h₂).app X) :=
  Iso.ext (Φ.comm_assoc h₁ h₂ X)

/-- The inverse form of the associativity coherence. -/
lemma comm_assoc_inv {i j k : I} (h₁ : i ≤ j) (h₂ : j ≤ k) (X : C i) :
    (Φ.comm (h₁.trans h₂)).inv.app X =
      (Φ.F k).map ((S.assoc h₁ h₂).inv.app X) ≫ (Φ.comm h₂).inv.app ((S.T h₁).obj X) ≫
        (S'.T h₂).map ((Φ.comm h₁).inv.app X) ≫ (S'.assoc h₁ h₂).hom.app ((Φ.F i).obj X) := by
  simpa using congrArg Iso.inv (Φ.commIso_assoc h₁ h₂ X)

/-- The object of the common-stage category over `S'` attached to an object over `S`. -/
@[simps]
def obj (X : CommonStage S) : CommonStage S' where
  stage := X.stage
  obj := (Φ.F X.stage).obj X.obj

variable {X Y Z : CommonStage S} {k l : I}

/-- The effect of `Φ` on a morphism represented at the stage `k`. -/
def mapAt (hX : X.stage ≤ k) (hY : Y.stage ≤ k) (u : X.extend hX ⟶ Y.extend hY) :
    (Φ.obj X).extend hX ⟶ (Φ.obj Y).extend hY :=
  (Φ.comm hX).hom.app X.obj ≫ (Φ.F k).map u ≫ (Φ.comm hY).inv.app Y.obj

lemma mapAt_id (hX : X.stage ≤ k) :
    Φ.mapAt hX hX (𝟙 (X.extend hX)) = 𝟙 ((Φ.obj X).extend hX) := by
  simp [mapAt]
  rfl

lemma mapAt_comp (hX : X.stage ≤ k) (hY : Y.stage ≤ k) (hZ : Z.stage ≤ k)
    (u : X.extend hX ⟶ Y.extend hY) (v : Y.extend hY ⟶ Z.extend hZ) :
    Φ.mapAt hX hZ (u ≫ v) = Φ.mapAt hX hY u ≫ Φ.mapAt hY hZ v := by
  simp [mapAt]

/-- The associativity coherence, rewritten so that the two comparisons for the composite
stage appear on the left. -/
lemma comm_corner_hom {i j k : I} (h₁ : i ≤ j) (h₂ : j ≤ k) (X : C i) :
    (Φ.comm (h₁.trans h₂)).hom.app X ≫ (Φ.F k).map ((S.assoc h₁ h₂).inv.app X) =
      (S'.assoc h₁ h₂).inv.app ((Φ.F i).obj X) ≫ (S'.T h₂).map ((Φ.comm h₁).hom.app X) ≫
        (Φ.comm h₂).hom.app ((S.T h₁).obj X) := by
  have hc : (Φ.F k).map ((S.assoc h₁ h₂).hom.app X) ≫ (Φ.F k).map ((S.assoc h₁ h₂).inv.app X)
      = 𝟙 _ := Iso.map_hom_inv_id ((S.assoc h₁ h₂).app X) (Φ.F k)
  rw [Φ.comm_assoc h₁ h₂ X]
  simp only [Category.assoc]
  rw [hc]
  simp

/-- The inverse form of `comm_corner_hom`. -/
lemma comm_corner_inv {i j k : I} (h₁ : i ≤ j) (h₂ : j ≤ k) (X : C i) :
    (Φ.F k).map ((S.assoc h₁ h₂).hom.app X) ≫ (Φ.comm (h₁.trans h₂)).inv.app X =
      (Φ.comm h₂).inv.app ((S.T h₁).obj X) ≫ (S'.T h₂).map ((Φ.comm h₁).inv.app X) ≫
        (S'.assoc h₁ h₂).hom.app ((Φ.F i).obj X) := by
  have hc : (Φ.F k).map ((S.assoc h₁ h₂).hom.app X) ≫ (Φ.F k).map ((S.assoc h₁ h₂).inv.app X)
      = 𝟙 _ := Iso.map_hom_inv_id ((S.assoc h₁ h₂).app X) (Φ.F k)
  rw [Φ.comm_assoc_inv h₁ h₂ X, ← Category.assoc, hc]
  simp

lemma transport_mapAt (hX : X.stage ≤ k) (hY : Y.stage ≤ k) (hkl : k ≤ l)
    (u : X.extend hX ⟶ Y.extend hY) :
    transport hkl (Φ.mapAt hX hY u) =
      Φ.mapAt (hX.trans hkl) (hY.trans hkl) (transport hkl u) := by
  have nat : ∀ (a b : C k) (f : a ⟶ b),
      (S'.T hkl).map ((Φ.F k).map f) ≫ (Φ.comm hkl).hom.app b =
        (Φ.comm hkl).hom.app a ≫ (Φ.F l).map ((S.T hkl).map f) :=
    fun _ _ f ↦ (Φ.comm hkl).hom.naturality f
  simp only [transport, mapAt, Functor.map_comp, Category.assoc]
  slice_rhs 1 2 => rw [Φ.comm_corner_hom hX hkl X.obj]
  slice_rhs 5 6 => rw [Φ.comm_corner_inv hY hkl Y.obj]
  slice_rhs 3 4 => rw [← nat]
  simp
  rfl

/-- The effect of `Φ` on a morphism of the common-stage category. -/
noncomputable def mapHom [IsDirectedOrder I] (f : X ⟶ Y) : Φ.obj X ⟶ Φ.obj Y :=
  Quotient.liftOn (f : Hom X Y)
    (fun u ↦ homMk (X := Φ.obj X) (Y := Φ.obj Y) u.leLeft u.leRight
      (Φ.mapAt u.leLeft u.leRight u.hom))
    (fun u u' h ↦ by
      obtain ⟨p, hu, hu', e⟩ := h
      rw [← homMk_transport (X := Φ.obj X) (Y := Φ.obj Y) u.leLeft u.leRight hu,
        ← homMk_transport (X := Φ.obj X) (Y := Φ.obj Y) u'.leLeft u'.leRight hu',
        Φ.transport_mapAt, Φ.transport_mapAt, e])

@[simp]
lemma mapHom_homMk [IsDirectedOrder I] (hX : X.stage ≤ k) (hY : Y.stage ≤ k)
    (u : X.extend hX ⟶ Y.extend hY) :
    Φ.mapHom (homMk hX hY u) =
      homMk (X := Φ.obj X) (Y := Φ.obj Y) hX hY (Φ.mapAt hX hY u) := rfl

/-- The functor between common-stage categories induced by a coefficient-compatible family
of functors. -/
noncomputable def functor [IsDirectedOrder I] :
    CommonStage S ⥤ CommonStage S' where
  obj X := Φ.obj X
  map f := Φ.mapHom f
  map_id X := by
    rw [id_eq_homMk, mapHom_homMk, Φ.mapAt_id]
    exact homMk_id (X := Φ.obj X) (le_refl X.stage)
  map_comp {X Y Z} f g := by
    obtain ⟨k, hX, hY, hZ, u, v, rfl, rfl⟩ := exists_homMk_comp f g
    rw [homMk_comp_homMk, mapHom_homMk, mapHom_homMk, mapHom_homMk, Φ.mapAt_comp,
      homMk_comp_homMk]

end CompatibleFunctor

end TransitionSystem

end CategoryTheory
