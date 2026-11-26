/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Evaluation of germs of locally constant maps

Evaluation at a point identifies the stalk of the presheaf of locally constant maps with the
coefficient set.

## References

* [Stacks Project, Tags 006W and 007B](https://stacks.math.columbia.edu/tag/006W)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat

/-- Evaluation identifies the germs of locally constant maps with the coefficient set.
Here `L` is the presheaf `V ↦ L_R(V)` of locally constant maps `V → R`, and `L.germ V x hx` is
the coprojection `g ↦ g_x` into the stalk `L.stalk x`. -/
theorem existsUnique_locallyConstant_germ_evaluation (X : TopCat.{u}) (x : X) (R : Type u) :
    let L : X.Presheaf (Type u) :=
      { obj := fun V ↦ LocallyConstant {y : X // y ∈ unop V} R
        map := fun {U V} i ↦ TypeCat.ofHom (LocallyConstant.comap
          ⟨fun y : {y : X // y ∈ unop V} ↦ ⟨y.1, i.unop.le y.2⟩,
            continuous_subtype_val.subtype_mk _⟩)
        map_id := by intros; rfl
        map_comp := by intros; rfl }
    ∃ ev : L.stalk x → R,
      (∀ (V : Opens X) (hx : x ∈ V) (g : LocallyConstant V R),
        ev (L.germ V x hx g) = g ⟨x, hx⟩) ∧
      Function.Bijective ev ∧
      ∀ ev' : L.stalk x → R,
        (∀ (V : Opens X) (hx : x ∈ V) (g : LocallyConstant V R),
          ev' (L.germ V x hx g) = g ⟨x, hx⟩) → ev' = ev := by
  dsimp
  let L : X.Presheaf (Type u) :=
    { obj := fun V ↦ LocallyConstant {y : X // y ∈ unop V} R
      map := fun {U V} i ↦ TypeCat.ofHom (LocallyConstant.comap
        ⟨fun y : {y : X // y ∈ unop V} ↦ ⟨y.1, i.unop.le y.2⟩,
          continuous_subtype_val.subtype_mk _⟩)
      map_id := by intros; rfl
      map_comp := by intros; rfl }
  let U (t : L.stalk x) : Opens X := Classical.choose (L.exists_germ_eq t)
  let hm (t : L.stalk x) : x ∈ U t :=
    Classical.choose (Classical.choose_spec (L.exists_germ_eq t))
  let hs (t : L.stalk x) : LocallyConstant (U t) R :=
    Classical.choose (Classical.choose_spec
      (Classical.choose_spec (L.exists_germ_eq t)))
  let ev : L.stalk x → R := fun t ↦ hs t ⟨x, hm t⟩
  have hrep (t : L.stalk x) : L.germ (U t) x (hm t) (hs t) = t := by
    exact Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (L.exists_germ_eq t)))
  have hval : ∀ (V : Opens X) (hx : x ∈ V) (g : LocallyConstant V R),
      ev (L.germ V x hx g) = g ⟨x, hx⟩ := by
    intro V hx g
    let t := L.germ V x hx g
    have heq0 : L.germ (U t) x (hm t) (hs t) = L.germ V x hx g := by
      rw [hrep t]
    obtain ⟨W, hxW, iWU, iWV, heq⟩ :=
      L.germ_eq x (hm t) hx (hs t) g heq0
    have hev := congrArg (fun k ↦ k ⟨x, hxW⟩) heq
    change hs t ⟨x, hm t⟩ = g ⟨x, hx⟩
    simpa [L, LocallyConstant.comap] using hev
  refine ⟨ev, hval, ?_, ?_⟩
  · constructor
    · intro a b hab
      obtain ⟨Va, hxa, ga, rfl⟩ := L.exists_germ_eq a
      obtain ⟨Vb, hxb, gb, rfl⟩ := L.exists_germ_eq b
      have hpoint : ga ⟨x, hxa⟩ = gb ⟨x, hxb⟩ := by
        rw [← hval Va hxa ga, ← hval Vb hxb gb, hab]
      let A : Opens X := ⟨Subtype.val '' {y : Va | ga y = ga ⟨x, hxa⟩},
        Va.isOpen.isOpenMap_subtype_val _ (ga.isLocallyConstant.isOpen_fiber _)⟩
      let B : Opens X := ⟨Subtype.val '' {y : Vb | gb y = gb ⟨x, hxb⟩},
        Vb.isOpen.isOpenMap_subtype_val _ (gb.isLocallyConstant.isOpen_fiber _)⟩
      have hA : A ≤ Va := by
        rintro y ⟨z, hz, rfl⟩
        exact z.property
      have hB : B ≤ Vb := by
        rintro y ⟨z, hz, rfl⟩
        exact z.property
      have hxAB : x ∈ A ⊓ B :=
        ⟨⟨⟨x, hxa⟩, rfl, rfl⟩, ⟨⟨x, hxb⟩, rfl, rfl⟩⟩
      apply L.germ_ext (A ⊓ B) hxAB
        (homOfLE (inf_le_left.trans hA)) (homOfLE (inf_le_right.trans hB))
      apply LocallyConstant.ext
      intro y
      obtain ⟨a, ha, hea⟩ := y.property.1
      obtain ⟨b, hb, heb⟩ := y.property.2
      change ga ⟨y.val, _⟩ = gb ⟨y.val, _⟩
      have ea : (⟨y.val, (inf_le_left.trans hA) y.property⟩ : Va) = a :=
        Subtype.ext hea.symm
      have eb : (⟨y.val, (inf_le_right.trans hB) y.property⟩ : Vb) = b :=
        Subtype.ext heb.symm
      rw [ea, eb]
      exact ha.trans (hpoint.trans hb.symm)
    · intro r
      let g : LocallyConstant (⊤ : Opens X) R := LocallyConstant.const (⊤ : Opens X) r
      refine ⟨L.germ ⊤ x (by simp) g, ?_⟩
      exact hval ⊤ (by simp) g
  · intro ev' hev'
    funext t
    obtain ⟨V, hxV, g, rfl⟩ := L.exists_germ_eq t
    rw [hev' V hxV g, hval V hxV g]

end TopCat
