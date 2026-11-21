/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosureRepresentable

/-!
# Right adjoints on a localizing closure restrict to the generators

Let `P` be a property of objects of a pretriangulated category `C`, stable under shifts and
closed under isomorphisms, and let `F : Loc(P) ⥤ D` be left adjoint to `G`. Suppose that `F` maps
`P` into a property `Q` of objects of `D`, and that the restriction `Fb : P ⥤ Q` of `F` is a
left adjoint. Then `G` maps `Q` into `P`
(`CategoryTheory.ObjectProperty.prop_rightAdjoint_obj_of_isLeftAdjoint`), and the adjunction
`F ⊣ G` restricts to an adjunction between the full subcategories `P` and `Q`
(`CategoryTheory.Adjunction.restrictObjectProperty`).

## Implementation details

For `N` in `Q`, the value `Fb^R N` of the right adjoint of `Fb` represents `A ↦ Hom(F A, N)` on
the objects `A` of `P`; since the objects of `P` detect isomorphisms of `Loc(P)`
(`CategoryTheory.ObjectProperty.isIso_homEquiv_of_bijective_localizingClosure`), `G N ≅ Fb^R N`.
-/

@[expose] public section

universe v u u'

open CategoryTheory Limits

namespace CategoryTheory

namespace Adjunction

variable {C : Type*} {D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C}

/-- An adjunction `F ⊣ G` restricts to full subcategories `P` of `C` and `Q` of `D` such that `F`
maps `P` into `Q` and `G` maps `Q` into `P`. -/
noncomputable def restrictObjectProperty (adj : F ⊣ G) (P : ObjectProperty C)
    (Q : ObjectProperty D) (hF : ∀ X, P X → Q (F.obj X)) (hG : ∀ Y, Q Y → P (G.obj Y)) :
    Q.lift (P.ι ⋙ F) (fun X ↦ hF X.obj X.property) ⊣
      P.lift (Q.ι ⋙ G) (fun Y ↦ hG Y.obj Y.property) :=
  adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι (Q.liftCompιIso _ _).symm
    (P.liftCompιIso _ _).symm

end Adjunction

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {P : ObjectProperty C}
  [P.IsStableUnderShift ℤ] [P.IsClosedUnderIsomorphisms]
  {D : Type*} [Category* D] {E : Type*} [Category* E]

/-- Let `F : Loc(P) ⥤ D` be left adjoint to `G`, and let `i : E ⥤ D` be fully faithful. If the
restriction of `F` to `P` factors through `i` as a left adjoint `Fb : P ⥤ E`, then `G` maps the
objects `i N` into `P`. -/
theorem prop_rightAdjoint_obj_of_isLeftAdjoint {F : P.localizingClosure.FullSubcategory ⥤ D}
    {G : D ⥤ P.localizingClosure.FullSubcategory} (adj : F ⊣ G) {i : E ⥤ D}
    (hi : i.FullyFaithful) (Fb : P.FullSubcategory ⥤ E) [Fb.IsLeftAdjoint]
    (e : Fb ⋙ i ≅ ιOfLE (P.le_localizingClosure) ⋙ F) (N : E) :
    P (G.obj (i.obj N)).obj := by
  let adjb := Adjunction.ofIsLeftAdjoint Fb
  let Tb := Fb.rightAdjoint.obj N
  let T : P.localizingClosure.FullSubcategory := (ιOfLE P.le_localizingClosure).obj Tb
  let ε : F.obj T ⟶ i.obj N := e.inv.app Tb ≫ i.map (adjb.counit.app N)
  have := isIso_homEquiv_of_bijective_localizingClosure adj ε fun A hA ↦ by
    let Ab : P.FullSubcategory := ⟨A.obj, hA⟩
    have h : (fun f : A ⟶ T ↦ F.map f ≫ ε) =
        (fun g : Fb.obj Ab ⟶ N ↦ e.inv.app Ab ≫ i.map g) ∘
          (adjb.homEquiv Ab N).symm ∘ fun f : A ⟶ T ↦ (homMk f.hom : Ab ⟶ Tb) := by
      ext f
      have := e.inv.naturality (homMk f.hom : Ab ⟶ Tb)
      dsimp [ε] at this ⊢
      rw [Adjunction.homEquiv_counit, i.map_comp, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ _) this
    rw [h]
    refine Function.Bijective.comp ?_ (Function.Bijective.comp (Equiv.bijective _) ?_)
    · refine ⟨fun g g' hg ↦ hi.map_injective (by simpa using hg),
        fun k ↦ ⟨hi.preimage (e.hom.app Ab ≫ k), by simp⟩⟩
    · exact ⟨fun g g' h ↦ by ext; simpa using congrArg (fun x ↦ x.hom) h,
        fun g ↦ ⟨homMk g.hom, rfl⟩⟩
  exact P.prop_of_iso ((ι _).mapIso (asIso (adj.homEquiv T _ ε))) Tb.property

end ObjectProperty

end CategoryTheory
