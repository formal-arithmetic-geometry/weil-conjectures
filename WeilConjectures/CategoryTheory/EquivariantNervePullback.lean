/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SheafSubcategoryComparison
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Equivariant nerves identify canonical sheaf pullbacks

Source: Stacks Project, Sites, Tags 03A1, 00WW and 00WX
(blueprint: lem-pur-equivariant-nerve-pullback).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace CategoryTheory

private noncomputable def nerveIntertwiner
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} (H : D ⥤ Sheaf J (Type u))
    (s : D ≌ D) (σ : Sheaf J (Type u) ≌ Sheaf J (Type u))
    (a : s.functor ⋙ H ≅ H ⋙ σ.functor) :
    sheafSubcategoryNerve H ⋙ (Functor.whiskeringLeft _ _ (Type u)).obj s.functor.op ≅
      σ.inverse ⋙ sheafSubcategoryNerve H :=
  NatIso.ofComponents (fun Y ↦ NatIso.ofComponents (fun d ↦
    Equiv.toIso ((Iso.homCongr (a.app d.unop) (Iso.refl Y)).trans
      (σ.toAdjunction.homEquiv _ _))) (by
        intro d d' f
        ext g
        change (H.obj (s.functor.obj d.unop) ⟶ Y) at g
        change σ.toAdjunction.homEquiv _ _
          (a.inv.app d'.unop ≫ H.map (s.functor.map f.unop) ≫ g) =
            H.map f.unop ≫ σ.toAdjunction.homEquiv _ _ (a.inv.app d.unop ≫ g)
        have hn := a.inv.naturality f.unop
        change σ.functor.map (H.map f.unop) ≫ a.inv.app d.unop =
          a.inv.app d'.unop ≫ H.map (s.functor.map f.unop) at hn
        rw [← Category.assoc, ← hn, Category.assoc,
          σ.toAdjunction.homEquiv_naturality_left])) (by
    intro Y Y' f
    ext d g
    change σ.toAdjunction.homEquiv _ _ (a.inv.app d.unop ≫ g ≫ f) =
      σ.toAdjunction.homEquiv _ _ (a.inv.app d.unop ≫ g) ≫ σ.inverse.map f
    rw [← Category.assoc, σ.toAdjunction.homEquiv_naturality_right])

/-- An explicit equivariant restricted Yoneda nerve identifies the canonical
sheaf pullback with the given ambient automorphism.

Source: Stacks Project, Sites, Tags 03A1, 00WW and 00WX
(blueprint: lem-pur-equivariant-nerve-pullback).

Proof: Precomposition by the two inverse continuous site functors gives inverse
functors on sheaves; the site unit and counit induce the two inverse isomorphisms.
Thus the right adjoint of canonical sheaf pullback is an equivalence and so is the
pullback. For the intertwiner, apply the ambient adjunction Hom bijections to
Hom(H(sd),Y), first using H(sd) ≅ σ(Hd). Naturality in d is the naturality of this
isomorphism and the left adjunction naturality; naturality in Y is right adjunction
naturality. Lift this presheaf isomorphism to sheaves using full faithfulness of
sheaf inclusion and the supplied nerve comparison. Finally take adjoint conjugates
for the composite adjunctions with the inverse nerve equivalence. This gives the
asserted intertwiner with the canonical left adjoint, not a newly chosen inverse.
-/
theorem equivariantNervePullback
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (H : D ⥤ Sheaf J (Type u)) (s : D ≌ D)
    (σ : Sheaf J (Type u) ≌ Sheaf J (Type u))
    (a : s.functor ⋙ H ≅ H ⋙ σ.functor)
    (e : Sheaf J (Type u) ≌ Sheaf K (Type u))
    (hnerve : e.functor ⋙ sheafToPresheaf K (Type u) ≅ sheafSubcategoryNerve H)
    [s.functor.IsContinuous K K] [s.inverse.IsContinuous K K] :
    (Functor.sheafPullback s.functor (Type u) K K).IsEquivalence ∧
      Nonempty (Functor.sheafPullback s.functor (Type u) K K ⋙ e.inverse ≅
        e.inverse ⋙ σ.functor) := by
  let R := s.functor.sheafPushforwardContinuous (Type u) K K
  let Q := s.inverse.sheafPushforwardContinuous (Type u) K K
  have hR : R.IsEquivalence := by
    refine Functor.IsEquivalence.mk' Q ?_ ?_
    · exact (Functor.sheafPushforwardContinuousComp' s.counitIso (Type u) K K K ≪≫
        Functor.sheafPushforwardContinuousId (Type u) K).symm
    · exact Functor.sheafPushforwardContinuousComp' s.unitIso.symm (Type u) K K K ≪≫
        Functor.sheafPushforwardContinuousId (Type u) K
  let adj := Functor.sheafAdjunctionContinuous s.functor (Type u) K K
  have hL := adj.isEquivalence_left_of_isEquivalence_right
  refine ⟨hL, ?_⟩
  let W := (Functor.whiskeringLeft Dᵒᵖ Dᵒᵖ (Type u)).obj s.functor.op
  have j : (e.functor ⋙ R) ⋙ sheafToPresheaf K (Type u) ≅
      (σ.inverse ⋙ e.functor) ⋙ sheafToPresheaf K (Type u) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (Functor.sheafPushforwardContinuousCompSheafToPresheafIso _ _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight hnerve W ≪≫ nerveIntertwiner H s σ a ≪≫
      Functor.isoWhiskerLeft _ hnerve.symm ≪≫ (Functor.associator _ _ _).symm
  let f := (Functor.whiskeringRight (Sheaf J (Type u)) (Sheaf K (Type u))
    (Dᵒᵖ ⥤ Type u)).obj (sheafToPresheaf K (Type u))
  let k : e.functor ⋙ R ≅ σ.inverse ⋙ e.functor :=
    f.preimageIso j
  exact ⟨((conjugateIsoEquiv (adj.comp e.symm.toAdjunction)
    (e.symm.toAdjunction.comp σ.toAdjunction)).symm k).symm⟩

end CategoryTheory
