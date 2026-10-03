/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Test
-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃ u

open CategoryTheory Limits

/-! ### Auxiliary lemmas -/

namespace CategoryTheory.Abelian.Ext

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w} C] [HasExt.{w} D] [HasExt.{w} E]
  [EnoughInjectives C]

attribute [local instance] Ext.subsingleton_of_injective

/-- Pushing an `Ext`-class forward along two exact functors in succession is the same as
pushing it forward along their composite. -/
lemma mapExactFunctor_mapExactFunctor (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] {X Y : C} {n : ℕ} (x : Ext X Y n) :
    (x.mapExactFunctor F).mapExactFunctor G = x.mapExactFunctor (F ⋙ G) := by
  induction n generalizing Y with
  | zero =>
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X Y).2 x
    simp only [Ext.mapExactFunctor_mk₀]
    rfl
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    have := I.injective
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ X hS x
      (Ext.eq_zero_of_injective (I := I.J) _) rfl
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp, hn]
    congr 1
    rw [Ext.mapExactFunctor_extClass, Ext.mapExactFunctor_extClass]
    exact Ext.mapExactFunctor_extClass G (hS.map_of_exact F)

/-- Pushing `Ext`-classes forward along exact functors is natural with respect to natural
transformations of the functors. -/
lemma mapExactFunctor_comp_mk₀_app {F F' : C ⥤ D} [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [F'.Additive] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F'] (τ : F ⟶ F') {X Y : C} {n : ℕ} (x : Ext X Y n) :
    (x.mapExactFunctor F).comp (mk₀ (τ.app Y)) (add_zero n) =
      (mk₀ (τ.app X)).comp (x.mapExactFunctor F') (zero_add n) := by
  induction n generalizing Y with
  | zero =>
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X Y).2 x
    simp only [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, τ.naturality]
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    have := I.injective
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ X hS x
      (Ext.eq_zero_of_injective (I := I.J) _) rfl
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
      Ext.mapExactFunctor_extClass]
    refine (Ext.comp_assoc _ _ _ rfl (add_zero 1) (by omega)).trans ?_
    refine (congrArg (fun z ↦ (y.mapExactFunctor F).comp z (rfl : n + 1 = n + 1))
      ((hS.map_of_exact F).extClass_naturality (hS.map_of_exact F') (S.mapNatTrans τ))).trans ?_
    refine (Ext.comp_assoc _ _ _ (add_zero n) (zero_add 1) rfl).symm.trans ?_
    refine (congrArg (fun z ↦ z.comp (hS.map_of_exact F').extClass rfl) (hn y)).trans ?_
    exact Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)

end CategoryTheory.Abelian.Ext

namespace CategoryTheory.Sheaf

open Abelian AddCommGrpCat

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
  [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
  [HasSheafify K AddCommGrpCat.{u}] [HasExt.{w} (Sheaf K AddCommGrpCat.{u})]
  [HasSheafify L AddCommGrpCat.{u}] [HasExt.{w} (Sheaf L AddCommGrpCat.{u})]

/-- Changing the comparison of constant sheaves in `CategoryTheory.Sheaf.H.mapFunctor`
amounts to precomposing with an automorphism of the constant sheaf `ℤ`. -/
lemma H.mapFunctor_eq_precompAddEquiv (G : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u})
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e e' : (constantSheaf K AddCommGrpCat.{u}).obj (of (ULift ℤ)) ≅
      G.obj ((constantSheaf J AddCommGrpCat.{u}).obj (of (ULift ℤ))))
    (F : Sheaf J AddCommGrpCat.{u}) (n : ℕ) :
    ⇑(H.mapFunctor G e' F n) = Ext.precompAddEquiv (e' ≪≫ e.symm) _ n ∘ H.mapFunctor G e F n := by
  ext x
  simp [H.mapFunctor_apply, Ext.mk₀_comp_mk₀_assoc]

/-- The bijectivity of the map `CategoryTheory.Sheaf.H.mapFunctor` on sheaf cohomology does
not depend on the chosen comparison of constant sheaves. -/
lemma H.bijective_mapFunctor_iff (G : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u})
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e e' : (constantSheaf K AddCommGrpCat.{u}).obj (of (ULift ℤ)) ≅
      G.obj ((constantSheaf J AddCommGrpCat.{u}).obj (of (ULift ℤ))))
    (F : Sheaf J AddCommGrpCat.{u}) (n : ℕ) :
    Function.Bijective (H.mapFunctor G e F n) ↔ Function.Bijective (H.mapFunctor G e' F n) := by
  rw [H.mapFunctor_eq_precompAddEquiv G e e', EquivLike.comp_bijective]

/-- The map on sheaf cohomology induced by a composite of exact functors is the composite of
the induced maps, for the composite comparison of constant sheaves. -/
lemma H.mapFunctor_comp [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
    (G₁ : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u})
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    (G₂ : Sheaf K AddCommGrpCat.{u} ⥤ Sheaf L AddCommGrpCat.{u})
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e₁ : (constantSheaf K AddCommGrpCat.{u}).obj (of (ULift ℤ)) ≅
      G₁.obj ((constantSheaf J AddCommGrpCat.{u}).obj (of (ULift ℤ))))
    (e₂ : (constantSheaf L AddCommGrpCat.{u}).obj (of (ULift ℤ)) ≅
      G₂.obj ((constantSheaf K AddCommGrpCat.{u}).obj (of (ULift ℤ))))
    (F : Sheaf J AddCommGrpCat.{u}) (n : ℕ) (x : H F n) :
    H.mapFunctor (G₁ ⋙ G₂) (e₂ ≪≫ G₂.mapIso e₁) F n x =
      H.mapFunctor G₂ e₂ (G₁.obj F) n (H.mapFunctor G₁ e₁ F n x) := by
  simp only [H.mapFunctor_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mapExactFunctor_mapExactFunctor, Iso.trans_hom, Functor.mapIso_hom]
  rw [Ext.mk₀_comp_mk₀_assoc]

/-- The map on sheaf cohomology induced by an exact functor is compatible with natural
isomorphisms of exact functors. -/
lemma H.mapFunctor_of_iso [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
    {G G' : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u}}
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (τ : G ≅ G')
    (e : (constantSheaf K AddCommGrpCat.{u}).obj (of (ULift ℤ)) ≅
      G.obj ((constantSheaf J AddCommGrpCat.{u}).obj (of (ULift ℤ))))
    (F : Sheaf J AddCommGrpCat.{u}) (n : ℕ) (x : H F n) :
    H.mapFunctor G' (e ≪≫ τ.app _) F n x = H.map (τ.hom.app F) n (H.mapFunctor G e F n x) := by
  simp only [H.mapFunctor_apply, H.map_apply, Iso.trans_hom, Iso.app_hom]
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mapExactFunctor_comp_mk₀_app,
    Ext.mk₀_comp_mk₀_assoc]

end CategoryTheory.Sheaf
