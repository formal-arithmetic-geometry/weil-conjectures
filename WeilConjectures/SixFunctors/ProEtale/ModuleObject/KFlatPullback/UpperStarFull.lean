/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective

/-!
# Pullbacks of multiplications by global sections

Let `h : S ⟶ V` be a morphism of schemes such that the restriction of global sections
`Γ(V, F) ⟶ Γ(S, h^* F)` is surjective for some abelian pro-étale sheaf `F` on `V`. Then every
morphism `𝟙 ⟶ h^* F` of sheaves on `S` is of the form `ε ≫ h^* s` for a morphism `s : 𝟙 ⟶ F`
(`AlgebraicGeometry.ProEtale.exists_ε_comp_upperStar_map_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- A morphism from the unit `ℤ` of abelian groups lifts along a surjective morphism. -/
lemma exists_comp_eq_of_surjective_tensorUnit {A B : Ab.{u}} (f : A ⟶ B)
    (hf : Function.Surjective f) (γ : 𝟙_ Ab.{u} ⟶ B) : ∃ δ : 𝟙_ Ab.{u} ⟶ A, δ ≫ f = γ := by
  obtain ⟨a, ha⟩ := hf (γ (ULift.up (1 : ℤ)))
  refine ⟨AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun n : ULift.{u} ℤ ↦ n.down • a)
    fun _ _ ↦ add_smul _ _ _), ?_⟩
  refine AddCommGrpCat.ext fun n ↦ ?_
  obtain ⟨k⟩ := n
  have hn : (ULift.up k : ULift.{u} ℤ) = k • (ULift.up (1 : ℤ) : ULift.{u} ℤ) := by
    ext
    simp
  rw [hn, map_zsmul, map_zsmul, ← ha, ConcreteCategory.comp_apply]
  simp

variable {S V : Scheme.{u}} (h : S ⟶ V)

/-- If the restriction of global sections along `h` is surjective on `F`, every morphism from the
unit to `h_* h^* F` factors through the unit of `h^* ⊣ h_*`. -/
lemma exists_comp_unit_eq (F : Sheaf (ProEt.topology V) Ab.{u + 1})
    (hF : Function.Surjective ((globalSectionsToUpperStar Ab.{u + 1} h).app F))
    (c : 𝟙_ (Sheaf (ProEt.topology V) Ab.{u + 1}) ⟶
      (h)_*[Ab.{u + 1}].obj ((h)^*[Ab.{u + 1}].obj F)) :
    ∃ s : 𝟙_ _ ⟶ F, s ≫ (upperStarLowerStarAdjunction Ab.{u + 1} h).unit.app F = c := by
  have hsurj : Function.Surjective
      ((Sheaf.Γ _ Ab.{u + 1}).map ((upperStarLowerStarAdjunction Ab.{u + 1} h).unit.app F)) := by
    intro y
    obtain ⟨x, hx⟩ := hF ((globalSectionsLowerStarIso Ab.{u + 1} h).hom.app _ y)
    refine ⟨x, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso
      ((globalSectionsLowerStarIso Ab.{u + 1} h).hom.app ((h)^*[Ab.{u + 1}].obj F))).1
    rw [← hx, globalSectionsToUpperStar_app, ConcreteCategory.comp_apply]
    rfl
  let adj := constantSheafΓAdj (ProEt.topology V) Ab.{u + 1}
  obtain ⟨δ, hδ⟩ := exists_comp_eq_of_surjective_tensorUnit _ hsurj (adj.homEquiv _ _ c)
  refine ⟨(adj.homEquiv _ _).symm δ, (adj.homEquiv _ _).injective ?_⟩
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply, hδ]

/-- If the restriction of global sections along `h` is surjective on `F`, every morphism
`𝟙 ⟶ h^* F` is `ε ≫ h^* s` for a morphism `s : 𝟙 ⟶ F`. -/
lemma exists_ε_comp_upperStar_map_eq (F : Sheaf (ProEt.topology V) Ab.{u + 1})
    (hF : Function.Surjective ((globalSectionsToUpperStar Ab.{u + 1} h).app F))
    (t : 𝟙_ (Sheaf (ProEt.topology S) Ab.{u + 1}) ⟶ (h)^*[Ab.{u + 1}].obj F) :
    ∃ s : 𝟙_ _ ⟶ F, Functor.LaxMonoidal.ε (h)^*[Ab.{u + 1}] ≫ (h)^*[Ab.{u + 1}].map s = t := by
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} h
  obtain ⟨s, hs⟩ := exists_comp_unit_eq h F hF
    (adj.homEquiv _ _ (inv (Functor.LaxMonoidal.ε (h)^*[Ab.{u + 1}]) ≫ t))
  refine ⟨s, ?_⟩
  have : (h)^*[Ab.{u + 1}].map s = inv (Functor.LaxMonoidal.ε (h)^*[Ab.{u + 1}]) ≫ t := by
    apply (adj.homEquiv _ _).injective
    rw [← hs, Adjunction.homEquiv_unit, adj.unit_naturality]
  rw [this, IsIso.hom_inv_id_assoc]

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The extension of scalars along the isomorphism `α_h` is an equivalence. -/
instance isEquivalence_extendScalars_condensedPullbackHom' :
    (Mod.extendScalars (condensedPullbackHom Λ h)).IsEquivalence :=
  have : (Mod.comap (asIso (condensedPullbackHom Λ h)).inv).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ h)).symm.isEquivalence_functor
  Functor.isEquivalence_of_iso (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ h)).symm

/-- **The pullback is full on the endomorphisms of the unit module** as soon as the restriction
of global sections of `Λ_V` along `h` is surjective. -/
lemma exists_upperStar_map_eq_of_surjective
    (hΛ : Function.Surjective
      ((globalSectionsToUpperStar Ab.{u + 1} h).app (condensedRingObj Λ V)))
    (ψ : (h)^*⟦Λ⟧.obj (𝟙_ _) ⟶ (h)^*⟦Λ⟧.obj (𝟙_ _)) :
    ∃ d : 𝟙_ (Mod (Sheaf (ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) ⟶ 𝟙_ _,
      (h)^*⟦Λ⟧.map d = ψ := by
  obtain ⟨ψ', rfl⟩ := (Mod.extendScalars (condensedPullbackHom Λ h)).map_surjective ψ
  obtain ⟨τ, rfl⟩ := Mod.regularEndRingHom_bijective.2 ψ'
  obtain ⟨s, hs⟩ := exists_ε_comp_upperStar_map_eq h _ hΛ τ.hom
  refine ⟨Mod.regularEndRingHom (MonObj.Γ.ofHom s), ?_⟩
  have h₁ := Functor.mapMod_map_regularEndRingHom (h)^*[Ab.{u + 1}] (condensedRingObj Λ V)
    (MonObj.Γ.ofHom s)
  have h₂ : MonObj.Γ.mapFunctor (h)^*[Ab.{u + 1}] (MonObj.Γ.ofHom s) = τ := by
    ext1
    rw [MonObj.Γ.mapFunctor_hom, MonObj.Γ.hom_ofHom, hs]
  rw [h₂] at h₁
  exact congrArg (Mod.extendScalars (condensedPullbackHom Λ h)).map h₁

end CondensedRing

end AlgebraicGeometry.ProEtale
