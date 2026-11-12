/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethCoefficientChangeFlat

/-!

# The Künneth map of nearby cycles under two successive flat changes of coefficients

Let `a₁ : Λ₁ ⟶ Λ₂` and `a₂ : Λ₂ ⟶ Λ₃` be flat coefficient changes whose (Push) comparisons
`ProEtale.CondensedRing.derivedPushHom` are invertible on bounded below objects along
quasi-compact quasi-separated morphisms (for instance `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`). For models whose `j`s
are quasi-compact and quasi-separated and bounded below `A₀`, `B₀` such that `Lf₁^* A₀ ⊗ᴸ Lf₂^* B₀`
is bounded below, `T₂ T₁ Π_{A₀,B₀}` and `Π_{T₂ T₁ A₀, T₂ T₁ B₀}` are isomorphic arrows
(`NearbyCyclesModel.nonempty_arrowIso_map_map_kunnethMap_of_flat_of_flat`): this is
`NearbyCyclesModel.nonempty_arrowIso_map_kunnethMap_of_flat` applied twice, the flat extensions of
scalars preserving bounded below objects and commuting with the derived tensor products.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

private lemma flatComp_nonempty_arrowIso_map_trans {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B A' B' : C} {A'' B'' : D} {f : A ⟶ B} {g : A' ⟶ B'}
    {h : A'' ⟶ B''} (k : Nonempty (Arrow.mk f ≅ Arrow.mk g))
    (l : Nonempty (Arrow.mk (F.map g) ≅ Arrow.mk h)) :
    Nonempty (Arrow.mk (F.map f) ≅ Arrow.mk h) :=
  ⟨F.mapArrow.mapIso k.some ≪≫ l.some⟩

-- Derived functors repeatedly request these graded tensor properties. Prove them once for
-- module sheaves so elaborating each functor does not reconstruct the same colimit arguments.
local instance flatComp_hasTensor₄ObjExt
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (S : Scheme.{u}) :
    ∀ K₁ K₂ K₃ K₄ : GradedObject ℤ (Mod (Sheaf (ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S)), GradedObject.HasTensor₄ObjExt K₁ K₂ K₃ K₄ := by
  infer_instance

local instance flatComp_hasGoodTensor₁₂Tensor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (S : Scheme.{u}) :
    ∀ K₁ K₂ K₃ : GradedObject ℤ (Mod (Sheaf (ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S)), GradedObject.HasGoodTensor₁₂Tensor K₁ K₂ K₃ := by
  infer_instance

local instance flatComp_hasGoodTensorTensor₂₃
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (S : Scheme.{u}) :
    ∀ K₁ K₂ K₃ : GradedObject ℤ (Mod (Sheaf (ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S)), GradedObject.HasGoodTensorTensor₂₃ K₁ K₂ K₃ := by
  infer_instance

variable {Λ₁ Λ₂ Λ₃ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ₁]
  [IsCommMonObj Λ₁] [MonObj Λ₂] [IsCommMonObj Λ₂] [MonObj Λ₃] [IsCommMonObj Λ₃]
  (a₁ : Λ₁ ⟶ Λ₂) [IsMonHom a₁] (a₂ : Λ₂ ⟶ Λ₃) [IsMonHom a₂]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a₁ X))]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a₂ X))]
  {X X' Y Y' Z Z' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {P : NearbyCyclesModel Z Z'} {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

/-- **The Künneth map under two successive flat changes of coefficients**: if the (Push)
comparisons of `a₁` and `a₂` are invertible on bounded below objects along quasi-compact
quasi-separated morphisms, then for models whose `j`s are quasi-compact and quasi-separated and
bounded below `A₀`, `B₀` such that `Lf₁^* A₀ ⊗ᴸ Lf₂^* B₀` is bounded below, `T₂ T₁ Π_{A₀,B₀}` and
`Π_{T₂ T₁ A₀, T₂ T₁ B₀}` are isomorphic arrows. -/
theorem nonempty_arrowIso_map_map_kunnethMap_of_flat_of_flat
    (h₁ : ∀ ⦃U T : Scheme.{u}⦄ (j : U ⟶ T) [QuasiCompact j] [QuasiSeparated j]
      (K : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ₁ U)))
      (n : ℤ) [K.IsGE n], IsIso ((derivedPushHom a₁ j).app K))
    (h₂ : ∀ ⦃U T : Scheme.{u}⦄ (j : U ⟶ T) [QuasiCompact j] [QuasiSeparated j]
      (K : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ₂ U)))
      (n : ℤ) [K.IsGE n], IsIso ((derivedPushHom a₂ j).app K))
    [QuasiCompact M.j] [QuasiSeparated M.j] [QuasiCompact N.j] [QuasiSeparated N.j]
    [QuasiCompact P.j] [QuasiSeparated P.j] (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (A₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ₁ X)))
    (B₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ₁ Y))) (n m : ℤ) [A₀.IsGE n] [B₀.IsGE n]
    [(L((f₁)^*⟦Λ₁⟧).obj A₀ ⊗ L((f₂)^*⟦Λ₁⟧).obj B₀).IsGE m] :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap a₂ Z')).leftDerivedFunctor.map
        ((Mod.extendScalars (coefficientMap a₁ Z')).leftDerivedFunctor.map
          (kunnethMap Λ₁ φ₁ φ₂ A₀ B₀))) ≅
      Arrow.mk (kunnethMap Λ₃ φ₁ φ₂
        ((Mod.extendScalars (coefficientMap a₂ X)).leftDerivedFunctor.obj
          ((Mod.extendScalars (coefficientMap a₁ X)).leftDerivedFunctor.obj A₀))
        ((Mod.extendScalars (coefficientMap a₂ Y)).leftDerivedFunctor.obj
          ((Mod.extendScalars (coefficientMap a₁ Y)).leftDerivedFunctor.obj B₀)))) := by
  let A₁ := (Mod.extendScalars (coefficientMap a₁ X)).leftDerivedFunctor.obj A₀
  let B₁ := (Mod.extendScalars (coefficientMap a₁ Y)).leftDerivedFunctor.obj B₀
  let C₀ := L((f₁)^*⟦Λ₁⟧).obj A₀ ⊗ L((f₂)^*⟦Λ₁⟧).obj B₀
  let C₁ := L((f₁)^*⟦Λ₂⟧).obj A₁ ⊗ L((f₂)^*⟦Λ₂⟧).obj B₁
  -- the first step `a₁`
  have := isGE_leftDerivedUpperStar_obj _ M.ε A₀ n
  have := isGE_leftDerivedUpperStar_obj _ N.ε B₀ n
  have := isGE_leftDerivedUpperStar_obj _ P.ε C₀ m
  have k₁ := nonempty_arrowIso_map_kunnethMap_of_flat a₁ φ₁ φ₂ A₀ B₀
    (h₁ M.j _ n) (h₁ N.j _ n) (h₁ P.j _ m)
  -- the second step `a₂`, at the bounded below `T₁ A₀` and `T₁ B₀`
  have : A₁.IsGE n := isGE_leftDerivedFunctor_extendScalars_obj a₁ A₀ n
  have : B₁.IsGE n := isGE_leftDerivedFunctor_extendScalars_obj a₁ B₀ n
  have := isGE_leftDerivedFunctor_extendScalars_obj a₁ C₀ m
  have : C₁.IsGE m :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (X := (Mod.extendScalars (coefficientMap a₁ Z)).leftDerivedFunctor.obj C₀)
      (((derivedExtendScalarsTensorIso a₁ Z).app _).app _ ≪≫
        tensorIso ((derivedPullIso a₁ f₁).app A₀) ((derivedPullIso a₁ f₂).app B₀)) m
  have := isGE_leftDerivedUpperStar_obj _ M.ε A₁ n
  have := isGE_leftDerivedUpperStar_obj _ N.ε B₁ n
  have := isGE_leftDerivedUpperStar_obj _ P.ε C₁ m
  have k₂ := nonempty_arrowIso_map_kunnethMap_of_flat a₂ φ₁ φ₂ A₁ B₁
    (h₂ M.j _ n) (h₂ N.j _ n) (h₂ P.j _ m)
  exact flatComp_nonempty_arrowIso_map_trans
    (Mod.extendScalars (coefficientMap a₂ Z')).leftDerivedFunctor k₁ k₂

/-- **The restricted Künneth map under two successive flat changes of coefficients**: under the
hypotheses of `NearbyCyclesModel.nonempty_arrowIso_map_map_kunnethMap_of_flat_of_flat`, for every
`h : W ⟶ Z'`, `T₂ T₁ Lh^* Π_{A₀,B₀}` and `Lh^* Π_{T₂ T₁ A₀, T₂ T₁ B₀}` are isomorphic arrows. -/
theorem nonempty_arrowIso_map_map_map_kunnethMap_of_flat_of_flat
    (h₁ : ∀ ⦃U T : Scheme.{u}⦄ (j : U ⟶ T) [QuasiCompact j] [QuasiSeparated j]
      (K : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ₁ U)))
      (n : ℤ) [K.IsGE n], IsIso ((derivedPushHom a₁ j).app K))
    (h₂ : ∀ ⦃U T : Scheme.{u}⦄ (j : U ⟶ T) [QuasiCompact j] [QuasiSeparated j]
      (K : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ₂ U)))
      (n : ℤ) [K.IsGE n], IsIso ((derivedPushHom a₂ j).app K))
    [QuasiCompact M.j] [QuasiSeparated M.j] [QuasiCompact N.j] [QuasiSeparated N.j]
    [QuasiCompact P.j] [QuasiSeparated P.j] (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    {W : Scheme.{u}} (h : W ⟶ Z')
    (A₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ₁ X)))
    (B₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ₁ Y))) (n m : ℤ) [A₀.IsGE n] [B₀.IsGE n]
    [(L((f₁)^*⟦Λ₁⟧).obj A₀ ⊗ L((f₂)^*⟦Λ₁⟧).obj B₀).IsGE m] :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap a₂ W)).leftDerivedFunctor.map
        ((Mod.extendScalars (coefficientMap a₁ W)).leftDerivedFunctor.map
          (L((h)^*⟦Λ₁⟧).map (kunnethMap Λ₁ φ₁ φ₂ A₀ B₀)))) ≅
      Arrow.mk (L((h)^*⟦Λ₃⟧).map (kunnethMap Λ₃ φ₁ φ₂
        ((Mod.extendScalars (coefficientMap a₂ X)).leftDerivedFunctor.obj
          ((Mod.extendScalars (coefficientMap a₁ X)).leftDerivedFunctor.obj A₀))
        ((Mod.extendScalars (coefficientMap a₂ Y)).leftDerivedFunctor.obj
          ((Mod.extendScalars (coefficientMap a₁ Y)).leftDerivedFunctor.obj B₀))))) :=
  nonempty_arrowIso_map_map_of_iso (F := L((h)^*⟦Λ₁⟧))
    (G := L(Mod.extendScalars (coefficientMap a₁ W)) ⋙ L(Mod.extendScalars (coefficientMap a₂ W)))
    (F' := L(Mod.extendScalars (coefficientMap a₁ Z')) ⋙
      L(Mod.extendScalars (coefficientMap a₂ Z'))) (G' := L((h)^*⟦Λ₃⟧))
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (derivedPullIso a₁ h) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (derivedPullIso a₂ h) ≪≫
      (Functor.associator _ _ _).symm) _
    (nonempty_arrowIso_map_map_kunnethMap_of_flat_of_flat a₁ a₂ h₁ h₂ φ₁ φ₂ A₀ B₀ n m)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
