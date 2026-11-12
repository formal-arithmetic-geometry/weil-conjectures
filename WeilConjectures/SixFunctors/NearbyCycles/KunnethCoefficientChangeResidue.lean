/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethCoefficientChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShortcutInstances
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueFinal

/-!

# The Künneth map of nearby cycles and the reduction `𝒪_E ⟶ 𝔽_E`

We specialize the compatibility of the Künneth map `Π_{A,B}` of nearby cycles with the change of
coefficients (`NearbyCyclesModel.nonempty_arrowIso_map_kunnethMap`) to the reduction
`𝒪_E ⟶ 𝔽_E` modulo the uniformizer, whose (Push) comparisons are invertible on bounded below
objects along any morphism of schemes
(`ProEtale.CondensedRing.isIso_derivedUpperStarExtendScalarsPushHom_residueField_app`):
for bounded below `𝒪_E`-complexes `A₀`, `B₀` such that `Lf₁^* A₀ ⊗ᴸ Lf₂^* B₀` is bounded below,
`𝔽_E ⊗ᴸ Π_{A₀,B₀}` and `Π_{𝔽_E ⊗ᴸ A₀, 𝔽_E ⊗ᴸ B₀}` are isomorphic arrows
(`NearbyCyclesModel.nonempty_arrowIso_map_kunnethMap_residueField`), also after restriction along
any `h : W ⟶ Z'` (`NearbyCyclesModel.nonempty_arrowIso_map_map_kunnethMap_residueField`).

The (Push) comparisons are needed at `Lε_M^* A₀`, `Lε_N^* B₀` and `Lε_P^* (Lf₁^* A₀ ⊗ᴸ Lf₂^* B₀)`.
The first two are bounded below with `A₀` and `B₀`, but the derived tensor product of bounded below
`𝒪_E`-complexes is not known to be bounded below (this would follow from a finite Tor dimension
of the condensed ring `𝒪_E`), so the bounded belowness of `Lf₁^* A₀ ⊗ᴸ Lf₂^* B₀` is a hypothesis.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme PadicAlgCl

-- Reuse the graded tensor and colimit proofs needed by every derived functor below.
-- Public restatements of the shortcut instances of `ShortcutInstances`, which is imported
-- privately (a public import would be re-exported to every dependent and change its instance
-- resolution); the local instance attribute needs them in the exported view (theorem headers).
theorem hasTensor₄ObjExt_kunnethCoefficientChangeResidue
    (T : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ :=
  hasTensor₄ObjExt_mod T R X₁ X₂ X₃ X₄

theorem hasGoodTensor₁₂Tensor_kunnethCoefficientChangeResidue
    (T : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (X₁ X₂ X₃ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ :=
  hasGoodTensor₁₂Tensor_mod T R X₁ X₂ X₃

theorem hasGoodTensorTensor₂₃_kunnethCoefficientChangeResidue
    (T : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (X₁ X₂ X₃ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ :=
  hasGoodTensorTensor₂₃_mod T R X₁ X₂ X₃

theorem hasColimitsOfShape_int_kunnethCoefficientChangeResidue
    (T : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] :
    HasColimitsOfShape ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) :=
  hasColimitsOfShape_int_mod T R

theorem preservesColimitsOfShape_int_curriedTensor_obj_kunnethCoefficientChangeResidue
    (T : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) :
    PreservesColimitsOfShape ℤ ((curriedTensor _).obj M) :=
  preservesColimitsOfShape_int_curriedTensor_obj_mod T R M

theorem preservesColimitsOfShape_int_curriedTensor_flip_obj_kunnethCoefficientChangeResidue
    (T : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) :
    PreservesColimitsOfShape ℤ ((curriedTensor _).flip.obj M) :=
  preservesColimitsOfShape_int_curriedTensor_flip_obj_mod T R M

attribute [local instance] hasTensor₄ObjExt_kunnethCoefficientChangeResidue
  hasGoodTensor₁₂Tensor_kunnethCoefficientChangeResidue
  hasGoodTensorTensor₂₃_kunnethCoefficientChangeResidue
  hasColimitsOfShape_int_kunnethCoefficientChangeResidue
  preservesColimitsOfShape_int_curriedTensor_obj_kunnethCoefficientChangeResidue
  preservesColimitsOfShape_int_curriedTensor_flip_obj_kunnethCoefficientChangeResidue

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {X X' Y Y' Z Z' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {P : NearbyCyclesModel Z Z'} {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

/-- **The Künneth map and the reduction `𝒪_E ⟶ 𝔽_E`**: for bounded below `𝒪_E`-complexes `A₀`,
`B₀` such that `Lf₁^* A₀ ⊗ᴸ Lf₂^* B₀` is bounded below, `𝔽_E ⊗ᴸ Lh^* Π_{A₀,B₀}` and
`Lh^* Π_{𝔽_E ⊗ᴸ A₀, 𝔽_E ⊗ᴸ B₀}` are isomorphic arrows, for every `h : W ⟶ Z'`. -/
theorem nonempty_arrowIso_map_map_kunnethMap_residueField (φ₁ : P.Hom M f₁ f₁')
    (φ₂ : P.Hom N f₂ f₂') {W : Scheme.{u}} (h : W ⟶ Z')
    (A₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (B₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y))) (n m : ℤ) [A₀.IsGE n]
    [B₀.IsGE n]
    [(L((f₁)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A₀ ⊗
      L((f₂)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀).IsGE m] :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap
        (Profinite.padicIntegersRingObjToResidueField ℓ E.1) W)).leftDerivedFunctor.map
        (L((h)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).map
          (kunnethMap (Profinite.padicIntegersRingObj ℓ E.1) φ₁ φ₂ A₀ B₀))) ≅
      Arrow.mk (L((h)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)⟧).map
        (kunnethMap (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) φ₁ φ₂
          ((Mod.extendScalars (coefficientMap
            (Profinite.padicIntegersRingObjToResidueField ℓ E.1) X)).leftDerivedFunctor.obj A₀)
          ((Mod.extendScalars (coefficientMap
            (Profinite.padicIntegersRingObjToResidueField ℓ E.1) Y)).leftDerivedFunctor.obj
              B₀)))) := by
  have := isGE_leftDerivedUpperStar_obj _ M.ε A₀ n
  have := isGE_leftDerivedUpperStar_obj _ N.ε B₀ n
  have := isGE_leftDerivedUpperStar_obj _ P.ε
    (L((f₁)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A₀ ⊗
      L((f₂)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀) m
  have hA := isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E M.j
    (L((M.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A₀) n
  have hB := isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E N.j
    (L((N.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀) n
  have hAB := isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E P.j
    (L((P.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj
      (L((f₁)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A₀ ⊗
        L((f₂)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀)) m
  have k := nonempty_arrowIso_map_map_kunnethMap
    (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
    φ₁ φ₂ h A₀ B₀ (by exact_mod_proofs hA) (by exact_mod_proofs hB)
    (by exact_mod_proofs hAB)
  exact_mod_proofs k

/-- **The Künneth map and the reduction `𝒪_E ⟶ 𝔽_E`**: for bounded below `𝒪_E`-complexes `A₀`,
`B₀` such that `Lf₁^* A₀ ⊗ᴸ Lf₂^* B₀` is bounded below, `𝔽_E ⊗ᴸ Π_{A₀,B₀}` and
`Π_{𝔽_E ⊗ᴸ A₀, 𝔽_E ⊗ᴸ B₀}` are isomorphic arrows. -/
theorem nonempty_arrowIso_map_kunnethMap_residueField (φ₁ : P.Hom M f₁ f₁')
    (φ₂ : P.Hom N f₂ f₂')
    (A₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (B₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y))) (n m : ℤ) [A₀.IsGE n]
    [B₀.IsGE n]
    [(L((f₁)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A₀ ⊗
      L((f₂)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀).IsGE m] :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap
        (Profinite.padicIntegersRingObjToResidueField ℓ E.1) Z')).leftDerivedFunctor.map
          (kunnethMap (Profinite.padicIntegersRingObj ℓ E.1) φ₁ φ₂ A₀ B₀)) ≅
      Arrow.mk (kunnethMap (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) φ₁ φ₂
          ((Mod.extendScalars (coefficientMap
            (Profinite.padicIntegersRingObjToResidueField ℓ E.1) X)).leftDerivedFunctor.obj A₀)
          ((Mod.extendScalars (coefficientMap
            (Profinite.padicIntegersRingObjToResidueField ℓ E.1) Y)).leftDerivedFunctor.obj
              B₀))) := by
  have := isGE_leftDerivedUpperStar_obj _ M.ε A₀ n
  have := isGE_leftDerivedUpperStar_obj _ N.ε B₀ n
  have := isGE_leftDerivedUpperStar_obj _ P.ε
    (L((f₁)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A₀ ⊗
      L((f₂)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀) m
  have hA := isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E M.j
    (L((M.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A₀) n
  have hB := isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E N.j
    (L((N.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀) n
  have hAB := isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E P.j
    (L((P.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj
      (L((f₁)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj A₀ ⊗
        L((f₂)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀)) m
  have k := nonempty_arrowIso_map_kunnethMap
    (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
    φ₁ φ₂ A₀ B₀ (by exact_mod_proofs hA) (by exact_mod_proofs hB) (by exact_mod_proofs hAB)
  exact_mod_proofs k

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
