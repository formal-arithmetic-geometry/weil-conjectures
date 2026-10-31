/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.OrientationCanonical

/-!
# Uniqueness of the integral lift of the finite orientations

Let `f : X ⟶ Y` be a morphism of separated `k`-schemes of finite type which is smooth of pure
relative dimension `d`, `T = 𝒪_{E,X}(d)[2d]` and `W = Rf^! 𝒪_{E,Y}`. A morphism `φ₀ : T ⟶ W`
lifting the canonical finite orientations (`ProEtale.CondensedRing.IsIntegralSmoothOrientation`)
is unique (`ProEtale.CondensedRing.IsIntegralSmoothOrientation.eq`): `W` is derived complete, so
a morphism into it is determined by its reductions as soon as the groups
`Hom(T[1], red_n W)` vanish (the `lim¹` term of the Milnor sequence). They do: `W ≅ T` by the
integral orientation, and `T[1]` is concentrated in degree `-2d - 1` while `red_n T` is
concentrated in degree `-2d`, the twist `𝒪_{E,X}(d)` being flat.

Consequently the canonical orientation `smoothOrientationOfSmooth` is the only canonical
orientation (`ProEtale.CondensedRing.smoothOrientationOfSmooth_eq_of_isCanonicalSmoothOrientation`):
to identify it with a given morphism it suffices to exhibit an integral lift of the finite
orientations extending to it.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Reduction

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]

/-- The derived reduction of a morphism `φ` of bounded constructible `𝒪_E`-complexes is the
reading `derivedReductionMap` of its reduction, through
`boundedConstructibleIntegersModPowReductionCompatibility`. -/
lemma leftDerivedFunctor_map_eq_derivedReductionMap
    {K L : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E⟧} (φ : K ⟶ L) :
    (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor.map
        ((boundedConstructible _).ι.map φ) =
      derivedReductionMap ℓ E n X
        ((boundedConstructibleIntegersModPowReduction X ℓ E n).map φ) := by
  have hn := (boundedConstructibleIntegersModPowReductionCompatibility X ℓ E n).hom.naturality φ
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [derivedReductionMap, ← Iso.app_hom, ← Iso.app_hom] at *
  rw [hn, Iso.inv_hom_id_assoc]

end Reduction

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) (d : ℕ)
  [SmoothOfRelativeDimension d f.left]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The derived reduction modulo `ℓⁿ` of the shifted integral Tate twist `𝒪_{E,X}(d)[2d]` is
concentrated in degree `-2d`: it is `((𝒪_E ⧸ ℓⁿ) ⊗ 𝒪_{E,X}(d))[2d]`, the twist being flat. -/
lemma isGE_leftDerivedFunctor_obj_integralTateTwist (n : ℕ) :
    ((Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).leftDerivedFunctor.obj
      ((boundedConstructible _).ι.obj ((shiftFunctor _ (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)))).IsGE (-(2 * d : ℤ)) := by
  let Lred := (Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).leftDerivedFunctor
  let ι := (boundedConstructible
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)).ι
  have : DerivedCategory.TStructure.t.IsGE ((shiftFunctor _ (2 * d : ℤ)).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).obj
          (integralTateTwistNat X.left ℓ E.1 d)))) (-(2 * d : ℤ)) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 _ _ (by lia)
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((Lred.mapIso ((ι.commShiftIso (2 * d : ℤ)).app _) ≪≫ (Lred.commShiftIso (2 * d : ℤ)).app _ ≪≫
      (shiftFunctor _ (2 * d : ℤ)).mapIso (Functor.leftDerivedFunctorSingleFunctorIsoOfFlat _
        (isLocallyFree_integralTateTwistNat ℓ E.1 X.hom d).flat)).symm) _

set_option maxHeartbeats 2000000 in
-- the instances of the t-structure are found up to unfolding the bounded constructible subcategory
omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The shifted integral Tate twist `𝒪_{E,X}(d)[2d]`, shifted once more, is concentrated in
degree `-2d - 1`. -/
lemma isLE_shift_one_integralTateTwist :
    ((shiftFunctor (DerivedCategory (Mod (Sheaf (ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left))) (1 : ℤ)).obj
      ((boundedConstructible _).ι.obj ((shiftFunctor _ (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)))).IsLE
      (-(2 * d : ℤ) - 1) := by
  let ι := (boundedConstructible
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)).ι
  have : DerivedCategory.TStructure.t.IsLE ((ι ⋙ shiftFunctor _ (2 * d : ℤ)).obj
      (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)) (-(2 * d : ℤ)) :=
    DerivedCategory.TStructure.t.isLE_shift
      ((DerivedCategory.singleFunctor _ 0).obj (integralTateTwistNat X.left ℓ E.1 d)) 0 _ _
      (by lia)
  have : DerivedCategory.TStructure.t.IsLE (ι.obj ((shiftFunctor _ (2 * d : ℤ)).obj
      (integralTateTwistBoundedConstructible ℓ E.1 X.hom d))) (-(2 * d : ℤ)) :=
    DerivedCategory.TStructure.t.isLE_of_iso ((ι.commShiftIso (2 * d : ℤ)).app _).symm _
  exact DerivedCategory.TStructure.t.isLE_shift (ι.obj ((shiftFunctor _ (2 * d : ℤ)).obj
    (integralTateTwistBoundedConstructible ℓ E.1 X.hom d))) (-(2 * d : ℤ)) 1 _ (by lia)

set_option maxHeartbeats 2000000 in
-- the instances of the t-structure are found up to unfolding the bounded constructible subcategory
/-- The reductions of `Rf^! 𝒪_{E,Y}` have no morphisms from `𝒪_{E,X}(d)[2d + 1]`: through the
integral orientation `Rf^! 𝒪_{E,Y} ≅ 𝒪_{E,X}(d)[2d]`, the source is concentrated in degree
`-2d - 1` and the target in degrees `≥ -2d`. -/
lemma subsingleton_shift_one_integralTateTwist_hom_upperShriek (n : ℕ) :
    Subsingleton ((shiftFunctor (DerivedCategory (Mod (Sheaf (ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left))) (1 : ℤ)).obj
        ((boundedConstructible _).ι.obj
        ((shiftFunctor _ (2 * d : ℤ)).obj (integralTateTwistBoundedConstructible ℓ E.1 X.hom d))) ⟶
      (Mod.comap (integersModPowReduction X.left ℓ E.1 n)).mapDerivedCategory.obj
        ((Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).leftDerivedFunctor.obj
          ((boundedConstructible _).ι.obj
            ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _))))) := by
  obtain ⟨ψ, hψ, -⟩ := exists_isIntegralSmoothOrientation ℓ E f d
  have := isGE_leftDerivedFunctor_obj_integralTateTwist ℓ (X := X) E d n
  have := isLE_shift_one_integralTateTwist ℓ (X := X) E d
  have : DerivedCategory.TStructure.t.IsGE
      ((Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).leftDerivedFunctor.obj
        ((boundedConstructible _).ι.obj
          ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _))))
      (-(2 * d : ℤ)) :=
    DerivedCategory.TStructure.t.isGE_of_iso
      ((Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).leftDerivedFunctor.mapIso
        ((boundedConstructible _).ι.mapIso (asIso ψ))) _
  have := Functor.isGE_mapDerivedCategory_obj
    (Mod.comap (integersModPowReduction X.left ℓ E.1 n))
    ((Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).leftDerivedFunctor.obj
      ((boundedConstructible _).ι.obj
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _))))
    (-(2 * d : ℤ))
  exact ⟨fun a b ↦ (DerivedCategory.TStructure.t.zero a (-(2 * d : ℤ) - 1) (-(2 * d : ℤ))).trans
    (DerivedCategory.TStructure.t.zero b (-(2 * d : ℤ) - 1) (-(2 * d : ℤ))).symm⟩

/-- **Uniqueness of the integral lift of the finite orientations**: two morphisms
`𝒪_{E,X}(d)[2d] ⟶ Rf^! 𝒪_{E,Y}` lifting the canonical finite orientations are equal. The
target is derived complete, and the `lim¹` obstruction `Hom(𝒪_{E,X}(d)[2d + 1], red_n Rf^! 𝒪_E)`
vanishes (`subsingleton_shift_one_integralTateTwist_hom_upperShriek`). -/
theorem IsIntegralSmoothOrientation.eq
    {φ₀ φ₁ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)}
    (h₀ : IsIntegralSmoothOrientation ℓ E f d φ₀) (h₁ : IsIntegralSmoothOrientation ℓ E f d φ₁) :
    φ₀ = φ₁ := by
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  have (n : ℕ) := subsingleton_shift_one_integralTateTwist_hom_upperShriek ℓ E f d (n + 1)
  have hred {φ} (h : IsIntegralSmoothOrientation ℓ E f d φ) (n : ℕ) :
      (Mod.extendScalars (integersModPowReduction X.left ℓ E.1 (n + 1))).leftDerivedFunctor.map
        ((boundedConstructible _).ι.map φ) =
        derivedReductionSmoothOrientation ℓ E f d (n + 1) := by
    exact (leftDerivedFunctor_map_eq_derivedReductionMap ℓ E.1 (n + 1) X.left φ).trans
      (congrArg (derivedReductionMap ℓ E.1 (n + 1) X.left)
        ((isIntegralSmoothOrientation_iff ℓ E f d φ).1 h n))
  refine (ObjectProperty.fullyFaithfulι _).map_injective
    (ProEtale.eq_of_comp_unit_eq (L := (boundedConstructible _).ι.obj
      ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)))
      (derivedCompleteIntegers_of_boundedConstructible
      ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)).property)
      fun n ↦ ?_)
  exact ((derivedReduction_map_eq_iff (n + 1) _ _).1 (hred h₀ n)).trans
    ((derivedReduction_map_eq_iff (n + 1) _ _).1 (hred h₁ n)).symm

/-- The integral orientation `integralSmoothOrientation` is the only integral lift of the
canonical finite orientations. -/
theorem eq_integralSmoothOrientation_of_isIntegralSmoothOrientation
    {φ₀ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ
        (⊥ : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ _ X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ _ f).obj (𝟙_ _)}
    (h : IsIntegralSmoothOrientation ℓ ⟨⊥, inferInstance⟩ f d φ₀) :
    φ₀ = integralSmoothOrientation ℓ f d :=
  h.eq ℓ _ f d (isIntegralSmoothOrientation_integralSmoothOrientation ℓ f d)

/-- Blueprint `det-sp-tower-gamma`: **the canonical orientation is unique**: a morphism
`ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` satisfying `IsCanonicalSmoothOrientation` is
`smoothOrientationOfSmooth`, the integral lift of the finite orientations being unique
(`IsIntegralSmoothOrientation.eq`). -/
theorem smoothOrientationOfSmooth_eq_of_isCanonicalSmoothOrientation
    {φ : boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))}
    (h : IsCanonicalSmoothOrientation ℓ f d φ) :
    smoothOrientationOfSmooth ℓ f d = φ := by
  obtain ⟨φ₀, h₀, rfl⟩ := h
  rw [smoothOrientationOfSmooth,
    eq_integralSmoothOrientation_of_isIntegralSmoothOrientation ℓ f d h₀]

end AlgebraicGeometry.ProEtale.CondensedRing
