/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionConservative
public import WeilConjectures.SmoothPurity.OrientationTransition

/-!
# The canonical orientation of a smooth morphism with `ℚ̄_ℓ`-coefficients

Let `f : X ⟶ Y` be a morphism of separated `k`-schemes of finite type which is smooth of pure
relative dimension `d`. An *orientation* of `f` is an isomorphism
`γ_f : ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` in `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. This file constructs the canonical one
(blueprint `def-pur-smooth-trace`, `det-sp-tower-gamma`).

The canonical finite orientations `Rf^! Λ_Y ≅ Λ_X(d)[2d]`, `Λ = 𝒪_E ⧸ ℓⁿ`, of the diagonal
argument (`Etale.dualizingComplexTwistShiftIso`, blueprint `thm-pur-diagonal-dualizing-object`)
are compatible with the reductions `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ`
(`ProEtale.CondensedRing.derivedExtendScalarsReduction_derivedReductionSmoothOrientation`,
blueprint `det-sp-purity-coefficient-change`). A compatible family of morphisms of reductions
into the derived complete complex `Rf^! 𝒪_{E,Y}` lifts to a morphism
(`ProEtale.exists_derivedReduction_map_eq`), so the finite orientations lift to an integral
morphism `φ₀ : 𝒪_X(d)[2d] ⟶ Rf^! 𝒪_Y` (`ProEtale.CondensedRing.exists_isIntegralSmoothOrientation`),
which is an isomorphism by derived Nakayama. Its extension of scalars to `ℚ̄_ℓ` is the
orientation.

## Main definitions

- `ProEtale.CondensedRing.IsCanonicalSmoothOrientation`: a morphism
  `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` is the extension of scalars of an integral lift of the canonical
  finite orientations.
- `ProEtale.CondensedRing.integralSmoothOrientation`: the integral lift, for `𝒪 = ℤ_ℓ`.
- `ProEtale.CondensedRing.smoothOrientationOfSmooth`: the canonical orientation, an isomorphism
  (`ProEtale.CondensedRing.isIso_smoothOrientationOfSmooth`) satisfying
  `IsCanonicalSmoothOrientation`
  (`ProEtale.CondensedRing.isCanonicalSmoothOrientation_smoothOrientationOfSmooth`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) (d : ℕ)
  [SmoothOfRelativeDimension d f.left]

set_option maxHeartbeats 1000000 in
-- elaborating the lift through the bounded constructible and ambient categories is slow
/-- **The canonical finite orientations lift to an integral isomorphism**
`φ₀ : 𝒪_{E,X}(d)[2d] ≅ Rf^! 𝒪_{E,Y}`: they are compatible with the reductions
(`derivedExtendScalarsReduction_derivedReductionSmoothOrientation`), so they lift to a morphism
into the derived complete complex `Rf^! 𝒪_{E,Y}` (`ProEtale.exists_derivedReduction_map_eq`),
which is an isomorphism as its reduction modulo `ℓ` is (`isIso_of_isIso_etaleReduction_map`). -/
theorem exists_isIntegralSmoothOrientation :
    ∃ φ₀ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _),
      IsIso φ₀ ∧ IsIntegralSmoothOrientation ℓ E f d φ₀ := by
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  let W := (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)
  obtain ⟨g, hg⟩ := ProEtale.exists_derivedReduction_map_eq
    (K := (boundedConstructible _).ι.obj ((shiftFunctor _ (2 * d : ℤ)).obj
      (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)))
    (L := (boundedConstructible _).ι.obj W)
    (derivedCompleteIntegers_of_boundedConstructible W.property)
    (fun n ↦ derivedReductionSmoothOrientation ℓ E f d (n + 1))
    (map_derivedReductionSmoothOrientation_comp_reductionTransition ℓ E f d)
  let φ₀ : (shiftFunctor _ (2 * d : ℤ)).obj
      (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶ W :=
    (ObjectProperty.fullyFaithfulι _).preimage g
  have hred (n : ℕ) : (boundedConstructibleIntegersModPowReduction X.left ℓ E.1 (n + 1)).map φ₀ =
      integersModPowReductionSmoothOrientation ℓ E f d (n + 1) := by
    refine boundedConstructibleIntegersModPowReduction_map_eq_of_leftDerivedFunctor_map_eq
      ℓ E.1 (n + 1) X.left φ₀ _ ?_
    rw [(ObjectProperty.fullyFaithfulι _).map_preimage g]
    exact hg n
  refine ⟨φ₀, ?_, (isIntegralSmoothOrientation_iff ℓ E f d φ₀).2 hred⟩
  refine isIso_of_isIso_etaleReduction_map ℓ E.1 one_ne_zero φ₀ ?_
  change IsIso ((finiteEtaleReading ℓ E.1 1 X).map
    ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 1).map φ₀))
  rw [hred 0]
  infer_instance

/-- Blueprint `def-pur-smooth-trace`, `det-sp-tower-gamma`: a morphism
`φ : ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` is the **canonical orientation** of `f` (smooth of pure relative
dimension `d`) if it is the extension of scalars (`extendScalarsIntegralOrientation`) of a
morphism `φ₀ : 𝒪_X(d)[2d] ⟶ Rf^! 𝒪_Y`, `𝒪 = ℤ_ℓ` the integers of the smallest finite
subextension `ℚ_ℓ` of `ℚ̄_ℓ`, lifting the canonical finite orientations
(`IsIntegralSmoothOrientation`, built from `Etale.dualizingComplexTwistShiftIso`). Such a lift
exists (`exists_isIntegralSmoothOrientation`). -/
def IsCanonicalSmoothOrientation
    (φ : boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) : Prop :=
  ∃ φ₀, IsIntegralSmoothOrientation ℓ ⟨⊥, inferInstance⟩ f d φ₀ ∧
    extendScalarsIntegralOrientation ℓ ⟨⊥, inferInstance⟩ f d φ₀ = φ

/-- The **integral orientation** `ℤ_ℓ,X(d)[2d] ≅ Rf^! ℤ_ℓ,Y` of a morphism `f` smooth of pure
relative dimension `d`: an integral isomorphism lifting the canonical finite orientations
(`exists_isIntegralSmoothOrientation`, for the integers `ℤ_ℓ` of the smallest finite
subextension `ℚ_ℓ` of `ℚ̄_ℓ`). -/
noncomputable def integralSmoothOrientation :
    (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ
        (⊥ : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ _ X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ _ f).obj (𝟙_ _) :=
  (exists_isIntegralSmoothOrientation ℓ ⟨⊥, inferInstance⟩ f d).choose

instance isIso_integralSmoothOrientation : IsIso (integralSmoothOrientation ℓ f d) :=
  (exists_isIntegralSmoothOrientation ℓ ⟨⊥, inferInstance⟩ f d).choose_spec.1

lemma isIntegralSmoothOrientation_integralSmoothOrientation :
    IsIntegralSmoothOrientation ℓ ⟨⊥, inferInstance⟩ f d (integralSmoothOrientation ℓ f d) :=
  (exists_isIntegralSmoothOrientation ℓ ⟨⊥, inferInstance⟩ f d).choose_spec.2

/-- The **canonical orientation** `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` of a morphism `f` smooth of pure
relative dimension `d`: the extension of scalars to `ℚ̄_ℓ` of the integral orientation
`integralSmoothOrientation`, which lifts the canonical finite orientations of the diagonal
argument. -/
noncomputable def smoothOrientationOfSmooth :
    boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  extendScalarsIntegralOrientation ℓ ⟨⊥, inferInstance⟩ f d (integralSmoothOrientation ℓ f d)

/-- The orientation of a smooth morphism is an isomorphism. -/
instance isIso_smoothOrientationOfSmooth : IsIso (smoothOrientationOfSmooth ℓ f d) := by
  rw [smoothOrientationOfSmooth]
  infer_instance

/-- The orientation `smoothOrientationOfSmooth` is the canonical orientation. -/
theorem isCanonicalSmoothOrientation_smoothOrientationOfSmooth :
    IsCanonicalSmoothOrientation ℓ f d (smoothOrientationOfSmooth ℓ f d) :=
  ⟨_, isIntegralSmoothOrientation_integralSmoothOrientation ℓ f d, rfl⟩

end AlgebraicGeometry.ProEtale.CondensedRing
