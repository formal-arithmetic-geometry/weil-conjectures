/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientation
public import WeilConjectures.SmoothPurity.IntegralTateTwistExtendScalars
public import WeilConjectures.SmoothPurity.UpperShriekUnitDualizable

/-!
# The finite orientations of a smooth morphism, read on integral coefficients

Let `f : X ⟶ Y` be a morphism of separated `k`-schemes of finite type which is smooth of pure
relative dimension `d`, and `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`.
This file states what it means for an integral morphism `φ₀ : 𝒪_X(d)[2d] ⟶ Rf^! 𝒪_Y` to lift the
canonical finite orientations:

- `ProEtale.CondensedRing.etaleReductionSmoothOrientationIso`: the canonical finite orientation
  modulo `ℓⁿ`, between the reductions of `𝒪_X(d)[2d]` and of `Rf^! 𝒪_Y` read on the small étale
  site: the inverse of the orientation `Rf^! Λ_Y ≅ Λ_X(d)[2d]`, `Λ = 𝒪_E ⧸ ℓⁿ`, of the diagonal
  argument (`Etale.dualizingComplexTwistShiftIso`, blueprint `thm-pur-diagonal-dualizing-object`),
  through the canonical reduction comparisons.
- `ProEtale.CondensedRing.IsIntegralSmoothOrientation`: the reductions of `φ₀` modulo `ℓⁿ`,
  `n ≥ 1`, are the canonical finite orientations.
- `ProEtale.CondensedRing.extendScalarsIntegralOrientation`: the extension of scalars of `φ₀`
  to `ℚ̄_ℓ`, a morphism `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`.
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

/-- The reduction modulo `ℓⁿ` of bounded constructible `𝒪_E`-complexes commutes with the shifts:
`red_n (K[m]) ≅ (red_n K)[m]`, read in the ambient derived categories, where the derived
extension of scalars commutes with the shifts. -/
noncomputable def boundedConstructibleIntegersModPowReductionShiftIso
    (K : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E⟧) (m : ℤ) :
    (boundedConstructibleIntegersModPowReduction X ℓ E n).obj ((shiftFunctor _ m).obj K) ≅
      (shiftFunctor _ m).obj ((boundedConstructibleIntegersModPowReduction X ℓ E n).obj K) :=
  let ι := (boundedConstructible
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)).ι
  let ιn := (boundedConstructible (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)).ι
  let Lred := (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((boundedConstructibleIntegersModPowReductionCompatibility X ℓ E n).app _ ≪≫
      Lred.mapIso ((ι.commShiftIso m).app K) ≪≫ (Lred.commShiftIso m).app (ι.obj K) ≪≫
      (shiftFunctor _ m).mapIso
        ((boundedConstructibleIntegersModPowReductionCompatibility X ℓ E n).app K).symm ≪≫
      ((ιn.commShiftIso m).app _).symm)

/-- A morphism `t : red_n K ⟶ red_n L` of reductions modulo `ℓⁿ` of bounded constructible
`𝒪_E`-complexes, read between the derived reductions `(𝒪_E ⧸ ℓⁿ) ⊗ᴸ K ⟶ (𝒪_E ⧸ ℓⁿ) ⊗ᴸ L` in the
ambient derived categories, through `boundedConstructibleIntegersModPowReductionCompatibility`. -/
noncomputable def derivedReductionMap {K L : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E⟧}
    (t : (boundedConstructibleIntegersModPowReduction X ℓ E n).obj K ⟶
      (boundedConstructibleIntegersModPowReduction X ℓ E n).obj L) :
    (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor.obj
        ((boundedConstructible _).ι.obj K) ⟶
      (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor.obj
        ((boundedConstructible _).ι.obj L) :=
  ((boundedConstructibleIntegersModPowReductionCompatibility X ℓ E n).app K).inv ≫
    (boundedConstructible _).ι.map t ≫
    ((boundedConstructibleIntegersModPowReductionCompatibility X ℓ E n).app L).hom

/-- A morphism `φ` of bounded constructible `𝒪_E`-complexes has reduction `t` modulo `ℓⁿ` as soon
as the derived reduction of `φ` in the ambient derived categories is `derivedReductionMap t`. -/
lemma boundedConstructibleIntegersModPowReduction_map_eq_of_leftDerivedFunctor_map_eq
    {K L : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E⟧} (φ : K ⟶ L)
    (t : (boundedConstructibleIntegersModPowReduction X ℓ E n).obj K ⟶
      (boundedConstructibleIntegersModPowReduction X ℓ E n).obj L)
    (h : (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor.map
        ((boundedConstructible _).ι.map φ) = derivedReductionMap ℓ E n X t) :
    (boundedConstructibleIntegersModPowReduction X ℓ E n).map φ = t := by
  apply (ObjectProperty.fullyFaithfulι _).map_injective
  have hn := (boundedConstructibleIntegersModPowReductionCompatibility X ℓ E n).hom.naturality φ
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [← cancel_mono ((boundedConstructibleIntegersModPowReductionCompatibility X ℓ E n).app L).hom,
    Iso.app_hom, hn, ← Iso.app_hom, h, derivedReductionMap, Iso.hom_inv_id_assoc]
  rfl

end Reduction

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) (d : ℕ)

/-- The **extension of scalars** to `ℚ̄_ℓ` of a morphism `φ₀ : 𝒪_{E,X}(d)[2d] ⟶ Rf^! 𝒪_{E,Y}`:
the morphism `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` obtained by applying the extension of scalars `T`
along `𝒪_E ⟶ E ⟶ ℚ̄_ℓ` and the comparisons `T(𝒪_{E,X}(d)[2d]) ≅ ℚ̄_ℓ,X(d)[2d]`
(`extendScalarsIntegralTateTwistBoundedConstructibleIso`) and `T(Rf^! 𝒪_{E,Y}) ≅ Rf^! ℚ̄_ℓ,Y`
(`integersToPadicAlgClUpperShriekUnitIso`). -/
noncomputable def extendScalarsIntegralOrientation
    (φ₀ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)) :
    boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  (extendScalarsIntegralTateTwistBoundedConstructibleIso ℓ E X d (2 * d)).inv ≫
    (boundedConstructibleExtendScalars X.left ℓ E ⋙ constructibleToPadicAlgCl X.left ℓ E).map φ₀ ≫
    (integersToPadicAlgClUpperShriekUnitIso ℓ E f).hom

/-- The extension of scalars of an isomorphism is an isomorphism. -/
instance isIso_extendScalarsIntegralOrientation
    (φ₀ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)) [IsIso φ₀] :
    IsIso (extendScalarsIntegralOrientation ℓ E f d φ₀) := by
  rw [extendScalarsIntegralOrientation]
  infer_instance
/-- The **canonical finite orientation**, read on the small étale site: modulo `ℓⁿ`, the
reductions of the shifted integral Tate twist `𝒪_{E,X}(d)[2d]` and of the integral relative
dualizing complex `Rf^! 𝒪_{E,Y}` are identified, through the canonical comparisons
`etaleReductionIntegralTateTwistIso`, `etaleReductionUpperShriekIso` and `etaleReductionUnitIso`,
with `Λ_X(d)[2d]` and `Rf^! Λ_Y`, `Λ = 𝒪_E ⧸ ℓⁿ`, and the isomorphism is the inverse of the
orientation `Rf^! Λ_Y ≅ Λ_X(d)[2d]` of the diagonal argument (`Etale.dualizingComplexTwistShiftIso`,
for the Kummer classes of `μ_{ℓⁿ} ⊗ Λ`, blueprint `thm-pur-diagonal-dualizing-object`). -/
noncomputable def etaleReductionSmoothOrientationIso (n : ℕ) [SmoothOfRelativeDimension d f.left] :
    (shiftFunctor _ (2 * d : ℤ)).obj ((finiteEtaleReading ℓ E.1 n X).obj
        ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj
          (integralTateTwistBoundedConstructible ℓ E.1 X.hom d))) ≅
      (finiteEtaleReading ℓ E.1 n X).obj
        ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj
          ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _))) :=
  haveI := HasCompactification.of_over f
  haveI : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 n) X.left :=
    HasInvertibleExponent.of_hom X.hom
  haveI : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 n) Y.left :=
    HasInvertibleExponent.of_hom Y.hom
  (shiftFunctor _ (2 * d : ℤ)).mapIso
      (etaleReductionIntegralTateTwistIso ℓ E.1 n X d ≪≫ (λ_ _).symm) ≪≫
    (Etale.dualizingComplexTwistShiftIso (integersModPowCoeff.{u} ℓ E.1 n) f.left d
      Y.hom).symm ≪≫
    ((etaleReductionUpperShriekIso ℓ E.1 n f).app (𝟙_ _) ≪≫
      (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E.1 n) f.left).mapIso
        (etaleReductionUnitIso ℓ E.1 n Y)).symm

/-- The **canonical finite orientation modulo `ℓⁿ`**, between the étale readings of the
reductions of `𝒪_{E,X}(d)[2d]` and of `Rf^! 𝒪_{E,Y}`: the canonical finite orientation
`etaleReductionSmoothOrientationIso`, through the commutation of the reduction and of the reading
with the shift. -/
noncomputable def finiteEtaleReadingSmoothOrientation (n : ℕ)
    [SmoothOfRelativeDimension d f.left] :
    (finiteEtaleReading ℓ E.1 n X).obj
      ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj
        ((shiftFunctor _ (2 * d : ℤ)).obj (integralTateTwistBoundedConstructible ℓ E.1 X.hom d))) ⟶
      (finiteEtaleReading ℓ E.1 n X).obj
        ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _))) :=
  (finiteEtaleReading ℓ E.1 n X).map
      (boundedConstructibleIntegersModPowReductionShiftIso ℓ E.1 n X.left _ (2 * d : ℤ)).hom ≫
    ((finiteEtaleReading ℓ E.1 n X).commShiftIso (2 * d : ℤ)).hom.app _ ≫
    (etaleReductionSmoothOrientationIso ℓ E f d n).hom

instance isIso_finiteEtaleReadingSmoothOrientation (n : ℕ)
    [SmoothOfRelativeDimension d f.left] :
    IsIso (finiteEtaleReadingSmoothOrientation ℓ E f d n) := by
  rw [finiteEtaleReadingSmoothOrientation]
  infer_instance

/-- A morphism `φ₀ : 𝒪_{E,X}(d)[2d] ⟶ Rf^! 𝒪_{E,Y}` **lifts the canonical finite orientations**
if for every `n ≥ 1` its reduction modulo `ℓⁿ`, read on the small étale site, is the canonical
finite orientation (`finiteEtaleReadingSmoothOrientation`). Such a lift is unique: a morphism
into the derived complete complex `Rf^! 𝒪_{E,Y}` is determined by its reductions
(`ProEtale.existsUnique_derivedReduction_map_eq`), which are determined by their étale readings,
the reading being fully faithful. -/
def IsIntegralSmoothOrientation [SmoothOfRelativeDimension d f.left]
    (φ₀ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)) : Prop :=
  ∀ n : ℕ, (finiteEtaleReading ℓ E.1 (n + 1) X).map
      ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 (n + 1)).map φ₀) =
    finiteEtaleReadingSmoothOrientation ℓ E f d (n + 1)

end AlgebraicGeometry.ProEtale.CondensedRing
