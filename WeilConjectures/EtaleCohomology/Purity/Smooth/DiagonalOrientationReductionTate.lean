/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionSupports

/-!
# The Tate data of the reduction of coefficients

Let `ρ : Λ →+* Λ'` be a surjective morphism of finite coefficient rings with principal kernel,
with characteristics `n = n' k` (for instance the reduction `𝒪_E ⧸ ℓⁿ⁺² ⟶ 𝒪_E ⧸ ℓⁿ⁺¹`, with
`k = ℓ`), and `Ψ` the derived extension of scalars along `ρ`. The change of coefficients of the
Tate twists `Λ_X(1) ⟶ Res Λ'_X(1)` (the `k`-th power map) is adjoint to an isomorphism
`σ_X : Ψ(Λ_X(1)) ≅ Λ'_X(1)` (`AlgebraicGeometry.Etale.reductionTateTwistOneIso`). Since `Ψ` is
monoidal and the Tate twists form coherent integer tensor families, `σ_X` extends uniquely to a
multiplicative family `Ψ(Λ_X(m)) ≅ Λ'_X(m)` (`AlgebraicGeometry.Etale.reductionTateTwistIso`),
and, shifting, to the Tate data `Ψ(Λ_X(m)[2m]) ≅ Λ'_X(m)[2m]` of the reduction
(`AlgebraicGeometry.Etale.reductionTateShiftData`, blueprint `det-sp-purity-coefficient-change`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory


open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})
  [NeZero (ringChar Λ)] [NeZero (ringChar Λ')] (k : ℕ) (hk : ringChar Λ = ringChar Λ' * k)

section Twist

variable (X : Scheme.{u}) [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X]

/-- The reduction of the Tate twist `Λ_X(1)`: the isomorphism `σ_X : Ψ(Λ_X(1)) ≅ Λ'_X(1)`
adjoint to the change of coefficients `Λ_X(1) ⟶ Res Λ'_X(1)` of the Tate twists
(`AlgebraicGeometry.Etale.tateTwistObjectOneChangeMap`, the `k`-th power map). -/
noncomputable def reductionTateTwistOneIso :
    (derivedExtendScalars hρ ha X).obj (tateTwistObject Λ X 1) ≅ tateTwistObject Λ' X 1 :=
  have := isIso_homEquiv_symm_tateTwistObjectOneChangeMap hρ ha X k hk
  asIso (((derivedExtendScalarsAdjunction hρ ha X).homEquiv _ _).symm
    (tateTwistObjectOneChangeMap ρ X k hk))

lemma reductionTateTwistOneIso_hom :
    (reductionTateTwistOneIso hρ ha k hk X).hom =
      ((derivedExtendScalarsAdjunction hρ ha X).homEquiv _ _).symm
        (tateTwistObjectOneChangeMap ρ X k hk) :=
  rfl

end Twist

section Data

variable (σ : ∀ (X : Scheme.{u}) [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] (m : ℤ),
    (derivedExtendScalars hρ ha X).obj (tateObject Λ X m) ≅ tateObject Λ' X m)

/-- The identifications `Ψ(Λ_X(m)[2m]) ≅ Ψ(Λ_X(m))[2m] ≅ Λ'_X(m)[2m]` attached to a family of
identifications `σ_{X,m} : Ψ(Λ_X(m)) ≅ Λ'_X(m)`, through the commutation of `Ψ` with the
shifts. -/
noncomputable def reductionTateShiftIso (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ' X] (m : ℤ) :
    (derivedExtendScalars hρ ha X).obj ((tateObject Λ X m)⟦2 * m⟧) ≅ (tateObject Λ' X m)⟦2 * m⟧ :=
  ((derivedExtendScalars hρ ha X).commShiftIso (2 * m)).app _ ≪≫
    (shiftFunctor _ (2 * m)).mapIso (σ X m)

/-- The identifications `Ψ(Λ_X(m)[2m]) ≅ Λ'_X(m)[2m]` attached to a family `σ` compatible with
the derived pullbacks are compatible with the derived pullbacks: this follows from the
compatibility of the commutations of `Ψ` and of `Le^*` with the shifts. -/
theorem reductionTateShiftIso_pullback
    (hσ : ∀ {U X : Scheme.{u}} [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ X]
      [HasInvertibleExponent Λ' U] [HasInvertibleExponent Λ' X] (e : U ⟶ X) (m : ℤ),
      (derivedExtendScalars hρ ha U).map (leftDerivedUpperStarTateObjectIso e m).hom ≫
          (σ U m).hom =
        (derivedExtendScalarsPullbackIso hρ ha e).hom.app _ ≫
          (L((e)^*[ModuleCat.{u + 1} Λ'])).map (σ X m).hom ≫
            (leftDerivedUpperStarTateObjectIso e m).hom)
    {U X : Scheme.{u}} [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ' U] [HasInvertibleExponent Λ' X] (e : U ⟶ X) (m : ℤ) :
    (derivedExtendScalars hρ ha U).map (leftDerivedUpperStarTateShiftIso Λ e m).hom ≫
        (reductionTateShiftIso hρ ha σ U m).hom =
      (derivedExtendScalarsPullbackIso hρ ha e).hom.app _ ≫
        (L((e)^*[ModuleCat.{u + 1} Λ'])).map (reductionTateShiftIso hρ ha σ X m).hom ≫
          (leftDerivedUpperStarTateShiftIso Λ' e m).hom := by
  sorry

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The Tate data of the reduction of coefficients** attached to a family of identifications
`σ_{X,m} : Ψ(Λ_X(m)) ≅ Λ'_X(m)` compatible with the derived pullbacks: the identifications
`Ψ(Λ_X(m)[2m]) ≅ Λ'_X(m)[2m]` (`AlgebraicGeometry.Etale.reductionTateShiftIso`). -/
noncomputable def reductionTateShiftData
    (hσ : ∀ {U X : Scheme.{u}} [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ X]
      [HasInvertibleExponent Λ' U] [HasInvertibleExponent Λ' X] (e : U ⟶ X) (m : ℤ),
      (derivedExtendScalars hρ ha U).map (leftDerivedUpperStarTateObjectIso e m).hom ≫
          (σ U m).hom =
        (derivedExtendScalarsPullbackIso hρ ha e).hom.app _ ≫
          (L((e)^*[ModuleCat.{u + 1} Λ'])).map (σ X m).hom ≫
            (leftDerivedUpperStarTateObjectIso e m).hom) :
    DerivedExtendScalarsTateShiftData Λ Λ' hρ ha where
  iso X _ _ m := reductionTateShiftIso hρ ha σ X m
  map_leftDerivedUpperStarTateShiftIso e m := reductionTateShiftIso_pullback hρ ha σ hσ e m

/-- In degree one, the Tate data `reductionTateShiftData` are the commutation of `Ψ` with the
shift followed by the shift of `σ_{X,1}`; for `σ_{X,1} = σ_X`
(`AlgebraicGeometry.Etale.reductionTateTwistOneIso`) this is the formula
`(τ.iso X 1).hom = (Ψ.commShiftIso (2 * 1)).hom.app _ ≫ (σ X).hom⟦2 * 1⟧'`. -/
lemma reductionTateShiftData_iso_hom (hσ) (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ' X] (m : ℤ) :
    ((reductionTateShiftData hρ ha σ hσ).iso X m).hom =
      ((derivedExtendScalars hρ ha X).commShiftIso (2 * m)).hom.app _ ≫ (σ X m).hom⟦2 * m⟧' :=
  rfl


variable [Finite Λ] [Finite Λ'] in
/-- The hypothesis `hunit` of
`AlgebraicGeometry.Etale.MonoidalSupportedCoefficientChange.preservesKummerBoundaries` for the
reduction of coefficients with the Tate data `reductionTateShiftData`, provided `σ_{U,0}` is,
through `Λ(0) ≅ Λ`, the identification `Ψ Λ_U ≅ Λ'_U`. -/
theorem reductionSupportedCoefficientChange_unit (hσ)
    (hσ₀ : ∀ (U : Scheme.{u}) [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U],
      (derivedExtendScalars hρ ha U).map (HasTateTwist.twistObjectZeroIso (Λ := Λ) U).hom ≫
          (derivedExtendScalarsConstantComplexIso hρ ha U).hom =
        (σ U 0).hom ≫ (HasTateTwist.twistObjectZeroIso (Λ := Λ') U).hom)
    (U : Scheme.{u}) [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U] :
    ((reductionSupportedCoefficientChange hρ ha (reductionTateShiftData hρ ha σ hσ)).functor U).map
        ((HasTateTwist.twistObjectZeroIso (Λ := Λ) U).inv ≫
          (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _) ≫
        ((reductionSupportedCoefficientChange hρ ha
          (reductionTateShiftData hρ ha σ hσ)).tateShiftIso U 0).hom =
      ((reductionSupportedCoefficientChange hρ ha
          (reductionTateShiftData hρ ha σ hσ)).constantComplexIso U).hom ≫
        (HasTateTwist.twistObjectZeroIso (Λ := Λ') U).inv ≫
          (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _ := by
  sorry
end Data

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})
  [NeZero (ringChar Λ)] [NeZero (ringChar Λ')] (k : ℕ) (hk : ringChar Λ = ringChar Λ' * k)

/-- The reduction `σ_X : Ψ(Λ_X(1)) ≅ Λ'_X(1)` of the Tate twist is compatible with the derived
pullbacks. -/
theorem reductionTateTwistOneIso_pullback {U X : Scheme.{u}} [HasInvertibleExponent Λ U]
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' U] [HasInvertibleExponent Λ' X]
    (e : U ⟶ X) :
    (derivedExtendScalars hρ ha U).map (leftDerivedUpperStarTateObjectIso e 1).hom ≫
        (reductionTateTwistOneIso hρ ha k hk U).hom =
      (derivedExtendScalarsPullbackIso hρ ha e).hom.app _ ≫
        (L((e)^*[ModuleCat.{u + 1} Λ'])).map (reductionTateTwistOneIso hρ ha k hk X).hom ≫
          (leftDerivedUpperStarTateObjectIso e 1).hom := by
  sorry

end AlgebraicGeometry.Etale
