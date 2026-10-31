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

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

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

/-- The reduction of the Tate twists `Ψ(Λ_X(m)) ≅ Λ'_X(m)`: the multiplicative extension, along
the monoidal functor `Ψ`, of the reduction `σ_X` of `Λ_X(1)`
(`CategoryTheory.MonoidalCategory.IntTensorFamily.iso`). -/
noncomputable def reductionTateTwistIso (m : ℤ) :
    (derivedExtendScalars hρ ha X).obj (tateTwistObject Λ X m) ≅ tateTwistObject Λ' X m :=
  haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
  letI := (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorMonoidal
  IntTensorFamily.iso ((tateTwistIntTensorFamily Λ X).map
      (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctor)
    (tateTwistIntTensorFamily Λ' X) (reductionTateTwistOneIso hρ ha k hk X) m

/-- In degree one, the reduction of the Tate twists is `σ_X`. -/
lemma reductionTateTwistIso_one :
    reductionTateTwistIso hρ ha k hk X 1 = reductionTateTwistOneIso hρ ha k hk X :=
  IntTensorFamily.iso_one _ _ _

end Twist

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The Tate data of the reduction of coefficients**: `Ψ(Λ_X(m)[2m]) ≅ Ψ(Λ_X(m))[2m] ≅ Λ'_X(m)[2m]`,
through the commutation of `Ψ` with the shifts and the reduction of the Tate twists
(`AlgebraicGeometry.Etale.reductionTateTwistIso`). -/
noncomputable def reductionTateShiftIso (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ' X] (m : ℤ) :
    (derivedExtendScalars hρ ha X).obj ((tateObject Λ X m)⟦2 * m⟧) ≅ (tateObject Λ' X m)⟦2 * m⟧ :=
  ((derivedExtendScalars hρ ha X).commShiftIso (2 * m)).app _ ≪≫
    (shiftFunctor _ (2 * m)).mapIso (reductionTateTwistIso hρ ha k hk X m)

/-- The Tate data of the reduction are compatible with the derived pullbacks. -/
theorem reductionTateShiftIso_pullback {U X : Scheme.{u}} [HasInvertibleExponent Λ U]
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' U] [HasInvertibleExponent Λ' X]
    (e : U ⟶ X) (m : ℤ) :
    (derivedExtendScalars hρ ha U).map (leftDerivedUpperStarTateShiftIso Λ e m).hom ≫
        (reductionTateShiftIso hρ ha k hk U m).hom =
      (derivedExtendScalarsPullbackIso hρ ha e).hom.app _ ≫
        (L((e)^*[ModuleCat.{u + 1} Λ'])).map (reductionTateShiftIso hρ ha k hk X m).hom ≫
          (leftDerivedUpperStarTateShiftIso Λ' e m).hom := by
  sorry

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The Tate data of the reduction of coefficients** `Ψ(Λ_X(m)[2m]) ≅ Λ'_X(m)[2m]`
(`AlgebraicGeometry.Etale.reductionTateShiftIso`), for the Tate twists of `Λ` and `Λ'`. -/
noncomputable def reductionTateShiftData : DerivedExtendScalarsTateShiftData Λ Λ' hρ ha where
  iso X _ _ m := reductionTateShiftIso hρ ha k hk X m
  map_leftDerivedUpperStarTateShiftIso e m := reductionTateShiftIso_pullback hρ ha k hk e m

/-- In degree one, the Tate data of the reduction are the commutation of `Ψ` with the shift
followed by the shift of `σ_X : Ψ(Λ_X(1)) ≅ Λ'_X(1)`. -/
lemma reductionTateShiftData_iso_one_hom (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ' X] :
    ((reductionTateShiftData hρ ha k hk).iso X 1).hom =
      ((derivedExtendScalars hρ ha X).commShiftIso (2 * 1)).hom.app _ ≫
        (reductionTateTwistOneIso hρ ha k hk X).hom⟦2 * 1⟧' := by
  simp only [reductionTateShiftData, reductionTateShiftIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, reductionTateTwistIso_one]
  rfl

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
