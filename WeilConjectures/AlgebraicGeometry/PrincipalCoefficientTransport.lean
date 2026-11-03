/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Reduction
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.AlgebraicGeometry.CoefficientChange.CoefficientTransformationComparisons
public import WeilConjectures.AlgebraicGeometry.PrincipalCoefficient.PrincipalCoefficientExceptional

/-! # Transporting principal comparisons to universal reductions

Universal derived base changes are unique up to their adjunction-compatible
isomorphism. This module reuses the original coefficient-reduction transport
argument, separately from any adic or rational coefficient model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Functor
attribute [local instance 2000] CommRing.toRing
namespace AlgebraicGeometry
open PrincipalCoefficient
namespace Etale
set_option hygiene false in
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))
variable {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} {X Y : Scheme.{u}}

/-- Blueprint `lem-fix-operation-reduction`: Basic operations and coefficient reduction; the
compatibility of the reduction `Λ → Λ ⧸ (ϖ)ⁿ` (for `Λ = 𝒪_E`, the reduction `𝒪_E → A_{E,n}`) with
the projection transformation.

For a nonzerodivisor `ϖ` of `Λ`, `f : X ⟶ Y` admitting a compactification, `K ∈ D(X_ét, Λ)` and
`L ∈ D(Y_ét, Λ)`, there are reductions `K_n = K ⊗ᴸ_Λ Λ ⧸ (ϖ)ⁿ` and `L_n = L ⊗ᴸ_Λ Λ ⧸ (ϖ)ⁿ`
(derived base changes, `AlgebraicGeometry.Etale.IsDerivedBaseChange`) such that the reduction
`ρ(PF_{f, K, L})` of the projection map, its image under `- ⊗ᴸ (Λ ⧸ (ϖ)ⁿ)_Y`, is isomorphic as an
arrow to the restriction of scalars of the projection map `PF_{f, K_n, L_n}` over `Λ ⧸ (ϖ)ⁿ`.
It is the reduction square that Step 1 of `sk-thm-sf-pf-adic` cites from
`sk-prop-sf-pf-reduction`, a consequence of
the fixed principal comparison. -/
theorem exists_isDerivedBaseChange_arrowIso_reductionModIdeal_projectionMap
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) (f : X ⟶ Y) [HasCompactification f]
    (K : 𝐃(X, Λ)) (L : 𝐃(Y, Λ)) :
    ∃ (Kn : 𝐃(X, Λ ⧸ Ideal.span {ϖ} ^ n))
      (η : K ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) X).obj Kn)
      (Ln : 𝐃(Y, Λ ⧸ Ideal.span {ϖ} ^ n))
      (η' : L ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) Y).obj Ln),
      IsDerivedBaseChange η ∧ IsDerivedBaseChange η' ∧
        Nonempty (Arrow.mk ((reductionModIdeal Λ Y (Ideal.span {ϖ} ^ n)).map
            (projectionMapApp Λ f K L)) ≅
          Arrow.mk ((derivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) Y).map
            (projectionMapApp (Λ ⧸ Ideal.span {ϖ} ^ n) f Kn Ln)))  := by
  let φ := Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)
  let SX := extension X.smallEtaleTopology φ
  let SY := extension Y.smallEtaleTopology φ
  let adX := scalarAdjunction X.smallEtaleTopology φ
  let adY := scalarAdjunction Y.smallEtaleTopology φ
  exact ⟨SX.obj K, adX.unit.app K, SY.obj L, adY.unit.app L,
    coefficientUnit _ _ adX K, coefficientUnit _ _ adY L,
    principalProjection hϖ n f K L⟩

/-- Exceptional coefficient change transported to any specified universal reduction.
Source: the principal two-term coefficient comparison in lem-fix-operation-reduction.
Proof: identify the specified target with the fixed scalar adjoint using universality,
then compose the fixed exceptional comparison with that isomorphism.
(blueprint: lem-principal-coefficient-exceptional). -/
theorem exists_isDerivedBaseChange_rightDerivedUpperShriek
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) (f : X ⟶ Y) [HasCompactification f]
    [(rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).IsLeftAdjoint]
    [(rightDerivedLowerShriek
      (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {ϖ} ^ n)) f).IsLeftAdjoint]
    (L : 𝐃(Y, Λ)) (Ln : 𝐃(Y, Λ ⧸ Ideal.span {ϖ} ^ n))
    (η : L ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) Y).obj Ln)
    (hη : IsDerivedBaseChange η) :
    ∃ θ : (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).rightAdjoint.obj L ⟶
      (derivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) X).obj
        ((rightDerivedLowerShriek
          (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {ϖ} ^ n)) f).rightAdjoint.obj Ln),
      IsDerivedBaseChange θ := by
  exact coefficientUnary Y.smallEtaleTopology X.smallEtaleTopology _
    (scalarAdjunction _ _) (scalarAdjunction _ _) _ _ L Ln η hη
    (principalExceptional hϖ n f L)

end Etale

namespace ProEtale

set_option hygiene false in
/-- The derived category `D(X_proét, Λ)` of pro-étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ}
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Restriction of scalars `D(X_proét, Λ/Iⁿ) ⥤ D(X_proét, Λ)` along the quotient map. -/
local notation "𝐑𝐞𝐬[" X ", " n "]" =>
  Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) (Ideal.Quotient.mk (I ^ n))

/-- Blueprint `lem-fix-operation-reduction`: Basic operations and coefficient reduction; the
compatibility of the reduction `Λ → Λ/Iⁿ` (for `Λ = 𝒪_E` and `I = 𝔪_E`, the reduction
`𝒪_E → A_{E,n}`) with the compact-support exchange transformation.

For an ideal `I` of `Λ` generated by a nonzerodivisor, a cartesian square `g' ≫ f = f' ≫ g`, a
compactification `c` of `f` and `K ∈ D(X_proét, Λ)` with a reduction `K_n = K ⊗ᴸ_Λ Λ/Iⁿ` (a
derived base change `η : K ⟶ Res K_n`, `CategoryTheory.Sheaf.IsDerivedBaseChange`), the
reduction modulo `Iⁿ` of the compact-support exchange map `Ex_!(c) : Lg^* Rf_!(c) K ⟶
Rf'_!(c') Lg'^* K` over `Λ` is isomorphic, as an arrow, to the restriction of scalars of the
exchange map `Ex_!(c)` over `Λ/Iⁿ` at `K_n`. It is a consequence of
the fixed principal comparison. -/
theorem nonempty_arrowIso_reductionModIdeal_rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (hI : ∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ})
    (n : ℕ) (sq : IsPullback g' f' f g) (c : Compactification f) (K : 𝐃(X, Λ))
    (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, n].obj Kn) (hη : Sheaf.IsDerivedBaseChange η) :
    Nonempty (Arrow.mk
        ((_root_.DerivedCategory.reductionModIdeal (Scheme.ProEt.topology Y') (I ^ n)).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
          c).app K)) ≅
      Arrow.mk (𝐑𝐞𝐬[Y', n].map ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) sq c).app Kn)))  := by
  obtain ⟨ϖ, hϖ, rfl⟩ := hI
  let φ := Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)
  obtain ⟨e⟩ := principalExchange hϖ n sq c K
  obtain ⟨eK⟩ := coefficientIso (Scheme.ProEt.topology X) φ
    (scalarAdjunction _ φ) (η := η) hη
  exact ⟨e ≪≫ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y') φ).mapArrow.mapIso
    (coefficientArrowUnary (rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {ϖ} ^ n)) sq c) eK)⟩

end ProEtale
end AlgebraicGeometry
