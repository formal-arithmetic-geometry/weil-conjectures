/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientComparison.IntegralAdjointFiniteFreeTowerData
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleUpperStar

/-! # Native unit and root-projection scalar normalization
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2).
(blueprint: def-pur-integral-adjoint-tate-scalar-data).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralCoefficientComparison

variable (ell : ℕ) [Fact ell.Prime] (E F : Type u) [Field E] [Field F]
  [Algebra (Padic ell) E] [Algebra (Padic ell) F]
  [FiniteDimensional (Padic ell) E] [FiniteDimensional (Padic ell) F]
  (i : E →ₐ[Padic ell] F)

/-- Actual inclusion on the finite coefficient rings in the native root tower.
The uniformizer towers here are cofinal with the ell-power reduction towers.
Source: (2), root projections (blueprint: def-pur-integral-adjoint-tate-scalar-data). -/
def finiteMap (n : ℕ) : twistFiniteRing ell E n ⟶ twistFiniteRing ell F n :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing ell E (n + 1)) := ⊥
  letI : TopologicalSpace (Padic.coefficientExtensionRing ell F (n + 1)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing ell E (n + 1)) := ⟨rfl⟩
  letI : DiscreteTopology (Padic.coefficientExtensionRing ell F (n + 1)) := ⟨rfl⟩
  twistContinuousMap (WeilConjectures.integralScalarQuotientMap ell E F i n)
    continuous_of_discreteTopology

/-- Native multiplication on the coefficient unit and coefficient inclusion tensor
identity on roots at every finite projection. The limit equation fixes the integral
Tate-line comparison itself, rather than only asserting existence of a line iso.
Source: (2), native units and Tate lines
(blueprint: def-pur-integral-adjoint-tate-scalar-data). -/
structure NativeLines (T : Scheme.{u}) where
  unit : (Mod.extendScalars (coefficientMap
      (Λ := spIntegralCondensed ell E) (Λ' := spIntegralCondensed ell F)
      (map ell E F i).hom.hom T)).obj
        (Mod.regular (condensedRingObj (spIntegralCondensed ell E) T)) ≅
    Mod.regular (condensedRingObj (spIntegralCondensed ell F) T)
  unit_multiplication : unit = Mod.extendScalarsObjRegularIso
    (coefficientMap (Λ := spIntegralCondensed ell E)
      (Λ' := spIntegralCondensed ell F) (map ell E F i).hom.hom T)
  tate : (Mod.extendScalars (coefficientMap
      (Λ := spIntegralCondensed ell E) (Λ' := spIntegralCondensed ell F)
      (map ell E F i).hom.hom T)).obj (coefficientIntegralTwistOne ell E T) ≅
    coefficientIntegralTwistOne ell F T
  level : ∀ n : ℕ, (Mod.extendScalars (coefficientMap
      (Λ := spIntegralCondensed ell E) (Λ' := spIntegralCondensed ell F)
      (map ell E F i).hom.hom T)).obj (coefficientIntegralTwistLevel ell E T n) ⟶
    coefficientIntegralTwistLevel ell F T n
  roots : ∀ n : ℕ,
    ((Mod.extendRestrictAdjunction (coefficientMap
      (Λ := spIntegralCondensed ell E) (Λ' := spIntegralCondensed ell F)
      (map ell E F i).hom.hom T)).homEquiv _ _ (level n)).hom =
    coefficientMap (finiteMap ell E F i n) T ⊗ₘ
      𝟙 (rootsOfUnitySheaf T (ell ^ (n + 1)))
  projections : ∀ n : ℕ,
    tate.hom ≫ limit.π (coefficientIntegralTwistSystem ell F T) (op n) =
      (Mod.extendScalars (coefficientMap
        (Λ := spIntegralCondensed ell E) (Λ' := spIntegralCondensed ell F)
        (map ell E F i).hom.hom T)).map
          (limit.π (coefficientIntegralTwistSystem ell E T) (op n)) ≫ level n

end AlgebraicGeometry.ProEtale.IntegralCoefficientComparison
