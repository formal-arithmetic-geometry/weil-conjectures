module

public import Sheaf.Paper.FramedScalarMaps
public import Sheaf.Paper.FramedAbelianRealization
import Sheaf.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit
import Sheaf.AlgebraicGeometry.ScalarUnitExt

/-! # Supported Kummer realization of a framed line bundle

Source: Stacks Tags 03AJ, 03PL and 0A45; blueprint main-20261015,
lem-pur-divisor-class, first sentence and final paragraph
(blueprint: def-pur-framed-scalar-realization).

The integral torsor extension remembers the frame on the complementary open.
Scalar extension is performed on roots of unity, never on Gm as a Z/m-module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w hC hD

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor

private theorem realizeExact_bijective {C D : Type v}
    [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
    [HasExt.{w} C] [HasExt.{w} D]
    [HasDerivedCategory.{hC} C] [HasDerivedCategory.{hD} D]
    (U : C ⥤ D) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {S B : C} {I : D} (η : I ⟶ U.obj S) (hη : U.DerivedUnit I S η) :
    Function.Bijective (divisorRealizeExact U (B := B) η) := by
  unfold divisorRealizeExact
  exact CategoryTheory.Abelian.scalar_unit_ext_bijective U η hη 2

/-- There is exactly one module extension with the prescribed integral realization.
Source: Stacks 03PL, 03FD and the framed-line scalar-normalization assertion
(blueprint: def-pur-framed-scalar-realization).
Proof: m=ell^n is a positive annihilator of A. Apply the supported integral DerivedUnit
bijection with target B[2], where B=mu_m tensor A. Exact forgetting and the single/shift
comparisons identify that bijection with divisorAbelianRealization. Its inverse at the
roots-coefficient image of k_m[1] beta gives existence and uniqueness. -/
theorem divisorScalarRealization_existsUnique (P : PurityFiniteSetting.{u})
    {Z T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k))
    (i : Z ⟶ T) [IsClosedImmersion i]
    (β : Ext.{u + 1} ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
      (Etale.supportedIntegralConstant Z)) T.gmSheaf 1) :
    DivisorUniqueRealization (P.divisorAbelianRealization i) (P.divisorIntegralSplice a i β) := by
  unfold DivisorUniqueRealization
  have hn : 0 < P.diagonalExponent :=
    pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level
  have hunit := Etale.supported_integral_derived_unit T P.diagonalExponent hn
    P.Coefficient P.diagonalExponent_annihilates i
  have hbij := realizeExact_bijective
    (Etale.RawModuleScalarComparison.forget P.Coefficient T)
    (S := (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale Z))
    (B := P.frameTwistEtale T 1)
    (Etale.supportedIntegralGenerator P.Coefficient i) hunit
  have hbij' : Function.Bijective (fun b ↦ P.divisorAbelianRealization i b) := by
    unfold divisorAbelianRealization
    exact hbij
  exact hbij'.existsUnique (P.divisorIntegralSplice a i β)

/-- The unique finite coefficient realization; its data is determined by the explicit
integral equation, rather than a mere existence assertion.
Source: framed-line refinement of lem-pur-divisor-class
(blueprint: def-pur-framed-scalar-realization). -/
@[irreducible] def divisorScalarRealization (P : PurityFiniteSetting.{u}) {Z T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k))
    (i : Z ⟶ T) [IsClosedImmersion i]
    (β : Ext.{u + 1} ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
      (Etale.supportedIntegralConstant Z)) T.gmSheaf 1) :
    Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
      (P.constantEtale Z)) (P.frameTwistEtale T 1) 2 :=
  divisorChooseRealization (P.divisorAbelianRealization i) (P.divisorIntegralSplice a i β)
    (P.divisorScalarRealization_existsUnique a i β)



end WeilConjectures.PurityFiniteSetting
