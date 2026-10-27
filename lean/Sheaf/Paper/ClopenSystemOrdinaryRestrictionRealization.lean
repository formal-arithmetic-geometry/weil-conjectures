module

public import Sheaf.Paper.ClopenCanonicalRestrictionEvaluation
public import Sheaf.Paper.AdicPurityObjects
public import Sheaf.Paper.CoefficientSystemDerivedComparison
public import Sheaf.Paper.OpenCompletedRestrictionIdentification
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Site transport and integral realization on a clopen component

Source: blueprint def-pur-section-invariant, finite-clopen expansion, retained steps 8--9;
Zheng, Lemmas 4.10 and 5.22; Stacks Tags 0941 and 08BJ
(blueprint: def-pur-clopen-ordinary-restriction-realization).

All systems below are actual strict systems. Their scalar forgetting and inverse limit
are the published functors on the derived category of strict towers. The result records
normalization equations for maps, as well as natural isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [local irreducible] HasDerivedCategory.standard
attribute [-instance] WeilConjectures.integralExceptionalEvaluation_additive
attribute [local instance] SheafOfModules.CoefficientSystemOrdinaryImage.inverseAdditive
set_option allowUnsafeReducibility true
attribute [local reducible] WeilConjectures.IntegralOnSlice.Site
  WeilConjectures.IntegralOnSlice.topology WeilConjectures.IntegralOnSlice.restrict
  WeilConjectures.IntegralOnSlice.ring WeilConjectures.IntegralOnSlice.finite
  WeilConjectures.IntegralOnSlice.projection
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.PurityFiniteSetting

set_option maxHeartbeats 500000 in
-- Record the section normalization independently of derived localization.
/-- Fixed-coefficient realization of ordinary component restriction, pinned on sections.
Source: Stacks 00XZ; Zheng 4.10
(blueprint: def-pur-clopen-ordinary-restriction-realization). -/
structure ClopenSystemOrdinaryRestrictionRealization (P : PurityFiniteSetting.{u})
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Xi ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] [QuasiCompact g]
    (C : ClopenSystemTransportCore P c j) where
  [restrictionOrdinaryAdditive : ∀ n, (C.site.ordinary.lift n).modules.Additive]
  [restrictionCompositeZero : ∀ n, ((C.site.ordinary.lift n).modules ⋙
    integralExceptionalProRealization P.coefficients.l P.extension Xi n).PreservesZeroMorphisms]
  [restrictionTargetZero : ∀ n, (integralExceptionalProRealization
    P.coefficients.l P.extension X n ⋙
      ProEtale.upperStar (ModuleCat.{u + 1} (clopenRealizationLevel P n).Coefficient)
        j).PreservesZeroMorphisms]
  restrictionOrdinary : ∀ n,
    (C.site.ordinary.lift n).modules ⋙
      integralExceptionalProRealization P.coefficients.l P.extension Xi n ≅
    integralExceptionalProRealization P.coefficients.l P.extension X n ⋙
      ProEtale.upperStar (ModuleCat.{u + 1} (clopenRealizationLevel P n).Coefficient) j
  restrictionOrdinary_sections : ∀ n
      (A : SheafOfModules.coefficientLevelModules (J := Scheme.ProEt.topology X)
        (clopenSystemRing P.coefficients.l P.extension)
        (clopenSystemUniformizer P.coefficients.l P.extension) n)
      (V : Xi.ProEt)
      (x : ((integralExceptionalProRealization P.coefficients.l P.extension Xi n).obj
        ((C.site.ordinary.lift n).modules.obj A)).obj.obj (op V))
      (y : ((C.site.ordinary.lift n).modules.obj A).val.obj (op V)),
    HEq x y → HEq
      (((ProEtale.upperStarIsoOpenImmersionRestriction
        (ModuleCat.{u + 1} (clopenRealizationLevel P n).Coefficient) j).hom.app
          ((integralExceptionalProRealization P.coefficients.l P.extension X n).obj A)).hom.app
            (op V) (((restrictionOrdinary n).hom.app A).hom.app (op V) x))
      (((C.setRestriction.sheafIso).hom.app
        ((SheafOfModules.coefficientUnderlying (J := Scheme.ProEt.topology X)
          (clopenSystemRing P.coefficients.l P.extension)
          (clopenSystemUniformizer P.coefficients.l P.extension) n).obj A)).hom.app (op V)
        (((C.site.ordinary.lift n).moduleUnderlying.hom.app A).hom.app (op V) y))

/-- Exact localization of the ordinary section-normalized restriction comparison.
The equation is imposed on every cochain representative, using the recorded Q factors.
Source: Stacks 00XZ, 015F; Zheng 4.10
(blueprint: def-pur-clopen-ordinary-restriction-realization). -/
def IsClopenRestrictionDerivedNormalized (P : PurityFiniteSetting.{u})
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Xi ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] [QuasiCompact g]
    (C : ClopenSystemTransportCore P c j)
    (O : ClopenSystemOrdinaryRestrictionRealization P c j C) (n : ℕ)
    (e : ClopenRestrictionRealizationIso P c j C n) : Prop :=
  letI := O.restrictionOrdinaryAdditive
  letI := O.restrictionCompositeZero
  letI := O.restrictionTargetZero
  ∀ H : CochainComplex (SheafOfModules.coefficientLevelModules
        (J := Scheme.ProEt.topology X) (clopenSystemRing P.coefficients.l P.extension)
        (clopenSystemUniformizer P.coefficients.l P.extension) n) ℤ,
    (Iso.hom e).app (DerivedCategory.Q.obj H) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} (clopenRealizationLevel P n).Coefficient)
        j).mapDerivedCategory.map
          ((integralExceptionalProRealization P.coefficients.l P.extension X
      n).mapDerivedCategoryFactors.hom.app H) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} (clopenRealizationLevel P n).Coefficient)
        j).mapDerivedCategoryFactors.hom.app
          (((integralExceptionalProRealization P.coefficients.l P.extension X
            n).mapHomologicalComplex (.up ℤ)).obj H) =
    (integralExceptionalProRealization P.coefficients.l P.extension Xi
      n).mapDerivedCategory.map
      ((SheafOfModules.CoefficientSystemDerivedImage.level.{u + 1, u, u + 1,
        u, u + 1, u + 2} C.site.derived n).inverseFactors.hom.app H) ≫
    (integralExceptionalProRealization P.coefficients.l P.extension Xi
      n).mapDerivedCategoryFactors.hom.app
        ((((C.site.ordinary.lift n).modules).mapHomologicalComplex (.up ℤ)).obj H) ≫
    DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex (O.restrictionOrdinary n) (.up ℤ)).hom.app H)

end WeilConjectures.PurityFiniteSetting
