/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueTensorPullPresentation
public import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueTensorRouteModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueScalarCounitModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueTensorPullCounitModel

/-! The residue tensor square on K-flat representatives with K-flat pullback.

Only the calculation on resolving representatives is left open here. The
scalar-route module proves the passage to arbitrary derived objects by
naturality and constructs the required resolutions itself.

## References

- Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.5.9(5), Remark 6.8.15.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_integralResidueScalarGeometryBridge
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Match the named tensor model without expanding the derived functor construction.
attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The residue tensor square on a K-flat complex whose pullback is K-flat. -/
theorem integralResidue_tensorGeometry_component {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ))
    (_hP : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat P)
    (hFP : ((f)^*⟦integralCoeff ℓ E⟧).kFlatMap P) :
    letI := residueExchangePullMonoidal ℓ E f
      (residueExchangeOrdinaryPullMonoidal ℓ E f) hFlat
    let M := DerivedCategory.Qh.obj P
    (residueExchangeUpperStar (integralCoeff ℓ E) f).map
          ((residueExchangeTensorIso ℓ E Y).hom.app M) ≫
        Functor.OplaxMonoidal.δ (residueExchangeUpperStar (integralCoeff ℓ E) f)
          M (residueExchangeCoefficient ℓ E Y) =
      (residueExchangeRestrictPullIso ℓ E f).hom.app
            ((residueExchangeReduction ℓ E Y).obj M) ≫
          (residueExchangeRestriction ℓ E X).map
            (((residueExchangePullComparisons ℓ E).pull f).inv.app M) ≫
          (residueExchangeTensorPullIso ℓ E f).hom.app
            ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj M) := by
  let := residueExchangePullMonoidal ℓ E f
    (residueExchangeOrdinaryPullMonoidal ℓ E f) hFlat
  have : IsIso (residueExchangeTensorModelTarget ℓ E f P) := by
    let : BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
      AlgebraicGeometry.ProEtale.sheafBraidedCategory Ab.{u + 1} X
    let : BraidedCategory (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) :=
      AlgebraicGeometry.ProEtale.sheafBraidedCategory Ab.{u + 1} Y
    delta residueExchangeTensorModelTarget residueExchangeUpperStar
      residueExchangeUpperStarCounit
    simpa only [Functor.tensorModelTarget, id] using
      Functor.tensorModelTarget_isIso (f)^*⟦integralCoeff ℓ E⟧
      (residueExchangeOrdinaryCoefficient ℓ E Y) P hFP
  apply (cancel_mono (residueExchangeTensorModelTarget ℓ E f P)).mp
  have hscalarModel :
      (residueExchangeRestrictPullIso ℓ E f).hom.app
          ((residueExchangeReduction ℓ E Y).obj (DerivedCategory.Qh.obj P)) ≫
        (residueExchangeRestriction ℓ E X).map
          (((residueExchangePullComparisons ℓ E).pull f).inv.app (DerivedCategory.Qh.obj P)) ≫
        (residueExchangeTensorPullIso ℓ E f).hom.app
          ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj (DerivedCategory.Qh.obj P)) ≫
        residueExchangeTensorModelTarget ℓ E f P = residueExchangeTensorModelMap ℓ E f P := by
    rw [integralResidue_tensorPullCounit_model ℓ E f P]
    exact integralResidue_scalarCounit_model ℓ E f P
  simpa only [Category.assoc] using
    (integralResidue_tensorRoute_model ℓ E f hFlat P).trans hscalarModel.symm

end AlgebraicGeometry.ProEtale.CondensedRing
