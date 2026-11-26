/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralScalarBoundaryConditions
public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportScalarTransitions

/-! # Integral scalar-mate steps for native compact support

## References

* [Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (P : CoefficientConstruction l (ULift.{u} (PadicAlgCl l)) D hl (f := f))
  (c : Compactification f)

/-- The initial three-arrow boundary respects a completed finite coefficient change: it
intertwines the stage transition with `supportScalarTransition`. -/
theorem integralSourceBoundary_transition [G : NativeGeometry.{u} l]
    (target : Realization l Y) (stage : StageAction l D hl P c)
    (i E : Index l (PadicAlgCl l)) (h : i ≤ E)
    (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) i) X)
    (KE : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    (hKE : KE.obj =
      (integralScalarExtension l (Coefficient.{u} l (PadicAlgCl l) i)
        (Coefficient.{u} l (PadicAlgCl l) E)
        (coefficientInclusion l (PadicAlgCl l) i E h) X).obj K.obj)
    (bi : (sections l Y).mapDerivedCategory.obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) i ⋙
          stage.system.functor ⋙ target.J).obj
          ((rationalization.{u, u} l (ULift.{u} (PadicAlgCl l)) (finiteField l i) X).obj K)) ⟶
      (PurCompactSupport.image (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) i)) c ⋙
        pbcDerivedExtend ((target.coefficient i).integralMap l Y)).obj K.obj)
    (bE : (sections l Y).mapDerivedCategory.obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙
          stage.system.functor ⋙ target.J).obj
          ((⟨i, (rationalization.{u, u} l (ULift.{u} (PadicAlgCl l)) (finiteField l i) X).obj K⟩ :
            generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X).toStage h)) ⟶
      (PurCompactSupport.image (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) c ⋙
        pbcDerivedExtend ((target.coefficient E).integralMap l Y)).obj KE.obj)
    (hbi : IntegralSourceBoundary l D hl P c target i K bi)
    (hbE : IntegralSourceBoundary l D hl P c target E KE bE) :
    ArrowHEq
      ((sections l Y).mapDerivedCategory.map
          ((stage.system.functor ⋙ target.J).map
            ((StageSystem.isoToStage
              (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
              ⟨i, (rationalization.{u, u} l (ULift.{u} (PadicAlgCl l)) (finiteField l i) X).obj K⟩
              h).hom)) ≫ bE)
      (bi ≫ supportScalarTransition l c target i E h K.obj) := by sorry

end WeilConjectures.LocallyFiniteAdicCompactSupport
