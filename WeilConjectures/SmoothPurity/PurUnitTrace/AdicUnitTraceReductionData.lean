/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Adic.AdicProjectionShiftCoherence
public import WeilConjectures.SmoothPurity.PurAdicScalarTrace.AdicScalarTraceCoherence
public import WeilConjectures.SmoothPurity.Pur.PurAdicReconstruction
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteUniversalSmoothTrace
public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackTower
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Unit trace reduction data

Source: current blueprint, purity transport Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-reduction-data).

This module defines the completed coefficient unit, source and Tate unit, the
counit-normalized finite right comparison, the exceptional reduction map and
its prescribed-reduction predicate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.PurUnitTrace
open ConstructibleExceptionalCoefficients
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]
  (S : RingSystem C.l C.Qbar D C.different (f := f))

/-- The existing completed regular coefficient module in degree zero.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-reduction-data). -/
abbrev coefficientUnit (W : Scheme.{u}) := integralConstantCoefficientObject C.l E W

/-- The existing completed Tate line, with the prescribed even shift.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-reduction-data). -/
def tateUnit (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :=
  (sfIntegralTwistingObject C.l E W (d : ℤ))⟦2 * (d : ℤ)⟧

/-- Completed pullback followed by the actual exact twist and even shift.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-reduction-data). -/
def sourceFunctor : DerivedCategory (scalarReductionSource C.l E Y) ⥤
    DerivedCategory (scalarReductionSource C.l E X) :=
  integralDerivedPullback C.l E f ⋙ integralComplexTwist D C.l C.different E X (d : ℤ) ⋙
    shiftFunctor _ (2 * (d : ℤ))

/-- The specified compact-support/exceptional adjunction at the chosen compactification.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-reduction-data). -/
def operation := S.operation (integralExceptionalCompactification D f) (.integral {carrier := E})

set_option genSizeOf false in
set_option genSizeOfSpec false in
set_option genInjectivity false in
set_option genCtorIdx false in
/-- The canonical finite right realization, characterized by the smooth exceptional counit.
Its existence is a conclusion of the main theorem, not an added hypothesis. The
recorded bare finiteRight isomorphism is insufficient to pin its normalization.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-reduction-data). -/
structure FiniteRightNormalization where
  iso : ∀ n : ℕ,
    (S.operation (integralExceptionalCompactification D f)
      (.finite {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)).G ⋙
        (finiteTorConstructible C.l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X).ι ≅
      (finiteTorConstructible C.l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y).ι ⋙
        ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing C.l E (n + 1))
          (integralExceptionalCompactification D f)
  counit : ∀ (n : ℕ)
    (K : finiteTorConstructibleCategory C.l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) Y),
    (S.left (integralExceptionalCompactification D f)
        (.finite {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)).inv.app
          ((S.operation (integralExceptionalCompactification D f)
            (.finite {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)).G.obj K) ≫
      ((S.operation (integralExceptionalCompactification D f)
        (.finite {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)).adjunction.counit.app K).hom =
      (PurCompactSupport.finiteImageIso C.l E n
        (integralExceptionalCompactification D f)).hom.app _ ≫
      (PurityFiniteSetting.smoothCompactSupport (purAdicFiniteSetting D C E n) f).map
        ((iso n).hom.app K) ≫
      PurityFiniteSetting.smoothExceptionalCounit (purAdicFiniteSetting D C E n) f K.obj

set_option maxHeartbeats 150000 in
-- The two specified scalar models require conversions between intrinsic coefficient categories.
/-- The canonical exceptional coefficient mate, with normalized scalar realization
and the counit-normalized finite right realization.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-reduction-data). -/
def targetReduction (normal : FiniteRightNormalization D C E f S)
    (K : finiteTorConstructibleIntegralCategory C.l E Y) (n : ℕ) :
    (scalarReductionDerivedExtension C.l E X n).obj
        (((operation D C E f S).G.obj K).obj) ⟶
      (ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing C.l E (n + 1))
        (integralExceptionalCompactification D f)).obj
          ((scalarReductionDerivedExtension C.l E Y n).obj K.obj) :=
by
  let sx := S.scalar (s := .integral {carrier := E})
    (t := .finite {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)
    (PurCompactSupport.reduction C.l E (n + 1) (Nat.succ_pos n))
    (Allowed.reduction {carrier := E} ⟨n + 1, Nat.succ_pos n⟩) true
  let sy := S.scalar (s := .integral {carrier := E})
    (t := .finite {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)
    (PurCompactSupport.reduction C.l E (n + 1) (Nat.succ_pos n))
    (Allowed.reduction {carrier := E} ⟨n + 1, Nat.succ_pos n⟩) false
  letI := sx.commShift
  letI := sy.commShift
  exact
    (PurCompactSupport.finiteReductionIso C.l E X n).inv.app _ ≫
      ((S.scalar (s := .integral {carrier := E})
        (t := .finite {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)
        (PurCompactSupport.reduction C.l E (n + 1) (Nat.succ_pos n))
        (Allowed.reduction {carrier := E} ⟨n + 1, Nat.succ_pos n⟩) true).realization.inv.app
          ((operation D C E f S).G.obj K)) ≫
      ((S.comparison (integralExceptionalCompactification D f)
        (s := .integral {carrier := E})
        (t := .finite {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)
        (PurCompactSupport.reduction C.l E (n + 1) (Nat.succ_pos n))
          (Allowed.reduction {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)).b.hom.app K).hom ≫
      (normal.iso n).hom.app _ ≫
      (ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing C.l E (n + 1))
        (integralExceptionalCompactification D f)).map
          ((S.scalar (s := .integral {carrier := E})
        (t := .finite {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)
        (PurCompactSupport.reduction C.l E (n + 1) (Nat.succ_pos n))
            (Allowed.reduction {carrier := E} ⟨n + 1, Nat.succ_pos n⟩) false).realization.hom.app K
              ≫
              (PurCompactSupport.finiteReductionIso C.l E Y n).hom.app K.obj)

/-- Equality with the actual finite smoothPurityMap at every positive exponent.
The heterogeneous equality retains the separately defined canonical finite targets.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-reduction-data). -/
def HasPrescribedReductions (normal : FiniteRightNormalization D C E f S)
    (K : finiteTorConstructibleIntegralCategory C.l E Y)
    (g : (sourceFunctor D C E f d).obj K.obj ⟶ ((operation D C E f S).G.obj K).obj) : Prop :=
  ∀ n : ℕ, HEq
    ((scalarReductionDerivedExtension C.l E X n).map g ≫ targetReduction D C E f S normal K n)
    (purAdicSourceReduction D C E f d K.obj K.property n ≫
      (purAdicFiniteArrow D C E f d K.obj K.property n).hom)

/-- Remove the regular unit from the exact twist by the actual site tensor unitor.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-reduction-data). -/
def twistedUnitIso (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :
    PurAdicScalarTrace.overTwistedUnit C.l E D C.different W d ≅ tateUnit D C E d W :=
  (shiftFunctor _ (2 * (d : ℤ))).mapIso
    (((integralSheafTwist C.l E W (d : ℤ)).mapDerivedCategorySingleFunctor 0).app
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted C.l E W)) ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          ((SheafOfModules.siteSheafTensorRightIso
            (completedIntegralCommRingSheafUnrestricted C.l E W)
            (integralTwistLine C.l E W (d : ℤ))).app _ ≪≫
              MonoidalCategory.leftUnitor (integralTwistLine C.l E W (d : ℤ))))

/-- Pull back the regular coefficient unit using its normalized tower map, then
remove the tensor unit from its exact twist.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-reduction-data). -/
def sourceUnitIso (core : CompletedUnitPullback.Core C.l E f) :
    (sourceFunctor D C E f d).obj (coefficientUnit D C E Y) ≅ tateUnit D C E d X :=
  (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((integralComplexTwist D C.l C.different E X (d : ℤ)).mapIso core.unit) ≪≫
    twistedUnitIso D C E d X

end WeilConjectures.PurUnitTrace
