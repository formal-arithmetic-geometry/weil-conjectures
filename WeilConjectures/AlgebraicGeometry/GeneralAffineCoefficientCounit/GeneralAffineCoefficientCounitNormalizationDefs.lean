/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineCoefficientCounit.AffineCoefficientCounitNormalization
import WeilConjectures.AlgebraicGeometry.FiniteCompactificationTranspose.FiniteRingCompactificationTransposeComparison
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityCoordinateMaps
import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalAffineTrace.DiagonalAffineTraceCoordinates
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitData
import WeilConjectures.SixFunctors.Etale.Derived.Identity
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
import WeilConjectures.AlgebraicGeometry.FiniteCompactificationTranspose.FiniteRingCompactificationTransposeComparison
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityCoordinateMaps
import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalAffineTrace.DiagonalAffineTraceCoordinates
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitData
import WeilConjectures.SixFunctors.Etale.Derived.Identity
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegrationGeneral.AffineOrderedGeneralCounitNormalization
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.AlgebraicGeometry.CurrentProEtaleProjectionFormulaStatement
public import WeilConjectures.AlgebraicGeometry.TensorTraceTranspose
public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionMaps
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback

/-! Shared definitions for the general affine coefficient counit normalization.
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.GeneralAffineCoefficientCounit
open AffineOrderedIntegrationGeneral FiniteCompactificationTranspose

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The coefficient-unit adjoint of the ordered trace, in ordinary-origin coordinates.
Source: P at A_Y in the tensor display
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def unitTranspose (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :=
  (Etale.rightDerivedUpperShriekAdjunction A (affineProjection Y d)).homEquiv
    (Etale.FiniteSmoothPurity.line A N hA (affineSpace Y d) d) (𝟙_ _)
    (WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.ordinaryTrace
      A N hN hA Y hY d ≫ (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom)

/-- The displayed tensor identity, in ordinary-origin coordinates and after C_X.
`tensorTraceTheta` is the counit-transposed tensor construction (with its source
symmetry), and `tensorTraceIntegrated` transposes inverse projection and tensor trace.
Source: theta(1 tensor P)=P_K, third paragraph
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def TensorIdentity (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤)))
    (H : E A Y) (d : ℕ) : Prop :=
  let f := affineProjection Y d
  let X := affineSpace Y d
  let W := Etale.FiniteSmoothPurity.line A N hA X d
  let t := WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.ordinaryTrace
    A N hN hA Y hY d ≫ (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom
  let tensorP := ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
    ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H)).map
      (unitTranspose A N hN hA Y hY d)
  IsIso (unitTranspose A N hN hA Y hY d) ∧
    tensorP ≫ Etale.tensorTraceTheta A f H = Etale.tensorTraceIntegrated A f W H t ∧
    (C A X).map tensorP ≫ (C A X).map (Etale.tensorTraceTheta A f H) =
      (C A X).map (Etale.tensorTraceIntegrated A f W H t)

/-- The actual ordinary line counit realized by the fixed proper/open site comparison.
Source: the affine-line counit and its site realization, fourth paragraph
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def lineCounit (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤)))
    (H : EPlus A Y)
    (hJ : DerivedCategory.TStructure.t.plus ((CoordinateLine.right A N hA Y).obj H.obj)) :=
  (B A (affineTraceLineCompactification Y)
    ⟨(CoordinateLine.right A N hA Y).obj H.obj, hJ⟩).inv ≫
      (C A Y).map ((CoordinateLine.adjunction A N hA Y hN hY).counit.app H.obj)

/-- The exceptional transpose of that same actual line counit. The exceptional right
adjoint is the ordinary Brown right adjoint, not an ambient pro-etale adjoint.
Source: Gamma and the specified Hom comparison, fourth paragraph
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def lineGamma (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤)))
    (H : EPlus A Y)
    (hJ : DerivedCategory.TStructure.t.plus ((CoordinateLine.right A N hA Y).obj H.obj)) :=
  transpose A (affineTraceLineCompactification Y) _
    (CoordinateLine.exceptionalAdjunction A Y)
    ⟨(CoordinateLine.right A N hA Y).obj H.obj, hJ⟩ H
    (lineCounit A N hN hA Y hY H hJ)

/-- All actual line equalities, including the projection and transpose comparison.
The boundedness witnesses are conclusions. The ordinary normalization uses the restricted
projective trace `CoordinateLine.integration`, namely Rq_* of the open counit followed
by the normalized projective-line trace. The target comparison is conjugation of the
identity left functor, so its scalar and orientation are fixed.
Source: the affine-line paragraph
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def LineIdentity (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤)))
    (H : E A Y) : Prop :=
  CoordinateLine.CounitNormalization A N hA Y hN hY H ∧
  ∃ (hH : DerivedCategory.TStructure.t.plus H)
    (hJ : DerivedCategory.TStructure.t.plus ((CoordinateLine.right A N hA Y).obj H))
    (_hG : DerivedCategory.TStructure.t.plus
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (affineTraceLineCompactification Y)).rightAdjoint.obj H)),
    (B A (affineTraceLineCompactification Y)
      ⟨(CoordinateLine.right A N hA Y).obj H, hJ⟩).hom ≫
        lineCounit A N hN hA Y hY ⟨H, hH⟩ hJ =
      (C A Y).map ((CoordinateLine.adjunction A N hA Y hN hY).counit.app H) ∧
    lineGamma A N hN hA Y hY ⟨H, hH⟩ hJ =
      (C A (AffineSpace PUnit.{u + 1} Y)).map
        ((CoordinateLine.comparison A N hA Y hN hY).hom.app H) ∧
    ProjectionLaw A (affineTraceLineCompactification Y) ∧
    TransposeLaw A (affineTraceLineCompactification Y) ∧
    RepresentativeLaw A (affineTraceLineCompactification Y)

/-- A coordinate pullback with an arbitrary signed finite Tate line and shift.
This extends the existing nonnegative-power domain display without changing its notions.
Source: base factors in the second paragraph
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def baseFactor (N : ℕ) (hA : (N : A) = 0) (Y : Scheme.{u})
    (d : ℕ) (c s : ℤ) (H : E A Y) : E A (affineSpace Y d) :=
  ((((Etale.derivedTensor (ModuleCat.{u + 1} A) (affineSpace Y d)).obj
    ((Etale.ordinaryFinitePullback A (affineProjection Y d)).obj H)).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A N (affineSpace Y d) hA c)))⟦s⟧)

/-- Derive and shift a normalized change of the projective Tate line.
Source: canonical Kummer exponent identification in the last paragraph
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def projectiveExponentIso {N M : ℕ} {hN : (N : A) = 0} {hM : (M : A) = 0}
    (Y : Scheme.{u})
    (e : Scheme.finiteEtaleTateLine (ProjectiveLine Y) M A hM ≅
      Scheme.finiteEtaleTateLine (ProjectiveLine Y) N A hN) :=
  (shiftFunctor _ (2 : ℤ)).mapIso ((_root_.DerivedCategory.singleFunctor _ 0).mapIso e)

/-- Restrict the same projective exponent identification to the affine chart.
Source: open restriction of the trace-normalized line
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def lineExponentIso {N M : ℕ} {hN : (N : A) = 0} {hM : (M : A) = 0}
    (Y : Scheme.{u})
    (e : Scheme.finiteEtaleTateLine (ProjectiveLine Y) M A hM ≅
      Scheme.finiteEtaleTateLine (ProjectiveLine Y) N A hN) :=
  (Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart Y)).mapIso
    (projectiveExponentIso A Y e)

/-- Tensor the canonical exponent comparison with the unchanged ordinary pullback.
Source: exponent independence of the counit and Gamma
(blueprint: lem-pur-affine-coefficient-counit-normalization). -/
def sourceExponentIso {N M : ℕ} {hN : (N : A) = 0} {hM : (M : A) = 0}
    (Y : Scheme.{u})
    (e : Scheme.finiteEtaleTateLine (ProjectiveLine Y) M A hM ≅
      Scheme.finiteEtaleTateLine (ProjectiveLine Y) N A hN) (H : E A Y) :
    (CoordinateLine.right A M hM Y).obj H ≅ (CoordinateLine.right A N hN Y).obj H := by
  refine (CoordinateLine.rightCoordinates A M hM Y H).symm ≪≫ ?_ ≪≫
    CoordinateLine.rightCoordinates A N hN Y H
  unfold AffineLinePurity.ordinarySourceObject
  exact ((Etale.derivedTensor (ModuleCat.{u + 1} A) (AffineSpace PUnit.{u + 1} Y)).obj
    ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} Y ↘ Y)).obj H)).mapIso
      (lineExponentIso A Y e)

end AlgebraicGeometry.ProEtale.GeneralAffineCoefficientCounit
