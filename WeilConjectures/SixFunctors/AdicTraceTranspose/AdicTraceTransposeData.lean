/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SixFunctors.CompactSupportPbcTransport.CompactSupportProjectionFormula
public import WeilConjectures.SixFunctors.Orientation.OrientationCoefficientTwists
public import WeilConjectures.SixFunctors.Supporting.ConstantCoefficientScalarNormalization
public import WeilConjectures.SmoothPurity.Adic.AdicProjectionShiftCoherence
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # Coefficient calculus for integral projection-trace transposes

Source: blueprint, sk-thm-purity-transport, Steps 2--3; the extracted
projection/counit calculation in lem-pur-adic-purity-scalar-naturality
(blueprint: def-pur-adic-trace-source-coordinates).

The full finite-Tor categories and all exceptional and scalar operations are the
published ones. Source objects are written in canonical ordinary tensor coordinates:
the shifted Tate line on the left and ordinary pullback on the right. The completion
unit and the signed tensor reassociation identify these coordinates with
Lf*(-)(d)[2d]. In particular no finite reduction is used to detect equality of maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
namespace WeilConjectures.AdicTraceTranspose
open ConstructibleExceptionalCoefficients

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)

/-- The existing finite field inside the fixed algebraic closure, packaged for the
published exceptional system. Source: coefficient conventions
(blueprint: def-pur-adic-trace-source-coordinates). -/
def field (E : Padic.FiniteCoefficientFields C.l C.Qbar) : FieldStage.{u} C.l where
  carrier := AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E

/-- The actual full uniform finite-Tor integral category. Source: integral conventions
(blueprint: def-pur-adic-trace-source-coordinates). -/
abbrev Cat (W : SixFunctorSpace D) (E : Padic.FiniteCoefficientFields C.l C.Qbar) :=
  ConstructibleExceptionalCoefficients.C.{u} C.l C.Qbar W.obj.left (.integral (field D C E))

/-- The canonical ordinary tensor model, with its K-flat generator normalization.
Source: tensor convention (blueprint: def-pur-adic-trace-source-coordinates). -/
abbrev tensorModel (W : SixFunctorSpace D) (E : Padic.FiniteCoefficientFields C.l C.Qbar) :=
  RationalSmoothPurityCanonical.ordinaryModel C.l (field D C E).carrier W.obj.left

variable {X Y : SixFunctorSpace D} (f : X ⟶ Y)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (c : Compactification f.hom.left) (d : ℕ)

/-- Ordinary tensor coordinates of the twisted and shifted pullback. Source: H_E and j_E
(blueprint: def-pur-adic-trace-source-coordinates). -/
def sourceAmbient (E : Padic.FiniteCoefficientFields C.l C.Qbar) :=
  (Functor.const (Cat D C Y E)).obj (line D C X E d).obj |>.prod'
    ((finiteTorConstructibleIntegral C.l (field D C E).carrier Y.obj.left).ι ⋙
      PurCompactSupport.pull (PurCompactSupport.completed C.l (field D C E).carrier) f.hom.left)
    |>.comp (tensorModel D C X E).tensor

/-- These canonical source coordinates have the asserted finite-Tor domain.
Source: H_E = Lf_E*(-)(d)[2d]
(blueprint: def-pur-adic-trace-source-coordinates).
Proof: completed pullback preserves constructibility and the uniform reduction Tor
bounds. Tensor with the shifted rank-one line shifts those bounds by -2d. On these
complete inputs the ordinary-to-completed augmentation is invertible, as specified by
tensorToOrdinary. Thus the ordinary source is the completed twisted shifted source
under the canonical symmetry and reassociation. The symmetry crossing [1] and [2d]
has sign (-1)^(2d)=1, including d=0. -/
theorem source_mem (E : Padic.FiniteCoefficientFields C.l C.Qbar) (K : Cat D C Y E) :
    finiteTorConstructibleIntegral C.l (field D C E).carrier X.obj.left
      ((sourceAmbient D C f d E).obj K) := by
  sorry

/-- H_E in j_E coordinates, lifted through the existing full subcategory.
Source: the canonical source reassociation j_E
(blueprint: def-pur-adic-trace-source-coordinates). -/
def source (E : Padic.FiniteCoefficientFields C.l C.Qbar) : Cat D C Y E ⥤ Cat D C X E :=
  (finiteTorConstructibleIntegral C.l (field D C E).carrier X.obj.left).lift
    (sourceAmbient D C f d E) (source_mem D C f d E)

variable (R : RingSystem.{u} C.l C.Qbar D C.different (f := f.hom.left))

/-- The specified exceptional operation, including its adjunction and counit.
Source: exceptional adjunction convention
(blueprint: def-pur-adic-trace-source-coordinates). -/
abbrev operation (E : Padic.FiniteCoefficientFields C.l C.Qbar) :=
  R.operation c (.integral (field D C E))

/-- The fixed full-subcategory inclusion, retaining its ambient shift comparison.
Source: integral full-subcategory convention
(blueprint: def-pur-adic-trace-source-coordinates). -/
abbrev inclusion (W : SixFunctorSpace D) (E : Padic.FiniteCoefficientFields C.l C.Qbar) :=
  (finiteTorConstructibleIntegral C.l (field D C E).carrier W.obj.left).ι

/-- The actual coefficient inclusion E ⊆ F. Source: coefficient conventions
(blueprint: def-pur-adic-trace-source-coordinates). -/
abbrev change {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F) :=
  PurCompactSupport.completedChange C.l (field D C E).carrier (field D C F).carrier
    (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar E F h)

/-- Ordinary derived scalar extension restricted to the full finite-Tor category,
with its specified chi comparison to strict-tower extension. Source: C_(F/E,W)
(blueprint: def-pur-adic-trace-source-coordinates). -/
abbrev scalar {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F) (side : Bool) :=
  R.scalar (s := .integral (field D C E)) (t := .integral (field D C F))
    (change D C h)
    (Allowed.integral (field D C E) (field D C F)
      (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar E F h)) side

/-- The canonical compact-support coefficient comparison, normalized by the proper/open
mate and the recorded realization. Source: c_(F/E)
(blueprint: def-pur-adic-trace-source-coordinates). -/
abbrev supportComparison {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F) :=
  R.comparison c (s := .integral (field D C E)) (t := .integral (field D C F))
    (change D C h)
    (Allowed.integral (field D C E) (field D C F)
      (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar E F h))

/-- The compact-support comparison as an ordinary natural isomorphism.
Source: canonical coefficient comparison c
(blueprint: def-pur-adic-trace-source-coordinates). -/
def supportIso {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F) :
    (operation D C f c R E).F ⋙ (scalar D C f R h false).functor ≅
      (scalar D C f R h true).functor ⋙ (operation D C f c R F).F := by
  letI := (scalar D C f R h true).commShift
  letI := (scalar D C f R h false).commShift
  exact (supportComparison D C f c R h).q

/-- The counit-characterized exceptional coefficient arrow. This is a natural
transformation by the actual mate construction, without a trace invertibility premise.
Source: definition of b_(F/E)
(blueprint: def-pur-adic-trace-source-coordinates). -/
def exceptionalComparison {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F) :
    (operation D C f c R E).G ⋙ (scalar D C f R h true).functor ⟶
      (scalar D C f R h false).functor ⋙ (operation D C f c R F).G :=
by
  letI := (scalar D C f R h true).commShift
  letI := (scalar D C f R h false).commShift
  exact (mateEquiv (operation D C f c R E).adjunction (operation D C f c R F).adjunction
    (TwoSquare.mk _ _ _ _ (supportIso D C f c R h).inv)).natTrans

by
  letI := (closed D C Y E).monoidal
  let e := (RationalSmoothPurityCanonical.ordinaryModel_existsUnique C.l
    (field D C E).carrier Y.obj.left).exists.choose_spec.1
  let U := @RingedSiteDualityModel.unitIso.{u + 1, u, u, u + 2}
    _ _ _ (IntegralOnSlice.abSheafify.{u, u} Y.obj.left none)
    (IntegralOnSlice.abLocallyBijective.{u, u} Y.obj.left none) _ _
    (IntegralOnSlice.duality.{u, u} C.l (field D C E).carrier Y.obj.left none)
  exact eqToIso (congrArg (fun T ↦ T.obj ((unit D C Y E).obj, K.obj)) e) ≪≫
    (closed D C Y E).tensor.mapIso (Iso.prod U.symm (Iso.refl K.obj)) ≪≫
    @MonoidalCategory.leftUnitor _ _ (closed D C Y E).monoidal.toMonoidalCategoryStruct K.obj

end WeilConjectures.AdicTraceTranspose
