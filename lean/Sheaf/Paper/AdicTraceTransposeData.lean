/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.CompactSupportProjectionFormula
public import Sheaf.Paper.OrientationCoefficientTwists
public import Sheaf.Paper.ConstantCoefficientScalarNormalization
public import Sheaf.Paper.AdicProjectionShiftCoherence
import Sheaf.CategoryTheory.PastedMatesCounitNormalization
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

/-- The published tensor closed structure with every sheafification universe fixed.
Source: ordinary tensor normalization
(blueprint: def-pur-adic-trace-source-coordinates). -/
abbrev closed (W : SixFunctorSpace D) (E : Padic.FiniteCoefficientFields C.l C.Qbar) :=
  @RingedSiteDualityModel.closed.{u + 1, u, u, u + 2}
    _ _ _ (IntegralOnSlice.abSheafify.{u, u} W.obj.left none)
    (IntegralOnSlice.abLocallyBijective.{u, u} W.obj.left none) _ _
    (IntegralOnSlice.duality.{u, u} C.l (field D C E).carrier W.obj.left none)

/-- The coefficient unit is finite-Tor and constructible. Source: integral conventions
(blueprint: def-pur-adic-trace-source-coordinates).
Proof: the unit is the completed coefficient sheaf in degree zero, by the normalized
unit comparison of IntegralOnSlice.duality. Every reduction is the constant quotient
in degree zero. Its quotient tower reconstructs the complete unit, and all Tor
intervals are [0,0]. Transport along the unit comparison. -/
theorem unit_mem (W : SixFunctorSpace D) (E : Padic.FiniteCoefficientFields C.l C.Qbar) :
    finiteTorConstructibleIntegral C.l (field D C E).carrier W.obj.left
      (integralConstantCoefficientObject C.l (field D C E).carrier W.obj.left) := by
  sorry

/-- The same coefficient unit, in the full subcategory. Source: R_E[0]
(blueprint: def-pur-adic-trace-source-coordinates). -/
def unit (W : SixFunctorSpace D) (E : Padic.FiniteCoefficientFields C.l C.Qbar) : Cat D C W E :=
  ⟨_, unit_mem D C W E⟩

/-- The actual one-term Tate line in degree -2d. Source: T_E = 1_E(d)[2d]
(blueprint: def-pur-adic-trace-source-coordinates). -/
def line (W : SixFunctorSpace D) (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (d : ℕ) : Cat D C W E :=
  ⟨DerivedCategory.Q.obj (sfOrientationIntegralComplex C.l (field D C E).carrier W.obj.left d),
    @sfOrientationIntegralComplex_mem C.l _ (field D C E).carrier _ _ _ W.obj.left
      (dlAdicGeometricResidueInvertible D C W.obj.left) d⟩

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

/-- The tensor coordinates identify the actual completed twisted shifted pullback.
This uses the existing integral pullback and exact Tate twist, rather than defining
another pullback operation.
Source: H_E=Lf_E*(-)(d)[2d] and its canonical j reassociation
(blueprint: def-pur-adic-trace-source-coordinates).
Proof: the normalized completion unit compares ordinary pullback on a complete
finite-Tor input with integralDerivedPullback. On flat K-flat representatives the
completion unit is the strict (c,0) augmentation. TensorToOrdinary removes completed
tensor on these inputs. The flat Tate line computes its derived tensor termwise;
apply the single-complex total identification and sfOrientationIntegralShiftIso.
Symmetry places the line on the left; signed reassociation moves [2d] to the line.
The crossing sign is (-1)^(2d)=1. These representative maps commute with arrows and
quasi-isomorphisms, so descent gives the asserted natural isomorphism. -/
theorem source_presentation (E : Padic.FiniteCoefficientFields C.l C.Qbar) :
    Nonempty (((finiteTorConstructibleIntegral C.l
      (field D C E).carrier Y.obj.left).ι ⋙
      integralDerivedPullback C.l (field D C E).carrier f.hom.left ⋙
      @sfIntegralTwistingFunctor C.l _ (field D C E).carrier _ _ _ X.obj.left
        (dlAdicGeometricResidueInvertible D C X.obj.left) (d : ℤ) ⋙
      shiftFunctor _ (2 * (d : ℤ))) ≅ sourceAmbient D C f d E) := by
  sorry

variable (R : RingSystem.{u} C.l C.Qbar D C.different (f := f.hom.left))

/-- The specified exceptional operation, including its adjunction and counit.
Source: exceptional adjunction convention
(blueprint: def-pur-adic-trace-source-coordinates). -/
abbrev operation (E : Padic.FiniteCoefficientFields C.l C.Qbar) :=
  R.operation c (.integral (field D C E))

/-- The specified left operation shift.
Source: exact exceptional adjunction
(blueprint: def-pur-adic-trace-source-coordinates). -/
instance operationLeftShift (E : Padic.FiniteCoefficientFields C.l C.Qbar) :
    (operation D C f c R E).F.CommShift ℤ := (operation D C f c R E).leftShift

/-- The counit-compatible right operation shift.
Source: exceptional adjunction shift convention
(blueprint: def-pur-adic-trace-source-coordinates). -/
instance operationRightShift (E : Padic.FiniteCoefficientFields C.l C.Qbar) :
    (operation D C f c R E).G.CommShift ℤ := (operation D C f c R E).rightShift

/-- The fixed full-subcategory inclusion, retaining its ambient shift comparison.
Source: integral full-subcategory convention
(blueprint: def-pur-adic-trace-source-coordinates). -/
abbrev inclusion (W : SixFunctorSpace D) (E : Padic.FiniteCoefficientFields C.l C.Qbar) :=
  (finiteTorConstructibleIntegral C.l (field D C E).carrier W.obj.left).ι

/-- The ordinary sheaf inverse-image functor underlying Lf*.
Source: derived inverse image convention
(blueprint: def-pur-adic-trace-source-coordinates). -/
abbrev pullModule (E : Padic.FiniteCoefficientFields C.l C.Qbar) :=
  proEtaleRingModulePullback f.hom.left
    ((PurCompactSupport.completed C.l (field D C E).carrier).ring Y.obj.left)
    ((PurCompactSupport.completed C.l (field D C E).carrier).ring X.obj.left)
    ((PurCompactSupport.completed C.l (field D C E).carrier).pull f.hom.left)

/-- The signed total complex representing H in j-coordinates.
Source: T tensor Lf*, with the shifted line on the left
(blueprint: def-pur-adic-trace-source-coordinates). -/
def sourceComplex (E : Padic.FiniteCoefficientFields C.l C.Qbar) :=
  (pullModule D C f E).mapHomologicalComplex (.up ℤ) ⋙
    ((proEtaleOrdinaryTensor X.obj.left
      ((PurCompactSupport.completed C.l (field D C E).carrier).ring X.obj.left)
        ).map₂CochainComplex).obj
      (sfOrientationIntegralComplex C.l (field D C E).carrier X.obj.left d)

/-- The source total carries the standard signed tensor and termwise pullback shifts.
Source: signed total convention
(blueprint: def-pur-adic-trace-source-coordinates). -/
instance sourceComplexShift (E : Padic.FiniteCoefficientFields C.l C.Qbar) :
    (sourceComplex D C f d E).CommShift ℤ := by
  dsimp only [sourceComplex]
  infer_instance

/-- The representative comparison uniquely fixed by the tensor localization.
Source: canonical source normalization
(blueprint: def-pur-adic-trace-source-coordinates).
Proof: the shifted rank-one line is a flat K-flat complex; inverse image preserves
flat K-flat representatives. Apply ordinaryModel.representative to that pair and
then its tensor functor to the inverse of the exact pullback factorization and e.
This prescribes the arrow uniquely, independently of either resolution. -/
theorem sourceRepresentative_existsUnique
    (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (P : CochainComplex (scalarReductionSource C.l (field D C E).carrier Y.obj.left) ℤ)
    (hp : proEtaleFlatRepresentatives Y.obj.left
      ((PurCompactSupport.completed C.l (field D C E).carrier).ring Y.obj.left) P)
    (K : Cat D C Y E) (e : DerivedCategory.Q.obj P ≅ K.obj) :
    ∃! r : DerivedCategory.Q.obj ((sourceComplex D C f d E).obj P) ≅
        ((source D C f d E).obj K).obj,
      ∃ (ht : proEtaleFlatRepresentatives X.obj.left
          ((PurCompactSupport.completed C.l (field D C E).carrier).ring X.obj.left)
          (sfOrientationIntegralComplex C.l (field D C E).carrier X.obj.left d))
        (hP : proEtaleFlatRepresentatives X.obj.left
          ((PurCompactSupport.completed C.l (field D C E).carrier).ring X.obj.left)
          (((pullModule D C f E).mapHomologicalComplex (.up ℤ)).obj P)),
        r = (tensorModel D C X E).representative.app (⟨_, ht⟩, ⟨_, hP⟩) ≪≫
          (tensorModel D C X E).tensor.mapIso (Iso.prod (Iso.refl _)
            (((pullModule D C f E).mapDerivedCategoryFactors.app P).symm ≪≫
              (PurCompactSupport.pull (PurCompactSupport.completed C.l
                (field D C E).carrier) f.hom.left).mapIso e)) := by
  sorry

/-- The canonical source comparison on a flat representative.
Source: source representative normalization
(blueprint: def-pur-adic-trace-source-coordinates). -/
def sourceRepresentative
    (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (P : CochainComplex (scalarReductionSource C.l (field D C E).carrier Y.obj.left) ℤ)
    (hp : proEtaleFlatRepresentatives Y.obj.left
      ((PurCompactSupport.completed C.l (field D C E).carrier).ring Y.obj.left) P)
    (K : Cat D C Y E) (e : DerivedCategory.Q.obj P ≅ K.obj) :=
  (sourceRepresentative_existsUnique D C f d E P hp K e).exists.choose

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

/-- Retain the published scalar shift as an instance at this coefficient inclusion.
Source: derived tensor shift
(blueprint: def-pur-adic-trace-source-coordinates). -/
instance scalarShift {E F : Padic.FiniteCoefficientFields C.l C.Qbar}
    (h : E ≤ F) (side : Bool) : (scalar D C f R h side).functor.CommShift ℤ :=
  (scalar D C f R h side).commShift

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

/-- The published projection transformation in ordinary tensor coordinates.
Source: PF_(T_E,K), proper counit followed by the inverse open-unit projection
(blueprint: def-pur-adic-trace-source-coordinates). -/
def projection (E : Padic.FiniteCoefficientFields C.l C.Qbar) (K : Cat D C Y E) :=
  ((PurCompactSupport.projectionMap (PurCompactSupport.completed C.l (field D C E).carrier)
    c (tensorModel D C X E)
    (RationalSmoothPurityCanonical.ordinaryModel C.l (field D C E).carrier c.Z)
    (tensorModel D C Y E)
    (PurCompactSupport.completedPull_comp C.l (field D C E).carrier c.i c.g)).app
      (line D C X E d).obj).app K.obj

/-- PF is invertible on precisely these inputs. Source: fix-prop-projection-formula
(blueprint: def-pur-adic-trace-source-coordinates).
Proof: apply the integral projection formula to the shifted Tate line and the
finite-Tor input K. The proper counit/open-unit construction of projection is
that formula after the normalized ordinary/completed comparison. Conjugating its
inverse by those comparisons proves this assertion. -/
theorem projection_isIso (E : Padic.FiniteCoefficientFields C.l C.Qbar) (K : Cat D C Y E) :
    IsIso (projection D C f c d E K) := by
  sorry

/-- Unit cancellation in the same normalized tensor coordinates.
Source: the tensor unit in the formula for u_E
(blueprint: def-pur-adic-trace-source-coordinates). -/
def tensorUnit (E : Padic.FiniteCoefficientFields C.l C.Qbar) (K : Cat D C Y E) :
    (tensorModel D C Y E).tensor.obj ((unit D C Y E).obj, K.obj) ≅ K.obj :=
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

/-- The projection-trace arrow in the published ordinary tensor coordinates.
The completed-coordinate version is adicTraceMap; here its completion comparisons
have already been cancelled by source and tensorModel.
Source: u_E=(t_E tensor 1) PF^-1
(blueprint: def-pur-adic-trace-source-coordinates). -/
def ordinaryTrace (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (t : (operation D C f c R E).F.obj (line D C X E d) ⟶ unit D C Y E)
    (K : Cat D C Y E) :
    (PurCompactSupport.image (PurCompactSupport.completed C.l (field D C E).carrier) c).obj
      ((source D C f d E).obj K).obj ⟶ K.obj :=
  @inv _ _ _ _ (projection D C f c d E K) (projection_isIso D C f c d E K) ≫
    (tensorModel D C Y E).tensor.map
      (Prod.mkHom ((R.left c (.integral (field D C E))).inv.app
        (line D C X E d) ≫ t.hom) (𝟙 K.obj)) ≫ (tensorUnit D C E K).hom

/-- The ordinary-coordinate trace map transported through the specified support
realization. In these j_E coordinates this is tilde-u_E.
Source: tilde-u_E=u_E P_E(j_E)
(blueprint: def-pur-adic-trace-source-coordinates). -/
def integrated (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (t : (operation D C f c R E).F.obj (line D C X E d) ⟶ unit D C Y E)
    (K : Cat D C Y E) :
    (operation D C f c R E).F.obj ((source D C f d E).obj K) ⟶ K :=
  ObjectProperty.homMk
    ((R.left c (.integral (field D C E))).hom.app ((source D C f d E).obj K) ≫
      ordinaryTrace D C f c d R E t K)

/-- The specified adjoint transpose, with canonical j_E coordinates built into source.
Source: gamma_E=adj_E(u_E) j_E
(blueprint: def-pur-adic-trace-source-coordinates). -/
def gamma (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (t : (operation D C f c R E).F.obj (line D C X E d) ⟶ unit D C Y E)
    (K : Cat D C Y E) :
    (source D C f d E).obj K ⟶ (operation D C f c R E).G.obj K :=
  ObjectProperty.homMk
    (adicTranspose D C (field D C E).carrier f.hom.left R c
      ((source D C f d E).obj K) K (ordinaryTrace D C f c d R E t K))

end WeilConjectures.AdicTraceTranspose
