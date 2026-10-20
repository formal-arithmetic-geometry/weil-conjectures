/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q132
-/
module

public import Sheaf.Paper.CurveMiddleExtension
public import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.AlgebraicGeometry.LisseTrivializedFiniteEtale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.NormalConstantOpenImage
import Sheaf.Paper.CommonStageCurveWeilMiddleExtension
import Sheaf.Paper.LisseIntegralSmallCoefficients
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Recovery of a lisse algebraic-coefficient sheaf from a dense open

Source: blueprint, sec-purity-real-sheaves, sk-i-real-boundary, Step 3;
Weil II (1.1.1) b)--d). (blueprint: lem-a1-lisse-middle-extension)

The unit below is formed from the actual ordinary etale adjunction units on the
integral model. The existing middle-extension realization places their ordinary
inverse limits in degree zero. Rationalization and the existing coefficient-stage
inclusion give the unit in the algebraic-coefficient pair category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Regard the whole curve as its own dense open, to use the same coefficient convention
on C as on U. No nonemptiness or connectedness is imposed.
Source: blueprint def-wf-middle-extension (blueprint: lem-a1-lisse-middle-extension). -/
def MiddleExtensionCurve.whole {D : WeilConjectures.FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) : MiddleExtensionCurve D where
  U := c.C
  C := c.C
  j := 𝟙 c.C
  dense := denseRange_id
  pureDimension := c.pureDimension

variable (l : ℕ) [Fact l.Prime] (Qbar : Type (u + 1)) [Field Qbar]
  [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]
  {D : WeilConjectures.FiniteFieldDatum.{u}} (c : MiddleExtensionCurve D) (hl : l ≠ D.p)

/-- The actual finite coefficient field of the pair representing F; localization does
not change objects. Source: Weil II (1.1.1) d)
(blueprint: lem-a1-lisse-middle-extension). -/
def curveLisseRecoveryStage (F : c.whole.LisseSheaf l hl Qbar) :
    Padic.FiniteCoefficientFields l Qbar :=
  letI := fun x : c.whole.U.left => ((c.whole.coefficientUnits l hl).1 x).invertible
  (lisseAlgebraicPair l c.whole.U.left Qbar F).base

/-- The integral diagram of the recorded rational model of F, without choosing a new
lattice or a trivializing cover. Source: Weil II (1.1.1) b)--d)
(blueprint: lem-a1-lisse-middle-extension). -/
def curveLisseRecoveryModel (F : c.whole.LisseSheaf l hl Qbar) :
    AdicIntegralDiagram l (curveLisseRecoveryStage l Qbar c hl F).val c.C.left :=
  letI := fun x : c.whole.U.left => ((c.whole.coefficientUnits l hl).1 x).invertible
  (lisseCoefficientPairModel l c.whole.U.left Qbar
    (lisseAlgebraicPair l c.whole.U.left Qbar F)).integral.obj

/-- Apply ordinary inverse image and direct image to every level of a diagram.
Source: blueprint Step 3; def-weil-pbc-inverse-image
(blueprint: lem-a1-lisse-middle-extension). -/
def curveLisseRecoveryDiagram (E : Padic.FiniteCoefficientFields l Qbar)
    (G : AdicIntegralDiagram l E.val c.C.left) :
    AdicIntegralDiagram l E.val c.C.left :=
  (G ⋙ Etale.upperStar
    (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val)) c.j.left) ⋙
    Etale.lowerStar
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val)) c.j.left

/-- The ordinary adjunction unit on inverse diagrams, with exactly the finite-level
units as components. Source: blueprint Step 3; def-weil-pbc-inverse-image
(blueprint: lem-a1-lisse-middle-extension). -/
def curveLisseRecoveryDiagramUnit (E : Padic.FiniteCoefficientFields l Qbar)
    (G : AdicIntegralDiagram l E.val c.C.left) :
    G ⟶ curveLisseRecoveryDiagram l Qbar c E G :=
  ((Etale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val)) c.j.left).whiskerRight
      ℕᵒᵖ).unit.app G

/-- Realize a coefficient diagram by ordinary inverse limit and placement in degree zero.
This reuses the middle-extension coefficient transport, with the identity direct image.
Source: def-wf-middle-extension, ordinary direct-image convention
(blueprint: lem-a1-lisse-middle-extension). -/
def curveLisseRecoveryRealization (E : Padic.FiniteCoefficientFields l Qbar) :
    AdicIntegralDiagram l E.val c.C.left ⥤ pbcAmbientStage l Qbar c.C.left E :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (middleExtensionLevelFunctor l Qbar E (𝟙 c.C.left)) ⋙
    lim ⋙ DerivedCategory.singleFunctor _ 0

/-- Both ends of the ordinary unit have bounded constructible complete realizations.
Source: blueprint sk-i-real-boundary, Step 3; Weil II (1.1.1) b)--d)
(blueprint: lem-a1-lisse-middle-extension).
Proof: take the recorded integral model. At each finite quotient its sheaf is finite
locally constant. Finite type over the finite field implies noetherianity, and
smoothness implies normality. Decompose into normal integral clopen components.
A finite etale surjection trivializes the finite quotient sheaf. Its normal integral
components meet the pulled-back dense open. On each, the constant-sheaf open-image
lemma identifies the actual unit with an isomorphism. Glue its inverses uniquely
using the sheaf equalizer. Naturality of the unit makes these inverses commute with
the coefficient transitions. Thus the target integral diagram is isomorphic to the
source, rather than requiring arbitrary direct image to preserve adic systems.
The ordinary inverse limit is the complete lisse module realization. Such a finite
lisse model is constructible, with bounded derived reductions over its coefficient
DVR, and satisfies the normalized etale-origin condition. The same three conditions
hold for the target by the constructed isomorphism. This proves both memberships. -/
theorem curveLisseRecoveryRealization_mem (F : c.whole.LisseSheaf l hl Qbar) :
    PbcIsBoundedConstructibleComplete c.C.left
      (pbcStageDatum.{u} l Qbar (curveLisseRecoveryStage l Qbar c hl F))
      ((curveLisseRecoveryRealization l Qbar c
        (curveLisseRecoveryStage l Qbar c hl F)).obj
          (curveLisseRecoveryModel l Qbar c hl F)) ∧
    PbcIsBoundedConstructibleComplete c.C.left
      (pbcStageDatum.{u} l Qbar (curveLisseRecoveryStage l Qbar c hl F))
      ((curveLisseRecoveryRealization l Qbar c
        (curveLisseRecoveryStage l Qbar c hl F)).obj
          (curveLisseRecoveryDiagram l Qbar c
            (curveLisseRecoveryStage l Qbar c hl F)
            (curveLisseRecoveryModel l Qbar c hl F))) := by
  sorry

/-- The integral degree-zero realization of F on the whole curve.
Source: def-wf-middle-extension, coefficient interpretation
(blueprint: lem-a1-lisse-middle-extension). -/
def curveLisseRecoverySource (F : c.whole.LisseSheaf l hl Qbar) :
    pbcIntegralStage l Qbar c.C.left (curveLisseRecoveryStage l Qbar c hl F) :=
  ⟨(curveLisseRecoveryRealization l Qbar c
      (curveLisseRecoveryStage l Qbar c hl F)).obj
        (curveLisseRecoveryModel l Qbar c hl F),
    (curveLisseRecoveryRealization_mem l Qbar c hl F).1⟩

/-- The integral degree-zero realization of ordinary j_*j^*F. Its construction
uses no derived direct image. Source: blueprint Step 3
(blueprint: lem-a1-lisse-middle-extension). -/
def curveLisseRecoveryTarget (F : c.whole.LisseSheaf l hl Qbar) :
    pbcIntegralStage l Qbar c.C.left (curveLisseRecoveryStage l Qbar c hl F) :=
  ⟨(curveLisseRecoveryRealization l Qbar c
      (curveLisseRecoveryStage l Qbar c hl F)).obj
        (curveLisseRecoveryDiagram l Qbar c (curveLisseRecoveryStage l Qbar c hl F)
          (curveLisseRecoveryModel l Qbar c hl F)),
    (curveLisseRecoveryRealization_mem l Qbar c hl F).2⟩

/-- Rationalize at the actual field E and include it into the recorded Qbar pair
category. Source: Weil II (1.1.1) c)--d); def-wf-middle-extension
(blueprint: lem-a1-lisse-middle-extension). -/
def curveLisseRecoveryPairFunctor (E : Padic.FiniteCoefficientFields l Qbar) :
    pbcIntegralStage l Qbar c.C.left E ⥤ c.CoefficientCategory l hl Qbar :=
  pbcStageLocalization l Qbar c.C.left E ⋙
    (pbcScalarSystem l Qbar c.C.left c.baseProperties.2.2.2.2
      (c.coefficientUnits l hl).2).ι E

/-- The actual unit of ordinary j^* and j_* in the algebraic-coefficient category.
The chosen coefficient stage is part of F, and both the integral arrow and its
images under rationalization and stage inclusion are specified constructions.
Source: blueprint Step 3; Weil II (1.1.1) b)--d)
(blueprint: lem-a1-lisse-middle-extension). -/
def curveLisseRecoveryUnit (F : c.whole.LisseSheaf l hl Qbar) :
    (curveLisseRecoveryPairFunctor l Qbar c hl
      (curveLisseRecoveryStage l Qbar c hl F)).obj
        (curveLisseRecoverySource l Qbar c hl F) ⟶
    (curveLisseRecoveryPairFunctor l Qbar c hl
      (curveLisseRecoveryStage l Qbar c hl F)).obj
        (curveLisseRecoveryTarget l Qbar c hl F) :=
  (curveLisseRecoveryPairFunctor l Qbar c hl
    (curveLisseRecoveryStage l Qbar c hl F)).map
      (ObjectProperty.homMk
        ((curveLisseRecoveryRealization l Qbar c
          (curveLisseRecoveryStage l Qbar c hl F)).map
            (curveLisseRecoveryDiagramUnit l Qbar c
              (curveLisseRecoveryStage l Qbar c hl F)
              (curveLisseRecoveryModel l Qbar c hl F))))

/-- Recovery from a dense lisse open: the actual unit F → j_*j^*F is invertible
for every lisse Qbar sheaf on the whole smooth curve.
Source: blueprint lem-a1-lisse-middle-extension, sk-i-real-boundary Step 3
(blueprint: lem-a1-lisse-middle-extension).
Proof: represent F by its finite-extension integral model. At each finite
coefficient level use finite type over the finite field to obtain noetherianity,
and smoothness to obtain normality. Decompose the curve into its finitely many
normal integral clopen components. Trivialize the finite locally constant sheaf
by a finite etale surjection; its normal integral components have nonempty dense
pullback of U, since etale maps are open. On each component apply the constant
normal-scheme open-image theorem to the actual restriction unit. Glue the unique
inverse sections along this etale cover using the sheaf equalizer, obtaining an
inverse module-sheaf map on every finite level. Naturality of the units shows
that these inverses commute with the transition maps. They therefore invert the
unit on integral diagrams. Ordinary coefficient transport, inverse limit and
placement in degree zero preserve the inverse equations. Finally rationalize
at the recorded field E and apply its inclusion into the coefficient pair
category. These functors preserve the inverse equations, so the displayed unit
is an isomorphism. No single finite cover trivializing all levels is assumed.
Empty curves have the unique unit; the clopen argument covers disconnected curves.
Naturality also makes any supplied Weil descent commute with the inverse. -/
theorem isIso_curveLisseRecoveryUnit (F : c.whole.LisseSheaf l hl Qbar) :
    IsIso (curveLisseRecoveryUnit l Qbar c hl F) := by
  sorry

end AlgebraicGeometry.Scheme
