/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CurveMiddleExtension
public import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.ConstructibleSheaf.DenseOpenUnit
import WeilConjectures.AlgebraicGeometry.PbcScalarTriangulation

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

/-- The ordinary unit on the recorded integral diagram is invertible: levelwise the
regular-scheme dense-open unit theorem, the curve being smooth (hence regular) and
noetherian, and each level finite locally constant
(blueprint: lem-wf-regular-locally-constant-dense-open-unit). -/
private theorem recoveryDiagramUnit_isIso (F : c.whole.LisseSheaf l hl Qbar) :
    IsIso (curveLisseRecoveryDiagramUnit l Qbar c
      (curveLisseRecoveryStage l Qbar c hl F) (curveLisseRecoveryModel l Qbar c hl F)) := by
  let := fun x : c.whole.U.left ↦ ((c.whole.coefficientUnits l hl).1 x).invertible
  let : IsRegular c.C.left := IsRegular.of_smooth c.C.hom
  let M := (lisseCoefficientPairModel l c.whole.U.left Qbar
    (lisseAlgebraicPair l c.whole.U.left Qbar F)).integral
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  change IsIso ((Etale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l
      (curveLisseRecoveryStage l Qbar c hl F).val)) c.j.left).unit.app (M.obj.obj n))
  let : IsFiniteLocallyConstantSheaf (M.obj.obj n) := M.property.1 n.unop
  exact Etale.isIso_unit_upperStarLowerStarAdjunction_of_isRegular c.j.left c.dense _

/-- Both ends of the ordinary unit have bounded constructible complete realizations.
Source: blueprint sk-i-real-boundary, Step 3; Weil II (1.1.1) b)--d)
(blueprint: lem-a1-lisse-middle-extension).
Proof: the source is the existing middle-extension membership theorem
middleExtensionIntegralComplex_mem applied to the whole curve and the recorded
integral model; its identity direct image, inverse limit and degree-zero placement
are this realization. Smoothness gives regularity, and the curve is noetherian,
so the regular-scheme dense-open unit theorem
(lem-wf-regular-locally-constant-dense-open-unit) inverts the ordinary unit at
every finite level, each level being finite locally constant. A natural
transformation with invertible components is invertible, so the diagram unit is
an isomorphism, and its realization transports membership to the target by
isomorphism closure of the bounded constructible complete predicate. -/
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
  let := fun x : c.whole.U.left ↦ ((c.whole.coefficientUnits l hl).1 x).invertible
  let := Fact.mk c.baseProperties.2.2.2.2
  let := Fact.mk (c.coefficientUnits l hl).2
  let E := curveLisseRecoveryStage l Qbar c hl F
  let M := (lisseCoefficientPairModel l c.whole.U.left Qbar
    (lisseAlgebraicPair l c.whole.U.left Qbar F)).integral
  have hsource : PbcIsBoundedConstructibleComplete c.C.left (pbcStageDatum.{u} l Qbar E)
      ((curveLisseRecoveryRealization l Qbar c E).obj M.obj) :=
    middleExtensionIntegralComplex_mem l Qbar c.whole E M
  have hunit : IsIso (curveLisseRecoveryDiagramUnit l Qbar c E M.obj) :=
    recoveryDiagramUnit_isIso l Qbar c hl F
  exact ⟨hsource, ObjectProperty.prop_of_iso
    (PbcIsBoundedConstructibleComplete c.C.left (pbcStageDatum.{u} l Qbar E))
    ((curveLisseRecoveryRealization l Qbar c E).mapIso
      (asIso (curveLisseRecoveryDiagramUnit l Qbar c E M.obj))) hsource⟩

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
Proof: at every finite level of the recorded integral model the ordinary unit is
invertible by the regular-scheme dense-open unit theorem
(lem-wf-regular-locally-constant-dense-open-unit), which needs no connectedness or
nonemptiness; hence the diagram unit is an isomorphism. Its realization is an
isomorphism, which lifts to the full integral subcategory since both ends are
members. Rationalization and the stage inclusion are functors and preserve it, so
the displayed unit is an isomorphism. -/
theorem isIso_curveLisseRecoveryUnit (F : c.whole.LisseSheaf l hl Qbar) :
    IsIso (curveLisseRecoveryUnit l Qbar c hl F) := by
  let E := curveLisseRecoveryStage l Qbar c hl F
  let G := curveLisseRecoveryModel l Qbar c hl F
  let R := curveLisseRecoveryRealization l Qbar c E
  have hunit : IsIso (curveLisseRecoveryDiagramUnit l Qbar c E G) :=
    recoveryDiagramUnit_isIso l Qbar c hl F
  let f : curveLisseRecoverySource l Qbar c hl F ⟶
      curveLisseRecoveryTarget l Qbar c hl F :=
    ObjectProperty.homMk (R.map (curveLisseRecoveryDiagramUnit l Qbar c E G))
  have hf : IsIso f := (ObjectProperty.isIso_hom_iff f).mp (by
    change IsIso (R.map (curveLisseRecoveryDiagramUnit l Qbar c E G))
    infer_instance)
  change IsIso ((curveLisseRecoveryPairFunctor l Qbar c hl E).map f)
  infer_instance

end AlgebraicGeometry.Scheme
