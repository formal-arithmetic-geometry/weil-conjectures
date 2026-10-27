/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Sheaf.Paper.PurAdicReconstruction
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.SixFunctors.IntegralOperationShiftData
public import Sheaf.Paper.ConstructibleExceptionalCompositor
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.IntegralTwistDerivedScalarCanonical
public import Sheaf.Paper.SfIntegralConstructibleLinear
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Sheaf.Paper.TwistPreservesFiniteness

/-! # Natural integral smooth purity and its coefficient equations

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, Steps 2--3.
(blueprint: lem-pur-adic-purity-scalar-naturality).

Main definitions: `source`, `scalar`, `sourceScalarComponent`, `Data`.
The existence theorem is in `AdicPurityScalarNaturality`.

All coefficient fields are finite subfields of the fixed algebraic closure.
Scalar extension below is ordinary derived tensor, restricted to the uniform
finite-Tor category. The exceptional adjunction is the recorded normalized system.
-/



@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.AdicPurityScalarNaturality

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)

/-- Finite coefficient fields in the fixed closure, including the base field.
Source: purity transport Step 3 (blueprint: lem-pur-adic-purity-scalar-naturality). -/
abbrev Field := Padic.FiniteCoefficientFields C.l C.Qbar

/-- The existing uniform finite-Tor category, with its actual completed coefficients.
Source: purity conventions (blueprint: lem-pur-adic-purity-scalar-naturality). -/
abbrev Cat (E : Field D C) (W : Scheme.{u}) :=
  finiteTorConstructibleIntegralCategory C.l E.val W

/-- Triangulated closure with the coefficient stage fixed before instance search.
This is the existing integral closure theorem, applied to this finite field.
Source: integral finite-Tor convention
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
instance coefficientTriangulated (E : Field D C) (W : Scheme.{u}) :
    (finiteTorConstructibleIntegral C.l E.val W).IsTriangulated :=
  ConstructibleExceptionalCoefficients.integralTriangulated C.l { carrier := E.val } W

/-- A finite coefficient field as the argument of the recorded exceptional system.
Source: purity coefficient conventions
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
def fieldStage (E : Field D C) : ConstructibleExceptionalCoefficients.FieldStage C.l :=
  { carrier := E.val }

/-- Ordinary derived scalar extension along the actual completed coefficient inclusion.
Source: purity transport Step 3 (blueprint: lem-pur-adic-purity-scalar-naturality). -/
abbrev ordinary (E F : Field D C) (h : E ≤ F) (W : Scheme.{u}) :=
  integralOrdinaryDerivedScalar C.l E.val F.val (IntermediateField.inclusion h) W

/-- Preservation needed to restrict ordinary tensor, asserted in the theorem below.
Source: purity transport Step 3 (blueprint: lem-pur-adic-purity-scalar-naturality). -/
def ScalarClosed (X Y : Scheme.{u}) : Prop :=
  ∀ (E F : Field D C) (h : E ≤ F) (side : Bool)
    (K : Cat D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)),
    finiteTorConstructibleIntegral C.l F.val
      (ConstructibleExceptionalCoefficients.endpoint X Y side)
      ((ordinary D C E F h (ConstructibleExceptionalCoefficients.endpoint X Y side)).obj K.obj)

variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The actual ambient functor Lf*(-)(d)[2d], in the reconstruction presentation.
Source: thm-pur-adic-reconstruction
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
def ambientSource (E : Field D C) :=
  integralDerivedPullback C.l E.val f ⋙
    integralComplexTwist D C.l C.different E.val X (d : ℤ) ⋙
      shiftFunctor _ (2 * (d : ℤ))

/-- Restriction of that very source, using reconstruction only for membership.
Source: purity transport Step 2 (blueprint: lem-pur-adic-purity-scalar-naturality). -/
def source (E : Field D C) : Cat D C E Y ⥤ Cat D C E X :=
  (finiteTorConstructibleIntegral C.l E.val X).lift
    ((finiteTorConstructibleIntegral C.l E.val Y).ι ⋙ ambientSource D C f d E)
    (fun K ↦ (purAdicReconstruction D C E.val f d K.obj K.property).choose_spec.2.1)

/-- The ordinary scalar functor restricted through the existing full inclusion.
Source: purity transport Step 3 (blueprint: lem-pur-adic-purity-scalar-naturality). -/
def scalar (hC : ScalarClosed D C X Y) (E F : Field D C) (h : E ≤ F)
    (side : Bool) :
    Cat D C E (ConstructibleExceptionalCoefficients.endpoint X Y side) ⥤
      Cat D C F (ConstructibleExceptionalCoefficients.endpoint X Y side) :=
  (finiteTorConstructibleIntegral C.l F.val _).lift
    ((finiteTorConstructibleIntegral C.l E.val _).ι ⋙ ordinary D C E F h _)
    (hC E F h side)

/-- Tensor associativity restricted through the full inclusions.
Source: purity transport Step 3 (blueprint: lem-pur-adic-purity-scalar-naturality). -/
def associator (hC : ScalarClosed D C X Y) (E F L : Field D C)
    (h : E ≤ F) (k : F ≤ L) (side : Bool) :
    scalar D C hC E F h side ⋙ scalar D C hC F L k side ≅
      scalar D C hC E L (h.trans k) side :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      ((integralOrdinaryDerivedScalarComp C.l E.val F.val (IntermediateField.inclusion h)
        _ L.val (IntermediateField.inclusion k)).app K.obj))
    (fun v ↦ by
      apply ObjectProperty.hom_ext
      exact (integralOrdinaryDerivedScalarComp C.l E.val F.val
        (IntermediateField.inclusion h) _ L.val (IntermediateField.inclusion k)).hom.naturality
          v.hom)

attribute [local irreducible] associator

/-- Identity tensor multiplication restricted through the full inclusions.
Source: purity transport Step 3 (blueprint: lem-pur-adic-purity-scalar-naturality). -/
def scalarUnit (hC : ScalarClosed D C X Y) (E : Field D C) (side : Bool) :
    scalar D C hC E E le_rfl side ≅
      𝟭 (Cat D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)) :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      ((integralOrdinaryDerivedScalarUnit C.l E.val _).app K.obj))
    (fun v ↦ by
      apply ObjectProperty.hom_ext
      exact (integralOrdinaryDerivedScalarUnit C.l E.val _).hom.naturality v.hom)

attribute [local irreducible] scalarUnit

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two derived-reduction presentations are identified by their normalized
adjunctions to the same exact scalar restriction. The final transport removes the
identity quotient cast in the positive-level System projection.
Source: Stacks 06YY and purity transport Step 2
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[no_expose] def reductionBridge (E : Field D C) (W : Scheme.{u}) (n : ℕ) :
    scalarReductionDerivedExtension C.l E.val W n ≅
      Scheme.pbcDerivedExtend
        ((PurCompactSupport.reduction C.l E.val (n + 1) (Nat.succ_pos n)).map W) := by
  let φ := completedIntegralCommRingProjectionUnrestricted C.l E.val W n
  have hp : (PurCompactSupport.reduction C.l E.val (n + 1) (Nat.succ_pos n)).map W = φ := by
    dsimp only [PurCompactSupport.reduction, PurCompactSupport.projection, φ]
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  exact hp.symm ▸
    (derivedScalarExtensionRestrictionAdjunction C.l E.val W n).choose.leftAdjointUniq
      (Scheme.pbcDerivedScalarAdjunction φ)


attribute [local irreducible] reductionBridge

variable (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))

/-- The fixed exceptional and compact-support adjunction at a finite coefficient field.
Source: def-weil-exceptional-inverse-image
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
abbrev operation (E : Field D C) :=
  S.ring.operation (integralExceptionalCompactification D f) (.integral (fieldStage D C E))

/-- The exceptional functor in the normalized adjunction, on the stated full categories.
Source: exceptional inverse image (blueprint: lem-pur-adic-purity-scalar-naturality). -/
def target (E : Field D C) : Cat D C E Y ⥤ Cat D C E X :=
  (operation D C f S E).G

/-- Its adjunction shift, retained with the explicit finite-field index.
Source: exceptional adjunction shifts
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
instance targetShift (E : Field D C) : (target D C f S E).CommShift ℤ :=
  (operation D C f S E).rightShift

/-- The normalized scalar stage, whose realization is ordinary completed-ring tensor.
Source: exceptional coefficient comparisons
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
abbrev rawScalar (E F : Field D C) (h : E ≤ F) (side : Bool) :=
  S.ring.scalar (s := .integral (fieldStage D C E))
    (t := .integral (fieldStage D C F))
    (PurCompactSupport.completedChange C.l E.val F.val (IntermediateField.inclusion h))
    (.integral (fieldStage D C E) (fieldStage D C F) (IntermediateField.inclusion h)) side

/-- The scalar comparison of the normalized exceptional adjunction.
Source: exceptional coefficient comparisons
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
instance rawScalarShift (E F : Field D C) (h : E ≤ F) (side : Bool) :
    (rawScalar D C f S E F h side).functor.CommShift ℤ :=
  (rawScalar D C f S E F h side).commShift

/-- The compact-support and exceptional scalar mates, with their fixed counit equation.
Source: exceptional coefficient comparisons
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
def comparison (E F : Field D C) (h : E ≤ F) :=
  letI := (rawScalar D C f S E F h true).commShift
  letI := (rawScalar D C f S E F h false).commShift
  S.ring.comparison (integralExceptionalCompactification D f)
    (s := .integral (fieldStage D C E)) (t := .integral (fieldStage D C F))
    (PurCompactSupport.completedChange C.l E.val F.val (IntermediateField.inclusion h))
    (.integral (fieldStage D C E) (fieldStage D C F) (IntermediateField.inclusion h))

/-- The normalized compact-support coefficient comparison, with shifts supplied
explicitly to the bundled mate projection.
Source: exceptional coefficient comparison
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
def compactComparison (E F : Field D C) (h : E ≤ F) :
    (operation D C f S E).F ⋙ (rawScalar D C f S E F h false).functor ≅
      (rawScalar D C f S E F h true).functor ⋙ (operation D C f S F).F := by
  letI := (rawScalar D C f S E F h true).commShift
  letI := (rawScalar D C f S E F h false).commShift
  exact (comparison D C f S E F h).q

attribute [local irreducible] comparison compactComparison

/-- The finite coefficient ring, with the existing positive-level finiteness instance.
Source: purity transport Step 2
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
abbrev finiteRing (E : Field D C) (n : ℕ+) := Padic.coefficientExtensionRing C.l E.val n

/-- Finiteness at every positive coefficient level.
Source: purity coefficient convention
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
instance finiteRingFinite (E : Field D C) (n : ℕ+) : Finite (finiteRing D C E n) :=
  Padic.finite_coefficientExtensionRing C.l E.val n n.pos

/-- Canonical fixed-scalar realization of the finite compact-support operation.
Every comparison here is fixed by the ordinary open unit or proper derived unit.
Source: exceptional adjunction construction, finite-level Step 2
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[no_expose] def finiteLeftFixed (E : Field D C) (n : ℕ+)
    (M : finiteTorConstructibleCategory C.l E.val n n.pos X) :
    (Scheme.sfIntrinsicDerivedEquivalence Y (finiteRing D C E n)).inverse.obj
        (((S.ring.operation (integralExceptionalCompactification D f)
          (.finite (fieldStage D C E) n)).F.obj M).obj) ≅
      (ProEtale.sfFixedCompactSupport (finiteRing D C E n)
        (integralExceptionalCompactification D f)).obj
          ((Scheme.sfIntrinsicDerivedEquivalence X (finiteRing D C E n)).inverse.obj
            M.obj) := by
  letI : Finite (finiteRing D C E n) :=
    Padic.finite_coefficientExtensionRing C.l E.val n n.pos
  let c := integralExceptionalCompactification D f
  let eX := Scheme.sfIntrinsicDerivedEquivalence X (finiteRing D C E n)
  let eY := Scheme.sfIntrinsicDerivedEquivalence Y (finiteRing D C E n)
  let P := Scheme.sfIntrinsicCompactSupport c (finiteRing D C E n)
  exact eY.inverse.mapIso
      ((S.ring.left c (.finite (fieldStage D C E) n)).app M ≪≫
        (constructibleFiniteImageIso C.l E.val n c).app M.obj ≪≫
        P.mapIso (eX.counitIso.app M.obj).symm ≪≫
        (ProEtale.sfIntrinsicCompactSupportComparison (finiteRing D C E n) c).app
          (eX.inverse.obj M.obj)) ≪≫
    (eY.unitIso.app _).symm

attribute [local irreducible] finiteLeftFixed

/-- The same finite right realization in fixed-scalar coordinates, using only the
specified realization equivalence and its unit.
Source: exceptional adjunction construction, finite-level Step 2
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[no_expose] def finiteRightFixed (E : Field D C) (n : ℕ+)
    (N : finiteTorConstructibleCategory C.l E.val n n.pos Y) :
    (Scheme.sfIntrinsicDerivedEquivalence X (finiteRing D C E n)).inverse.obj
        (((S.ring.operation (integralExceptionalCompactification D f)
          (.finite (fieldStage D C E) n)).G.obj N).obj) ⟶
      (@ProEtale.sfFiniteExceptionalFixed (finiteRing D C E n) _
        (Padic.finite_coefficientExtensionRing C.l E.val n n.pos) X Y f
        (integralExceptionalCompactification D f)).obj
          ((Scheme.sfIntrinsicDerivedEquivalence Y (finiteRing D C E n)).inverse.obj
            N.obj) := by
  letI : Finite (finiteRing D C E n) :=
    Padic.finite_coefficientExtensionRing C.l E.val n n.pos
  exact (Scheme.sfIntrinsicDerivedEquivalence X (finiteRing D C E n)).inverse.map
      ((S.ring.finiteRight (integralExceptionalCompactification D f)
        (fieldStage D C E) n).hom.app N) ≫
    (Scheme.sfIntrinsicDerivedEquivalence X (finiteRing D C E n)).unitIso.inv.app _

attribute [local irreducible] finiteRightFixed

/-- The finite right realization is the Hom-transpose comparison of adjoints.
For every bounded-below etale representative and every map, its composition with
the system transpose is exactly the ordinary etale transpose, transported through
the canonical compact-support comparison and the derived comparison adjunction.
This pins finiteRight independently of gamma and of targetRealization.
Source: exceptional inverse image, finite adjunction and purity transport Step 2
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[no_expose] def FiniteRightNormalized : Prop := by
  refine ∀ (E : Field D C) (n : ℕ+), ?_
  letI : Finite (finiteRing D C E n) :=
    Padic.finite_coefficientExtensionRing C.l E.val n n.pos
  let A := ULift.{u + 1, u} (finiteRing D C E n)
  let c := integralExceptionalCompactification D f
  letI := c.hasCompactification
  let O := S.ring.operation c (.finite (fieldStage D C E) n)
  let eX := Scheme.sfIntrinsicDerivedEquivalence X (finiteRing D C E n)
  let eY := Scheme.sfIntrinsicDerivedEquivalence Y (finiteRing D C E n)
  let U := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let P := ProEtale.sfFixedCompactSupport (finiteRing D C E n) c
  let adj := (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).ofNatIsoLeft
    (Etale.rightDerivedLowerShriekIso A c).symm
  exact ∀ (M : finiteTorConstructibleCategory C.l E.val n n.pos X)
    (N : finiteTorConstructibleCategory C.l E.val n n.pos Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : U.obj K.obj ≅ eX.inverse.obj M.obj) (v : O.F.obj M ⟶ N),
    e.hom ≫ eX.inverse.map ((O.adjunction.homEquiv M N v).hom) ≫
        finiteRightFixed D C f S E n N =
      U.map (adj.homEquiv K.obj _
        ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ _
          ((ProEtale.fixedCompactSupportComparisonIso A c).inv.app K ≫
            P.map e.hom ≫ (finiteLeftFixed D C f S E n M).inv ≫ eY.inverse.map v.hom)))

attribute [local irreducible] FiniteRightNormalized

/-- The exceptional reduction of the normalized adjunction, in reconstruction's
finite target. The scalar realizations are the recorded integral-to-finite maps;
the middle arrows are the specified coefficient mate and finite right realization.
Source: purity transport Step 2 and reconstruction target normalization
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[no_expose] def targetReductionMap (E : Field D C) (K : Cat D C E Y) (n : ℕ) :
    (scalarReductionDerivedExtension C.l E.val X n).obj
        (((target D C f S E).obj K).obj) ⟶
      (@ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing C.l E.val (n + 1)) _
        (Padic.finite_coefficientExtensionRing C.l E.val (n + 1) (Nat.succ_pos n)) X Y f
        (integralExceptionalCompactification D f)).obj
          ((scalarReductionDerivedExtension C.l E.val Y n).obj K.obj) := by
  let N : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
  let a := PurCompactSupport.reduction C.l E.val N N.pos
  let ha := ConstructibleExceptionalCoefficients.Allowed.reduction (fieldStage D C E) N
  let RX := S.ring.scalar (s := .integral (fieldStage D C E))
    (t := .finite (fieldStage D C E) N) a ha true
  let RY := S.ring.scalar (s := .integral (fieldStage D C E))
    (t := .finite (fieldStage D C E) N) a ha false
  letI := RX.commShift
  letI := RY.commShift
  let B := S.ring.comparison (integralExceptionalCompactification D f)
    (s := .integral (fieldStage D C E)) (t := .finite (fieldStage D C E) N) a ha
  let J := RY.functor.obj K
  let G := @ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing C.l E.val N) _
    (Padic.finite_coefficientExtensionRing C.l E.val N N.pos) X Y f
    (integralExceptionalCompactification D f)
  let rX := RX.realization.inv.app ((target D C f S E).obj K)
  let b := (B.b.hom.app K).hom
  let rG := (S.ring.finiteRight (integralExceptionalCompactification D f)
    (fieldStage D C E) N).hom.app J
  let rY := G.map (RY.realization.hom.app K ≫
    (reductionBridge D C E Y n).inv.app K.obj)
  exact (reductionBridge D C E X n).hom.app ((target D C f S E).obj K).obj ≫
    rX ≫ b ≫ rG ≫ rY


attribute [local irreducible] targetReductionMap

/-- Canonical passage from the ordinary tensor presentation to the normalized scalar
stage: completion chi followed by the recorded strict-tower realization.
Source: finite-free completed scalar comparison
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[no_expose] def scalarBridge (hC : ScalarClosed D C X Y) (E F : Field D C) (h : E ≤ F)
    (side : Bool) (K : Cat D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)) :
    (scalar D C hC E F h side).obj K ≅
      (rawScalar D C f S E F h side).functor.obj K :=
  ObjectProperty.isoMk _
    (scalarCompletionIso C.l E.val F.val (IntermediateField.inclusion h) _ K.obj
      K.property.1.1 ≪≫
    ((eqToIso (S.ring.integralScalar_eq (fieldStage D C E) (fieldStage D C F)
      (IntermediateField.inclusion h) side)).symm.app K))


attribute [local irreducible] scalarBridge

/-- The inherited constant-section linear structure on the full finite-Tor category.
Source: def-weil-linear-functor
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
instance coefficientLinear (E : Field D C) (W : Scheme.{u}) :
    Linear (Padic.coefficientExtensionIntegers C.l E.val) (Cat D C E W) :=
  Linear.fullSubcategory (finiteTorConstructibleIntegral C.l E.val W)

attribute [local irreducible] coefficientLinear

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source shifts are inherited from actual derived pullback, twist and shift.
Source: purity transport Step 2 (blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[no_expose] instance sourceShift (E : Field D C) : (source D C f d E).CommShift ℤ := by
  letI := (IntegralSystemRealization.integralShifts C.l E.val).pull f
  letI : (ambientSource D C f d E).CommShift ℤ := by
    dsimp [ambientSource, integralComplexTwist]
    infer_instance
  dsimp only [source]
  infer_instance

attribute [local irreducible] sourceShift

/-- Ordinary scalar shifts are the ones inherited from derived tensor.
Source: purity transport Step 3 (blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[no_expose] instance scalarShift (hC : ScalarClosed D C X Y) (E F : Field D C)
    (h : E ≤ F) (side : Bool) : (scalar D C hC E F h side).CommShift ℤ := by
  dsimp only [scalar]
  infer_instance


attribute [local irreducible] scalarShift

/-- The canonical source scalar component. Move the shift through ordinary tensor,
then use completed twist and pullback comparisons, conjugated by completion chi.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[no_expose] def sourceScalarComponent (hC : ScalarClosed D C X Y) (E F : Field D C)
    (h : E ≤ F) (K : Cat D C E Y) :
    ((scalar D C hC E F h true).obj ((source D C f d E).obj K)).obj ≅
      ((source D C f d F).obj ((scalar D C hC E F h false).obj K)).obj := by
  let P := (constructibleIntegralPullback C.l E.val f).obj ⟨K.obj, K.property.1⟩
  have ht : IsSfDerivedComplete C.l E.val X
      ((integralComplexTwist D C.l C.different E.val X (d : ℤ)).obj P.obj) :=
    ((twist_preserves_finiteness C.l E.val X C.Qbar (d : ℤ)).2.2.2.2.2.2.2.2.1
      P.obj P.property).1
  let chiX := scalarCompletionIso C.l E.val F.val (IntermediateField.inclusion h) X
    ((integralComplexTwist D C.l C.different E.val X (d : ℤ)).obj P.obj) ht
  let beta := (integralTwistCompletedBeta C.l E.val F.val (IntermediateField.inclusion h)
    X (d : ℤ)).app P
  let chiY := scalarCompletionIso C.l E.val F.val (IntermediateField.inclusion h) Y
    K.obj K.property.1.1
  let pull := scalarPullbackCompleted C.l E.val F.val (IntermediateField.inclusion h) f
    K.obj K.property.1.1 P.property.1
  let pullChi := (integralDerivedPullback C.l F.val f).mapIso chiY.symm
  let twist := (integralComplexTwist D C.l C.different F.val X (d : ℤ)).mapIso
    (pull ≪≫ pullChi)
  let comparison := chiX ≪≫ beta ≪≫ twist
  let shift := ((ordinary D C E F h X).commShiftIso (2 * (d : ℤ))).app
    ((integralComplexTwist D C.l C.different E.val X (d : ℤ)).obj P.obj)
  exact shift ≪≫ (shiftFunctor _ (2 * (d : ℤ))).mapIso comparison


attribute [local irreducible] sourceScalarComponent

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Explicit composition of the recorded shift structures, without re-inferring
coefficient stages from their underlying carriers.
Source: purity transport shift equations
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[instance_reducible] def composeShift {A B V : Type (u + 2)} [Category.{u + 2} A]
    [Category.{u + 2} B] [Category.{u + 2} V]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift V ℤ]
    (F : A ⥤ B) (G : B ⥤ V) (sF : F.CommShift ℤ) (sG : G.CommShift ℤ) :
    (F ⋙ G).CommShift ℤ :=
  @Functor.CommShift.comp A B V _ _ _ F G ℤ _ _ _ _ sF sG

/-- Mathlib's shift compatibility, with the two canonical structures made explicit.
Source: purity transport shift equations
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
abbrev ShiftCompatibility {A B : Type (u + 2)} [Category.{u + 2} A]
    [Category.{u + 2} B] [HasShift A ℤ] [HasShift B ℤ]
    (F G : A ⥤ B) (sF : F.CommShift ℤ) (sG : G.CommShift ℤ) (e : F ≅ G) : Prop :=
  @NatTrans.CommShift A B _ _ F G e.hom ℤ _ _ _ sF sG

attribute [local irreducible] rawScalarShift targetShift composeShift

/-- The prescribed finite reductions of the same purity family, in the canonical
exceptional realization. Source: adic reconstruction, Step 2
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[no_expose] def FiniteReductions
    (gamma : ∀ E : Field D C, source D C f d E ≅ target D C f S E)
    (targetRealization : ∀ E : Field D C,
      target D C f S E ⋙ (finiteTorConstructibleIntegral C.l E.val X).ι ≅
        (finiteTorConstructibleIntegral C.l E.val Y).ι ⋙
          integralExceptionalInverseImage C.l E.val D C.different f) : Prop :=
  ∀ (E : Field D C) (K : Cat D C E Y) (n : ℕ),
    IsIso (purAdicSourceReduction D C E.val f d K.obj K.property n) ∧
    IsIso (purAdicTargetReduction D C E.val f d K.obj K.property n) ∧
    (scalarReductionDerivedExtension C.l E.val X n).map
        (((gamma E).hom.app K).hom ≫ (targetRealization E).hom.app K) ≫
        purAdicTargetReduction D C E.val f d K.obj K.property n =
      purAdicSourceReduction D C E.val f d K.obj K.property n ≫
        (purAdicFiniteArrow D C E.val f d K.obj K.property n).hom

/-- The coefficient comparison is the counit transpose for the fixed adjunction.
Source: coefficient mate equation, Step 3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[no_expose] def CoefficientMate (hC : ScalarClosed D C X Y)
    (c : ∀ (E F : Field D C) (h : E ≤ F),
      (operation D C f S E).F ⋙ scalar D C hC E F h false ≅
        scalar D C hC E F h true ⋙ (operation D C f S F).F)
    (b : ∀ (E F : Field D C) (h : E ≤ F),
      target D C f S E ⋙ scalar D C hC E F h true ≅
        scalar D C hC E F h false ⋙ target D C f S F) : Prop :=
  ∀ (E F : Field D C) (h : E ≤ F) (K : Cat D C E Y),
    (b E F h).hom.app K =
      ((operation D C f S F).adjunction.homEquiv _ _)
        ((c E F h).inv.app ((target D C f S E).obj K) ≫
          (scalar D C hC E F h false).map
            ((operation D C f S E).adjunction.counit.app K))

/-- The exceptional realization has the prescribed canonical finite reductions.
Source: reconstruction target normalization, Step 2
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
def TargetRealizationReductions
    (targetRealization : ∀ E : Field D C,
      target D C f S E ⋙ (finiteTorConstructibleIntegral C.l E.val X).ι ≅
        (finiteTorConstructibleIntegral C.l E.val Y).ι ⋙
          integralExceptionalInverseImage C.l E.val D C.different f) : Prop :=
  ∀ (E : Field D C) (K : Cat D C E Y) (n : ℕ),
    (scalarReductionDerivedExtension C.l E.val X n).map
        ((targetRealization E).hom.app K) ≫
        purAdicTargetReduction D C E.val f d K.obj K.property n =
      targetReductionMap D C f S E K n

attribute [local irreducible] scalar source target FiniteReductions CoefficientMate
  TargetRealizationReductions

/-- The purity square and its tensor-unit, composition and shift equations.
Every conjunct is the corresponding displayed equation of coefficient naturality.
Source: purity transport, Step 3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
def Coherence (scalarClosed : ScalarClosed D C X Y)
    (gamma : ∀ E : Field D C, source D C f d E ≅ target D C f S E)
    (a : ∀ (E F : Field D C) (h : E ≤ F),
      source D C f d E ⋙ scalar D C scalarClosed E F h true ≅
        scalar D C scalarClosed E F h false ⋙ source D C f d F)
    (b : ∀ (E F : Field D C) (h : E ≤ F),
      target D C f S E ⋙ scalar D C scalarClosed E F h true ≅
        scalar D C scalarClosed E F h false ⋙ target D C f S F) : Prop :=
    (∀ (E F : Field D C) (h : E ≤ F) (K : Cat D C E Y),
    (scalar D C scalarClosed E F h true).map ((gamma E).hom.app K) ≫
        (b E F h).hom.app K =
      (a E F h).hom.app K ≫
        (gamma F).hom.app ((scalar D C scalarClosed E F h false).obj K)) ∧
    (∀ (E : Field D C) (K : Cat D C E Y),
    (a E E le_rfl).hom.app K ≫
        (source D C f d E).map ((scalarUnit D C scalarClosed E false).hom.app K) =
      (scalarUnit D C scalarClosed E true).hom.app ((source D C f d E).obj K)) ∧
    (∀ (E : Field D C) (K : Cat D C E Y),
    (b E E le_rfl).hom.app K ≫
        (target D C f S E).map ((scalarUnit D C scalarClosed E false).hom.app K) =
      (scalarUnit D C scalarClosed E true).hom.app ((target D C f S E).obj K)) ∧
    (∀ (E F L : Field D C) (h : E ≤ F) (k : F ≤ L) (K : Cat D C E Y),
    (associator D C scalarClosed E F L h k true).hom.app ((source D C f d E).obj K) ≫
        (a E L (h.trans k)).hom.app K =
      (scalar D C scalarClosed F L k true).map ((a E F h).hom.app K) ≫
        (a F L k).hom.app ((scalar D C scalarClosed E F h false).obj K) ≫
        (source D C f d L).map ((associator D C scalarClosed E F L h k false).hom.app K)) ∧
    (∀ (E F L : Field D C) (h : E ≤ F) (k : F ≤ L) (K : Cat D C E Y),
    (associator D C scalarClosed E F L h k true).hom.app
        ((target D C f S E).obj K) ≫ (b E L (h.trans k)).hom.app K =
      (scalar D C scalarClosed F L k true).map ((b E F h).hom.app K) ≫
        (b F L k).hom.app ((scalar D C scalarClosed E F h false).obj K) ≫
        (target D C f S L).map
          ((associator D C scalarClosed E F L h k false).hom.app K)) ∧
    (∀ (E F : Field D C) (h : E ≤ F),
    ShiftCompatibility
      (source D C f d E ⋙ scalar D C scalarClosed E F h true)
      (scalar D C scalarClosed E F h false ⋙ source D C f d F)
      (composeShift (source D C f d E) (scalar D C scalarClosed E F h true)
        (sourceShift D C f d E) (scalarShift D C scalarClosed E F h true))
      (composeShift (scalar D C scalarClosed E F h false) (source D C f d F)
        (scalarShift D C scalarClosed E F h false) (sourceShift D C f d F)) (a E F h)) ∧
    (∀ (E F : Field D C) (h : E ≤ F),
    ShiftCompatibility
      (target D C f S E ⋙ scalar D C scalarClosed E F h true)
      (scalar D C scalarClosed E F h false ⋙ target D C f S F)
      (composeShift (target D C f S E) (scalar D C scalarClosed E F h true)
        (targetShift D C f S E) (scalarShift D C scalarClosed E F h true))
      (composeShift (scalar D C scalarClosed E F h false) (target D C f S F)
        (scalarShift D C scalarClosed E F h false) (targetShift D C f S F)) (b E F h)) ∧
    (∀ (E : Field D C),
    ShiftCompatibility (source D C f d E) (target D C f S E)
      (sourceShift D C f d E) (targetShift D C f S E) (gamma E))

attribute [local irreducible] Coherence


/-- Named operation property, retaining the original finite-Tor functor and structures.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[irreducible] def SourceAdditiveProperty (E : Field D C) : Prop := (source D C f d E).Additive

/-- Named operation property, retaining the original finite-Tor functor and structures.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[irreducible] def SourceExactProperty (E : Field D C) : Prop := (source D C f d E).IsTriangulated

/-- Named operation property, retaining the original finite-Tor functor and structures.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[irreducible] def SourceLinearProperty (E : Field D C) : Prop :=
  (source D C f d E).Linear (Padic.coefficientExtensionIntegers C.l E.val)

/-- Named operation property, retaining the original finite-Tor functor and structures.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[irreducible] def TargetLinearProperty (E : Field D C) : Prop :=
  (target D C f S E).Linear (Padic.coefficientExtensionIntegers C.l E.val)

/-- Named operation property, retaining the original finite-Tor functor and structures.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[irreducible] def TargetExactProperty (E : Field D C) : Prop := (target D C f S E).IsTriangulated

/-- Named operation property, retaining the original finite-Tor functor and structures.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[irreducible] def ScalarAdditiveProperty (scalarClosed : ScalarClosed D C X Y)
    (E F : Field D C) (h : E ≤ F) (side : Bool) : Prop :=
  (scalar D C scalarClosed E F h side).Additive

/-- Named operation property, retaining the original finite-Tor functor and structures.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
@[irreducible] def ScalarExactProperty (scalarClosed : ScalarClosed D C X Y)
    (E F : Field D C) (h : E ≤ F) (side : Bool) : Prop :=
  (scalar D C scalarClosed E F h side).IsTriangulated


/-- A generic container for a family of proof obligations. Its inductive checking
never unfolds the coefficient functors in a concrete family.
Source: elementary logical packaging
(blueprint: def-pur-adic-purity-scalar-naturality-data). -/
structure PropertyFamily {I : Sort*} (P : I → Prop) : Prop where
  property (i : I) : P i

/-- Source operation properties, with the original finite-Tor source functor.
Source: purity transport Steps 2--3
(blueprint: def-pur-adic-purity-scalar-naturality-data). -/
structure SourceOperationData : Prop where
  additiveFamily : PropertyFamily (fun E : Field D C ↦ SourceAdditiveProperty D C f d E)
  exactFamily : PropertyFamily (fun E : Field D C ↦ SourceExactProperty D C f d E)
  linearFamily : PropertyFamily (fun E : Field D C ↦ SourceLinearProperty D C f d E)

/-- The original source additive property, projected from its family.
Source: original operation data
(blueprint: def-pur-adic-purity-scalar-naturality-data). -/
abbrev SourceOperationData.sourceAdditive (P : SourceOperationData D C f d) :=
  P.additiveFamily.property

/-- The original source exact property, projected from its family.
Source: original operation data
(blueprint: def-pur-adic-purity-scalar-naturality-data). -/
abbrev SourceOperationData.sourceExact (P : SourceOperationData D C f d) :=
  P.exactFamily.property

/-- The original source linear property, projected from its family.
Source: original operation data
(blueprint: def-pur-adic-purity-scalar-naturality-data). -/
abbrev SourceOperationData.sourceLinear (P : SourceOperationData D C f d) :=
  P.linearFamily.property

/-- Exceptional operation properties for the recorded normalized adjunction.
Source: purity transport Steps 2--3
(blueprint: def-pur-adic-purity-scalar-naturality-data). -/
structure TargetOperationData : Prop where
  finiteRightNormalized : FiniteRightNormalized D C f S
  targetLinear (E : Field D C) : TargetLinearProperty D C f S E
  targetExact (E : Field D C) : TargetExactProperty D C f S E

/-- Ordinary scalar closure and its inherited additive and exact structures.
Source: purity transport Steps 2--3
(blueprint: def-pur-adic-purity-scalar-naturality-data). -/
structure ScalarOperationData : Prop where
  scalarClosed : ScalarClosed D C X Y
  scalarAdditive (E F : Field D C) (h : E ≤ F) (side : Bool) :
    ScalarAdditiveProperty D C (X := X) (Y := Y) scalarClosed E F h side
  scalarExact (E F : Field D C) (h : E ≤ F) (side : Bool) :
    ScalarExactProperty D C (X := X) (Y := Y) scalarClosed E F h side

/-- Exactness, linearity and scalar closure for the simultaneous purity family.
The property groups retain each original field, while avoiding repeated kernel
checking of their dependent coefficient-category instances.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
structure OperationData extends SourceOperationData D C f d,
    TargetOperationData D C f S, ScalarOperationData D C (X := X) (Y := Y)

/-- The normalized comparisons of the same simultaneous purity family.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
structure ComparisonData extends OperationData D C f d S where
  gamma (E : Field D C) : source D C f d E ≅ (target D C f S E)
  targetRealization (E : Field D C) :
    target D C f S E ⋙ (finiteTorConstructibleIntegral C.l E.val X).ι ≅
      (finiteTorConstructibleIntegral C.l E.val Y).ι ⋙
        integralExceptionalInverseImage C.l E.val D C.different f
  targetRealizationReductions : TargetRealizationReductions D C f d S targetRealization
  finiteReductions : FiniteReductions D C f d S gamma targetRealization
  a (E F : Field D C) (h : E ≤ F) :
    source D C f d E ⋙ scalar D C scalarClosed E F h true ≅
      scalar D C scalarClosed E F h false ⋙ source D C f d F
  aCanonical (E F : Field D C) (h : E ≤ F) (K : Cat D C E Y) :
    ((a E F h).hom.app K).hom =
      (sourceScalarComponent D C f d scalarClosed E F h K).hom
  c (E F : Field D C) (h : E ≤ F) :
    (operation D C f S E).F ⋙ scalar D C scalarClosed E F h false ≅
      scalar D C scalarClosed E F h true ⋙ (operation D C f S F).F
  cCanonical (E F : Field D C) (h : E ≤ F) (K : Cat D C E X) :
    (c E F h).hom.app K =
      (scalarBridge D C f S scalarClosed E F h false ((operation D C f S E).F.obj K)).hom ≫
        (compactComparison D C f S E F h).hom.app K ≫
        (operation D C f S F).F.map
          (scalarBridge D C f S scalarClosed E F h true K).inv
  b (E F : Field D C) (h : E ≤ F) :
    (target D C f S E) ⋙ scalar D C scalarClosed E F h true ≅
      scalar D C scalarClosed E F h false ⋙ (target D C f S F)
  bMate : CoefficientMate D C f S scalarClosed c b


/-- The simultaneous family with all operation, reduction and coefficient equations.
The inherited records store exactly the original fields in three bounded groups.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
structure Data extends ComparisonData D C f d S where
  coherence : Coherence D C f d S scalarClosed gamma a b


end WeilConjectures.AdicPurityScalarNaturality
