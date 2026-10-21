/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.Paper.CurveWeilMiddleExtension
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.ConstructiblePullbackTExact
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Ordinary direct image in the intrinsic common-stage heart

Source: blueprint def-wf-middle-extension, ordinary direct-image paragraph
(blueprint: def-wf-middle-extension).

The earlier pair-category realization and upstream Weil-sheaf realization remain imported.
Here j_* is the right adjoint of the actual inverse image on constructible sheaves. This
universal property determines the ordinary direct image up to unique adjunction-compatible
isomorphism; no derived direct image, arbitrary map or extra coefficient objects enter.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (c : AlgebraicGeometry.Scheme.MiddleExtensionCurve D)

/-- Actual base change of j₀ along the fixed algebraic-closure inclusion.
Source: blueprint geometric-fibre convention (blueprint: def-wf-middle-extension). -/
def qbarCurveGeometricOpen :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map c.j).left

/-- The recorded geometric inverse image, retaining each literal finite coefficient stage.
Source: blueprint ordinary-direct-image convention (blueprint: def-wf-middle-extension). -/
def qbarCurveDerivedRestriction :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _ (qbarCurveGeometricOpen D c)
    (sfWeilPrimeInvertible D l hl c.U) (sfWeilPrimeInvertible D l hl c.C)

/-- Inverse image preserves the standard constructible heart.
Source: BS 6.8.11(3), 6.8.15; blueprint def-wf-middle-extension
(blueprint: def-wf-middle-extension).
Proof: at every finite torsion level open inverse image is exact. The completed
pullback has exactly these reductions, and good truncations commute with it.
Rationalization and finite scalar extension preserve the two degree-zero bounds.
The common-stage inclusion therefore preserves both heart conditions. -/
theorem qbarCurveRestriction_mem
    (F : sfCommonStageHeart l (D.geometricFiber c.C).left Ω) :
    sfCommonStageHeartProperty l (D.geometricFiber c.U).left Ω
      ((qbarCurveDerivedRestriction D l hl Ω c).obj F.obj) := by
  sorry

/-- Ordinary sheaf inverse image is the restriction of the actual geometric pullback.
Source: blueprint ordinary-direct-image convention (blueprint: def-wf-middle-extension). -/
def qbarCurveSheafRestriction :
    sfCommonStageHeart l (D.geometricFiber c.C).left Ω ⥤
      sfCommonStageHeart l (D.geometricFiber c.U).left Ω :=
  (sfCommonStageHeartProperty l (D.geometricFiber c.U).left Ω).lift
    ((sfCommonStageHeartProperty l (D.geometricFiber c.C).left Ω).ι ⋙
      qbarCurveDerivedRestriction D l hl Ω c) (qbarCurveRestriction_mem D l hl Ω c)

/-- The sheaf inverse image admits its ordinary constructible direct-image right adjoint.
Source: blueprint def-wf-middle-extension and Weil II (1.1.1)
(blueprint: def-wf-middle-extension).
Proof: ordinary direct image is sectionwise evaluation on V times_C U, with the
induced coefficient action. It is right adjoint to sheaf inverse image. On a
noetherian curve, a constructible adic sheaf has constructible ordinary direct
image under an open immersion: on each of the finitely many missing closed points
its stalk is the inertia invariants of a finite-dimensional generic stalk. Finite
coefficient extension commutes with those invariants. Thus the ordinary adjunction
restricts at rational stages and descends to the common-stage heart. This proves
existence of the right adjoint and identifies it with the prescribed ordinary j_*. -/
theorem qbarCurveSheafRestriction_isLeftAdjoint :
    (qbarCurveSheafRestriction D l hl Ω c).IsLeftAdjoint := by
  sorry

/-- Ordinary j_* in the actual intrinsic coefficient category. The adjunction
uniquely determines its data up to the equality of objects used downstream, namely
canonical isomorphism compatible with unit and counit.
Source: blueprint ordinary-direct-image paragraph (blueprint: def-wf-middle-extension). -/
def qbarCurveOrdinaryPushforward :
    sfCommonStageHeart l (D.geometricFiber c.U).left Ω ⥤
      sfCommonStageHeart l (D.geometricFiber c.C).left Ω :=
  @Functor.rightAdjoint _ _ _ _ (qbarCurveSheafRestriction D l hl Ω c)
    (qbarCurveSheafRestriction_isLeftAdjoint D l hl Ω c)

/-- The ordinary sheaf adjunction fixes the restriction counit, hence its identity
normalization on the open. Source: blueprint def-wf-middle-extension
(blueprint: def-wf-middle-extension). -/
def qbarCurveOrdinaryAdjunction :
    qbarCurveSheafRestriction D l hl Ω c ⊣ qbarCurveOrdinaryPushforward D l hl Ω c :=
  @Adjunction.ofIsLeftAdjoint _ _ _ _ (qbarCurveSheafRestriction D l hl Ω c)
    (qbarCurveSheafRestriction_isLeftAdjoint D l hl Ω c)

/-- First form ordinary direct image in degree zero, then shift cohomologically by one.
Source: blueprint final paragraph (blueprint: def-wf-middle-extension). -/
def qbarCurveShiftedOrdinaryImage :
    sfCommonStageHeart l (D.geometricFiber c.U).left Ω ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber c.C).left :=
  qbarCurveOrdinaryPushforward D l hl Ω c ⋙
    (sfCommonStageHeartProperty l (D.geometricFiber c.C).left Ω).ι ⋙ shiftFunctor _ (1 : ℤ)

end WeilConjectures
