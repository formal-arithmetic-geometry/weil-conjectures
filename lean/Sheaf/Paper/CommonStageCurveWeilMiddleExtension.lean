/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.QbarCurveOrdinaryImage
public import Sheaf.Paper.CommonStageFourierTransform

/-! # Ordinary middle extension of common-stage Weil sheaves

Source: main-20261015, def-wf-middle-extension, ordinary direct-image and shift paragraphs
(blueprint: def-wf-middle-extension).

The Weil direct image is determined by the ordinary sheaf adjunction. The shift is
implemented by tensoring with the explicit arithmetic constant coefficient line [1].
That line is the trivial-character Artin--Schreier projector, not a chosen Weil map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (c : Scheme.MiddleExtensionCurve D)

/-- Ordinary inverse image of Weil sheaves has ordinary direct image as right adjoint.
Source: Weil II (1.1.1), blueprint def-wf-middle-extension
(blueprint: def-wf-middle-extension).
Proof: ordinary j_* is sectionwise evaluation at V times_C U. Its Frobenius
comparison is the counit mate of zlFrobeniusSquare. The inverse Frobenius square
makes that mate invertible. The sheaf adjunction therefore restricts to equivariant
maps. On the finite boundary, stalks are inertia invariants, finite dimensional;
thus j_* preserves constructibility. Pass through rationalization and common stages.
No Frobenius-stable integral lattice is needed. -/
theorem qbarCurveWeilPull_isLeftAdjoint :
    (zlWeilPull D l hl Ω c.j).IsLeftAdjoint := by
  sorry

/-- Ordinary direct image on the recorded common-stage Weil heart, determined by
its adjunction to the actual inverse image, including its unit and counit.
Source: blueprint ordinary j_* convention (blueprint: def-wf-middle-extension). -/
def qbarCurveWeilOrdinaryPushforward :
    sfCommonStageWeilSheaf D l hl c.U Ω ⥤ sfCommonStageWeilSheaf D l hl c.C Ω :=
  @Functor.rightAdjoint _ _ _ _ (zlWeilPull D l hl Ω c.j)
    (qbarCurveWeilPull_isLeftAdjoint D l hl Ω c)

/-- Forget the Weil structure while retaining the actual geometric heart object.
Source: blueprint sheaf-theoretic convention (blueprint: def-wf-middle-extension). -/
def qbarCurveWeilHeartForget (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageHeart l (D.geometricFiber X₀).left Ω where
  obj M := ⟨M.obj.carrier, M.property⟩
  map f := ObjectProperty.homMk f.hom.hom.f

/-- The ordinary Weil direct image forgets to the recorded ordinary geometric j_*.
Source: blueprint sections formula (blueprint: def-wf-middle-extension).
Proof: the two functors are right adjoints to the same inverse-image operation
after forgetting Frobenius. The adjunction bijections identify the comparison,
whose section maps are identity maps on G(V times_C U). Frobenius is the mate of
the normalized pullback square, so this comparison respects the induced Weil map. -/
theorem qbarCurveWeilOrdinaryPushforward_forget :
    Nonempty (qbarCurveWeilOrdinaryPushforward D l hl Ω c ⋙
        qbarCurveWeilHeartForget D l hl Ω c.C ≅
      qbarCurveWeilHeartForget D l hl Ω c.U ⋙
        qbarCurveOrdinaryPushforward D l hl Ω c) := by
  sorry

variable (F : FourierSetting.{u})

/-- Arithmetic affine-line geometry, with its actual characteristic.
Source: blueprint affine-line application (blueprint: def-wf-middle-extension).
Proof: the line is Spec k0[x], a Noetherian integral scheme. Its global sections
are the polynomial k0-algebra and have characteristic p, as k0 has p^a elements. -/
theorem qbarAffineArithmeticGeometry :
    IsNoetherian (fourierAffineModel F PUnit.{u + 1}).left ∧
      CharP Γ((fourierAffineModel F PUnit.{u + 1}).left, ⊤) F.field.p := by
  sorry

/-- The explicit arithmetic constant line [1]. The trivial-character projector on
the Artin--Schreier cover of the zero function has invariant sections exactly the
constant coefficient sheaf. Complete, rationalize and then shift by one.
Source: blueprint ordinary-image shift convention (blueprint: def-wf-middle-extension). -/
def qbarAffineArithmeticShiftLine :
    generalAlgebraicallyClosedConstructibleCategory F.coefficients.l F.coefficients.Qbar
      (fourierAffineModel F PUnit.{u + 1}).left :=
  letI := (qbarAffineArithmeticGeometry F).1
  letI := (qbarAffineArithmeticGeometry F).2
  (shiftFunctor _ (1 : ℤ)).obj
    ⟨fourierCoefficientStage F,
      (sfRationalConstructibleLocalization F.coefficients.l (fourierCoefficient F)
        (fourierAffineModel F PUnit.{u + 1}).left).obj
        ⟨fourierAdicArtinSchreier F (fourierAffineModel F PUnit.{u + 1}).left 1 0,
          fourierAdicArtinSchreier_mem F (fourierAffineModel F PUnit.{u + 1}).left 1 0⟩⟩

/-- Canonical shift [1] of fixed Frobenius pairs on the affine line. The shift line
is defined over k0, hence has the normalized arithmetic-descent Weil map. Tensor
uses the recorded monoidal Frobenius comparison; no independent map is supplied.
Source: blueprint final paragraph (blueprint: def-wf-middle-extension). -/
def qbarAffineWeilShift :
    sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
        (fourierAffineModel F PUnit.{u + 1}) F.coefficients.Qbar ⥤
      sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
        (fourierAffineModel F PUnit.{u + 1}) F.coefficients.Qbar :=
  fourierWeilTensorFunctor F (fourierAffineModel F PUnit.{u + 1})
    (fourierModelWeil F (fourierAffineModel F PUnit.{u + 1})
      (qbarAffineArithmeticShiftLine F))

/-- The explicit shift-line tensor is naturally the actual cohomological shift.
Source: blueprint final paragraph (blueprint: def-wf-middle-extension).
Proof: the trivial-character projector averages over the finite torsor. Its invariant
sections descend uniquely to the base, identifying its completed image with the
constant coefficient module, with section 1 as unit. The map m tensor 1 to m
is its unit comparison. Apply the signed tensor/shift comparison and descend
through rationalization and common stages. Arithmetic descent gives the constant
line its usual Frobenius, and monoidal pullback preserves this unit comparison.
Thus the construction shifts the given Weil structure, without changing it. -/
theorem qbarAffineWeilShift_forget :
    Nonempty (qbarAffineWeilShift F ⋙
        sfCommonStageWeilForget F.field F.coefficients.l F.coefficients.different
          (fourierAffineModel F PUnit.{u + 1}) F.coefficients.Qbar ≅
      sfCommonStageWeilForget F.field F.coefficients.l F.coefficients.different
          (fourierAffineModel F PUnit.{u + 1}) F.coefficients.Qbar ⋙
        shiftFunctor _ (1 : ℤ)) := by
  sorry

end WeilConjectures
