/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.OperationCoefficientActionData
import WeilConjectures.SmoothPurity.Compact.CompactSupportScalarExtensionLaws

/-! # A component of the operation coefficient reduction argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe d t u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

/-- Coefficient actions, scalar towers, and adjunction mates for the completed direct images.
Source: blueprint lem-fix-operation-reduction, proof steps 8--10;
Stacks 07K0 and Bhatt--Scholze 6.7.2, 6.8.14.

Proof: ordinary finite-free coefficient extension commutes with direct image:
in a basis it is a finite sum of copies of the identity. Its comparison is
balanced and hence linear over the target coefficient ring; uniqueness of the
derived counit identifies it with the prescribed proper projection mate.
Restrict the actual completed direct image to the intrinsic constructible
subcategory. For compact support combine the proper-factor comparison with
extension by zero; finite-free scalar extension commutes with products and
cones in the defining completed tower. All integral comparison maps are fixed
by these constructions. For a three-field tower both mates are transposes of
the same restriction comparison. The restriction associators agree with the
balanced-tensor associators, so uniqueness of mates gives the integral cocycle
and unit equations, including repeated fields. Extend integral Hom maps
linearly to their coefficient localizations: on a pure tensor the map is the
coefficient times the integral image. The integral equations therefore descend
to the specified rational stages; their common-stage presentation gives the
stated algebraic-closure actions. The same transposition proves the unit and
counit equations of the exceptional-adjoint square. Threefold pasting gives
the direct-image scalar tower and the open/proper compact-support pasting.
For identity ring maps the normalized tensor multiplication is the unit, so
the proper mate and compact-support comparisons are identities.
(blueprint: lem-fix-basic-operation-coefficient-coherence). -/
theorem basicOperationCoefficientCoherence
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω]
    (X Y : Scheme.{u}) (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    coefficientOperationMateEquations ∧
    (∀ (K₀ : Type u) [Field K₀] (hl₀ : IsUnit (l : K₀))
      [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
      [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
      [QuasiCompact (X ↘ Spec (.of K₀))]
      [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
      [QuasiCompact (Y ↘ Spec (.of K₀))]
      [f.IsOver (Spec (.of K₀))] [IsSeparated f]
      [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f),
      ∃ S : SfCompactSupportCoefficientAction l K₀ hl₀ Ω c,
        operationIntegralCoefficientCoherent l Ω X Y
          (fun E₀ ↦ sfCompactSupportFiniteIntegralFunctor l K₀ hl₀ c
            (Coefficient.{u} l Ω E₀)) (fun h ↦ S.integralBeta h)) ∧
    (∀ (K₀ : Type u) [Field K₀] (hl₀ : IsUnit (l : K₀))
      [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
      [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
      [QuasiCompact (X ↘ Spec (.of K₀))]
      [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
      [QuasiCompact (Y ↘ Spec (.of K₀))]
      [f.IsOver (Spec (.of K₀))],
      OperationDirectImageCoefficientAction l Ω X Y f) ∧
    (directImageScalarExtensionLaws l) ∧
    (compactSupportScalarIsomorphisms l) ∧
    (compactSupportScalarExtensionLaws) ∧
    directImageScalarTowerLaws ∧
    coefficientOperationIdentityLaws := by sorry

end WeilConjectures
