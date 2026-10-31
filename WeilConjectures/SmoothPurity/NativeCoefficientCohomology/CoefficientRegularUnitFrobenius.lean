/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientEndpointObjects
public import WeilConjectures.SmoothPurity.Pullback.PullbackTensorCommonStageUnitCoherence
import WeilConjectures.SmoothPurity.Automorphism.AutomorphismConstructibleStageEquivalence
import all WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackTower
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitCanonicalWeil
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitCommonTensorUnitor

/-! # The regular coefficient as the Frobenius-compatible tensor unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
open WeilConjectures.ConstantPurityFrobenius
namespace WeilConjectures.NativeCoefficientCohomology

/-- The canonical invertibility witness on the geometric fibre.
Source: finite-field coefficient convention
(blueprint: lem-sf-coefficient-regular-unit-frobenius). -/
local instance coefficientRegularUnitResidueUnits (P : PurityFiniteSetting.{u})
    (X₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    ∀ x : (P.field.geometricFiber X₀).left,
      Invertible (P.coefficients.l : (P.field.geometricFiber X₀).left.residueField x) :=
  fun x ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different X₀ x

/-- The regular coefficient Weil object identifies with the coherent tensor unit,
compatibly with the uniquely coherent tensor-unit Frobenius comparison.

Source: the normalized unit comparison in the constant-purity source convention;
Stacks Project, Tags 07A4 and 0941; Bhatt--Scholze, Sections 3.5 and 6.5.
(blueprint: lem-sf-coefficient-regular-unit-frobenius)

Proof: the coefficient prime is a unit on the geometric fibre, so the completed
unit pullback data `Core` exists for geometric Frobenius at the least finite
coefficient field. The completed-unit common tensor comparison gives an
isomorphism from the regular coefficient unit to the reconstructed tensor unit
intertwining the selected coherent unit map with `commonCoreTheta`. The unit of
every `Core` is the actual constant Weil map (completedUnitCanonicalWeil), so
`commonCoreTheta` is the published constant Weil structure. No primitive root,
Tate degree, or shift is involved; the empty scheme is covered by the same formulas. -/
theorem coefficient_regular_unit_frobenius
    (P : PurityFiniteSetting.{u}) (X₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    let U := constantWeilAlgebraicallyClosedComplex P.coefficients.l P.field
      P.coefficients.different X₀ P.coefficients.Qbar
    let I := pullbackTensorCommonUnit P.coefficients.l P.coefficients.Qbar
      (P.field.geometricFiber X₀).left
    let F := sourceFrobenius P.field P.coefficients.l
      P.coefficients.different P.coefficients.Qbar X₀
    let ε := (pullbackTensorCommonStageUnitCoherence P.coefficients.l P.coefficients.Qbar
      (P.field.geometricFrobenius X₀).hom).exists.choose
    ∃ b : U.carrier ≅ I, F.map b.hom ≫ ε.hom = U.str.hom ≫ b.hom := by
  let D := P.field
  let l := P.coefficients.l
  let hl := P.coefficients.different
  let Ω := P.coefficients.Qbar
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
    (Padic.finiteCoefficientBase l Ω)
  have hU := (automorphismConstructibleStage_units D l hl (D.geometricFiber X₀)).1
  obtain ⟨c⟩ := CompletedUnitPullback.core_exists l E D hl
    (D.geometricFrobenius X₀).hom hU hU
  obtain ⟨a, ha⟩ := CompletedUnitPullback.completedUnitCommonTensorComparison D l hl X₀ Ω c
  have hθ : CompletedUnitPullback.commonCoreTheta D l hl X₀ Ω c =
      (constantWeilAlgebraicallyClosedComplex l D hl X₀ Ω).str := by
    dsimp only [CompletedUnitPullback.commonCoreTheta]
    rw [CompletedUnitPullback.completedUnitCanonicalWeil]
    apply Iso.ext
    rfl
  rw [hθ] at ha
  exact ⟨a, ha⟩

end WeilConjectures.NativeCoefficientCohomology
