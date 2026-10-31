/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.WfTensorUnitSquare.WfTensorUnitSquareData
import WeilConjectures.SixFunctors.WfTensorUnitSquare.WfCompletedConstantPullbackNormalization
import WeilConjectures.SixFunctors.WfTensorUnitSquare.WfNormalizedKoszulFiberUnitTransport
import all WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct

/-! # Frobenius tensor comparison and the actual completion unit

The derived unit square follows from the specified completion comparison.
The strict square combines normalized constants and augmented Koszul transport;
applying localization gives the equality on the recorded models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.WfTensorUnitSquare
variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A) (e : Aut X)

variable (p : A)

private theorem derivedSquare (hp : Ideal.span (Set.range (fun _ : Fin 1 ↦ p)) = d.ideal)
    (M N : PbcBoundedConstructibleComplete X d) :
    DerivedSquare X d e p hp M N := by
  unfold DerivedSquare completed
  rw [Iso.trans_hom, ← Category.assoc]
  have h := (wfPullbackCompletion_exists X d 1 (fun _ ↦ p) hp e
    ((wfOrdinaryDerivedTensor X d).obj (M.obj, N.obj))).exists.choose_spec
  change _ ≫ (wfPullbackCompletion X d 1 (fun _ ↦ p) hp e _).hom = _ at h
  rw [h]
  exact (wfCompletion_unit_map X d 1 (fun _ ↦ p) hp (ordinary X d e M N).hom)


private theorem strictSquare (M N : PbcBoundedConstructibleComplete X d) :
    StrictSquare X d e p M N := by
  obtain ⟨k, hk, huniq⟩ := completedConstantPullback_normalized X d e
  refine ⟨k, ⟨hk, ?_⟩, ?_⟩
  · intro U V _ _ _ _
    obtain ⟨delta, b, hn, hunit⟩ :=
      normalizedKoszulFiber_unit_transport X d e p k hk U V
    refine ⟨delta, b, hn, hunit, ?_⟩
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, hunit]
  · intro l hl
    exact huniq l hl.1

end WeilConjectures.WfTensorUnitSquare

namespace WeilConjectures

/-- The specified Frobenius comparisons preserve the actual completion unit, strictly
on the flat K-flat models and in their derived localization.
Source: blueprint, sec-six-functors/sk-rem-sf-pf-done,
fix-prop-projection-formula.proof.md, penultimate sentence; original step 3 of
lem-wf-tensor-completion-frobenius
(blueprint: lem-wf-tensor-pullback-completion-unit-square).

Proof: (1) inverse image for Frobenius is exact and preserves countable products by
lem-weil-proetale-isomorphism-inverse-image. The specified coefficient map is induced
by the finite constant-quotient maps. The ringed-topoi tensor-pullback theorem preserves
flat K-flat representatives; its total comparison is alpha.
(2) The coefficient map preserves one and the uniformizer. Thus HQ_m to Q_m preserves
the degree-zero inclusion and the transitions (uniformizer in degree minus one and
identity in degree zero). The balanced tensor formula gives beta_m H(1 tensor iota_m)
= (1 tensor iota_m) alpha on tensor generators and on each totalization summand.
(3) The product projections then give delta H(u) = u' alpha. Their transition equations
make delta commute with one minus shift. Use delta on both fiber coordinates; it
commutes with the signed differential. The actual unit is (u,0), so its image is
(delta H(u),0) = (u' alpha,0), an equality of chain maps, without a homotopy.
(4) Localization preserves this equality and composition. The finite-quotient coefficient
presentation comparison preserves the same towers, products, fiber and unit. The
representative characterization of a and uniqueness of the unit-normalized completion
comparison identify the localized maps with the specified a and b. -/
theorem wfTensorPullbackCompletionUnitSquare
    (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (X₀ : Over (Spec (.of D.k₀))) [IsSeparated X₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (M N : PbcBoundedConstructibleComplete (D.geometricFiber X₀).left
      (pbcStageDatum.{u} c.l c.Qbar E)) :
    WfTensorUnitSquare.DerivedSquare (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) (D.geometricFrobenius X₀)
        (pbcStageUniformizer.{u} c.l c.Qbar E) (wfUniformizer_generates D c E) M N ∧
      WfTensorUnitSquare.StrictSquare (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) (D.geometricFrobenius X₀)
        (pbcStageUniformizer.{u} c.l c.Qbar E) M N := by
  exact ⟨WfTensorUnitSquare.derivedSquare _ _ _ _ _ M N,
    WfTensorUnitSquare.strictSquare _ _ _ _ M N⟩

end WeilConjectures
