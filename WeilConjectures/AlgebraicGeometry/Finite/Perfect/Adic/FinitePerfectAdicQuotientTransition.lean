/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicMarkedOrigin

/-! # The ordinary quotient arrows in fixed-scalar chart coordinates

Source: Stacks Project, Tags 03CY and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Ordinary fixed-scalar coordinates of the finite quotient on the chart: ordinary scalar
extension to the finite quotient ring, followed by the fixed coefficient encoding and
restriction to the chart. Its termwise application to a K-flat complex computes
`finitePerfectAdicQuotientCoordinates`.
Source: Stacks Tags 03CY, 099R and 06YY. -/
def finitePerfectAdicQuotientStrictCoordinates
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (V : X.Etale) (n : ℕ) :
    CompletedAdicModules X d ⥤ Sheaf (ProEt.topology V.left)
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) :=
  completedAdicChange X (completedAdicCommProjection X d n) ⋙
    finiteCoefficientSliceRestriction X (A ⧸ d.ideal ^ (n + 1))
      (completedAdicFiniteCommRing X d n) (φ n) V

instance finitePerfectAdicQuotientStrictCoordinates_additive
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (V : X.Etale) (n : ℕ) :
    (finitePerfectAdicQuotientStrictCoordinates X d φ V n).Additive :=
  inferInstanceAs (completedAdicChange X (completedAdicCommProjection X d n) ⋙
    finiteCoefficientSliceRestriction X (A ⧸ d.ideal ^ (n + 1))
      (completedAdicFiniteCommRing X d n) (φ n) V).Additive

/-- Restriction of scalars along the consecutive finite quotient map, on chart sheaves. -/
abbrev finitePerfectAdicStepRestrict (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (V : X.Etale) (n : ℕ) :
    Sheaf (ProEt.topology V.left) (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) ⥤
      Sheaf (ProEt.topology V.left)
        (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)))) :=
  sheafCompose (ProEt.topology V.left) (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1}
    (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1))))



/-- A consecutive arrow of fixed-scalar coordinates is the ordinary quotient arrow: on every
chart object it sends the sheafified pure tensor `b ⊗ x` to `q(b) ⊗ x`. Since sheafified pure
tensors generate, this determines the arrow uniquely.
Source: Stacks Project, Tag 09C6. -/
def FinitePerfectAdicQuotientTransition
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (V : X.Etale) (n : ℕ)
    (δ : finitePerfectAdicQuotientStrictCoordinates X d φ V (n + 1) ⟶
      finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
        finitePerfectAdicStepRestrict X d V n) : Prop :=
  ∀ (N : CompletedAdicModules X d) (U : V.left.ProEt)
    (b : (completedAdicFiniteCommRing X d (n + 1)).obj.obj
      (op (finitePerfectAdicChartObject V U)))
    (x : N.val.obj (op (finitePerfectAdicChartObject V U))),
    (δ.app N).hom.app (op U)
        (completedAdicChangeTensor X (completedAdicCommProjection X d (n + 1)) N
          (op (finitePerfectAdicChartObject V U)) b x) =
      completedAdicChangeTensor X (completedAdicCommProjection X d n) N
        (op (finitePerfectAdicChartObject V U))
        ((completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)).hom.app
          (op (finitePerfectAdicChartObject V U)) b) x

/-- The ordinary quotient arrows exist between the fixed-scalar coordinates. This uses the
compatibility of the finite comparisons `φ` with the quotient maps.
Source: Stacks Project, Tags 03CY and 09C6.

Proof sketch: the unit of ordinary scalar extension along the finite projection, composed with
the identification of restriction along the composite projection, transposes to an arrow of
ordinary scalar extensions; since `φ` intertwines the constant and the actual quotient maps,
its fixed-scalar encoding is semilinear over the constant quotient map. -/
theorem finitePerfectAdic_quotient_transition_exists
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hcompat : FinitePerfectModelsCompatible X d φ) (V : X.Etale) (n : ℕ) :
    ∃ δ : finitePerfectAdicQuotientStrictCoordinates X d φ V (n + 1) ⟶
        finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
          finitePerfectAdicStepRestrict X d V n,
      FinitePerfectAdicQuotientTransition X d φ V n δ := by
  sorry

end AlgebraicGeometry.Scheme
