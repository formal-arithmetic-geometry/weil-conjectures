/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M6
-/
module

public import Sheaf.Paper.ExceptionalIntegralAdjunctionLocalization

/-! # Localization of a supplied integral coefficient mate

Source: Zheng, Construction 6.2. Only one change of coefficient field is considered;
there is no geometric construction or common-field coherence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v w
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.ConstructibleExceptionalCoefficients
attribute [local instance] Operation.leftAdditive Operation.rightAdditive
  Operation.leftShift Operation.rightShift
attribute [local instance] Scalar.commShift Scalar.additive
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X Y : Scheme.{max u v}}

/-- The scalar shift maps are the localized supplied integral shift maps.
Source: Zheng, Construction 6.2, shift compatibility in coefficient localization
(blueprint: lem-sf-integral-scalar-mate-localization). -/
@[irreducible]
def scalarShiftLocalization
    (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (T : Scheme.{max u v})
    (S : Scalar.{u, v} l Ω (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i) T)
    (cs : (rationalScalar.{u, v} l Ω E L i T).CommShift ℤ) : Prop :=
  letI := cs
  letI := S.commShift
  ∀ (n : ℤ) (K : C.{u, v} l Ω T (.integral E)),
    HEq (((rationalScalar.{u, v} l Ω E L i T).commShiftIso n).hom.app
        ((rationalization.{u, v} l Ω E T).obj K))
      ((rationalization.{u, v} l Ω L T).map ((S.functor.commShiftIso n).hom.app K))

/-- Localize a single supplied counit square on the explicit raw tensor functors.
Source: Zheng, Construction 6.2, scalar-extension paragraph
(blueprint: lem-sf-integral-scalar-mate-localization).

Proof: use the two ambient functor equalities to identify the integral scalar maps
with the completed scalar maps on all underlying objects and arrows. The inclusions
are full, and membership proofs are irrelevant, so this also identifies their maps
on every integral Hom group. Extend q and b by tensoring their components with one.
The image of the first uniformizer is a unit times a positive power of the second;
hence its image in the second localized ring is invertible. The tensor balancing
relation therefore extends naturality of q and b from integral arrows to every
localized pure tensor. Tensor induction extends it to sums. The inverse component
formulas prove both transformations invertible. The two localization counit squares
identify the rational counits with the localized integral counits, so applying the
second localization functor to d.counit proves the rational counit equation. Use the
supplied canonical endpoint localization shifts. Extend the endpoint scalar shifts by
the same tensor construction. Applying localization
to d.qShift and d.bShift proves their shift equations. The component formula for q
is precisely its construction. The two endpoint scalar shifts are specified on every
integral representative by the localized shifts of SX and SY; thus they too are
determined, rather than chosen arbitrarily. Identity field extensions and zero categories obey
the same formulas without extra hypotheses. -/
theorem exists_integral_scalar_mate_localization
    (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (A : Operation.{u, v} l Ω X Y (.integral E))
    (B : Operation.{u, v} l Ω X Y (.integral L))
    [A.F.Additive] [A.G.Additive] [B.F.Additive] [B.G.Additive]
    [A.F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    [A.G.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    [B.F.Linear (Padic.coefficientExtensionIntegers l L.carrier)]
    [B.G.Linear (Padic.coefficientExtensionIntegers l L.carrier)]
    {hEX hEY hLX hLY}
    (R : RawLocalizedAdjunction l Ω E X Y A hEX hEY)
    (S : RawLocalizedAdjunction l Ω L X Y B hLX hLY)
    (qA : CounitFieldComparison.{u, v} l Ω A (R.operation l Ω E)
      (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y))
    (qB : CounitFieldComparison.{u, v} l Ω B (S.operation l Ω L)
      (rationalization.{u, v} l Ω L X) (rationalization.{u, v} l Ω L Y))
    (hqA : ∀ K, HEq (qA.q.hom.app K)
      (𝟙 ((rationalization.{u, v} l Ω E Y).obj (A.F.obj K))))
    (hbA : ∀ M, HEq (qA.b.hom.app M)
      (𝟙 ((rationalization.{u, v} l Ω E X).obj (A.G.obj M))))
    (hqB : ∀ K, HEq (qB.q.hom.app K)
      (𝟙 ((rationalization.{u, v} l Ω L Y).obj (B.F.obj K))))
    (hbB : ∀ M, HEq (qB.b.hom.app M)
      (𝟙 ((rationalization.{u, v} l Ω L X).obj (B.G.obj M))))
    (hsAX : qA.shiftX = integralRationalizationShift l Ω E X)
    (hsAY : qA.shiftY = integralRationalizationShift l Ω E Y)
    (hsBX : qB.shiftX = integralRationalizationShift l Ω L X)
    (hsBY : qB.shiftY = integralRationalizationShift l Ω L Y)
    (SX : Scalar.{u, v} l Ω (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i) X)
    (SY : Scalar.{u, v} l Ω (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i) Y)
    (hSX : SX.functor ⋙ RingStage.inclusion.{u, v} l Ω X (.integral L) =
      RingStage.inclusion.{u, v} l Ω X (.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i X)
    (hSY : SY.functor ⋙ RingStage.inclusion.{u, v} l Ω Y (.integral L) =
      RingStage.inclusion.{u, v} l Ω Y (.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i Y)
    (d : letI := SX.commShift
      letI := SY.commShift
      CounitComparison.{u, v} l Ω A B SX.functor SY.functor) :
    letI := SX.commShift
    letI := SY.commShift
    ∃ e : CounitFieldComparison.{u, v} l Ω (R.operation l Ω E) (S.operation l Ω L)
        (rationalScalar.{u, v} l Ω E L i X) (rationalScalar.{u, v} l Ω E L i Y),
      (∀ K : C.{u, v} l Ω X (.integral E),
        HEq (e.q.hom.app ((rationalization.{u, v} l Ω E X).obj K))
          ((rationalization.{u, v} l Ω L Y).map (d.q.hom.app K))) ∧
      scalarShiftLocalization l Ω E L i X SX e.shiftX ∧
      scalarShiftLocalization l Ω E L i Y SY e.shiftY := by sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
