/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FixedFinitePositiveCoefficientTwist
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass.Basic

/-! # Finite-coefficient Kummer classes

Source: literature/blueprint/slopmaster2-20261029-2300/blueprint/sec-smooth-purity/
sk-prop-an/pur9-def-kummer-class (blueprint: pur9-def-kummer-class).

The main definition realizes the finite-coefficient Kummer boundary using the canonical
derived Kummer morphism and the finite purity coefficient datum. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
/-- The coefficient ring of a finite purity setting has nonzero characteristic.
Source: blueprint sec-smooth-purity/sk-prop-an/pur9-def-kummer-class
(blueprint: pur9-def-kummer-class).
Proof: A is finite (`diagonalCoefficientFinite`), so its characteristic is nonzero by
Mathlib `CharP.ringChar_ne_zero_of_finite`. Alternatively, ell^n is zero in A by
`diagonalExponent_annihilates`, so the characteristic divides ell^n > 0. -/
theorem coefficientNeZero (P : PurityFiniteSetting.{u}) :
    NeZero (ringChar P.Coefficient) :=
  ⟨CharP.ringChar_ne_zero_of_finite P.Coefficient⟩
/-- The finite coefficient ring has an invertible exponent on every k-scheme.
Source: blueprint sec-smooth-purity/sk-prop-an/pur9-def-kummer-class
(blueprint: pur9-def-kummer-class).
Proof: take the admissible exponent ell^n = `diagonalExponent`. It is positive because
ell is prime, and it annihilates A by `diagonalExponent_annihilates`. It is a unit in
the global sections of W by `diagonalExponent_isUnit` applied to the structure morphism
aW, since ell differs from the characteristic of k; this includes the empty scheme. -/
theorem coefficientHasInvertibleExponent (P : PurityFiniteSetting.{u})
    (W : Scheme.{u}) (aW : W ⟶ Spec (.of P.field.k)) :
    HasInvertibleExponent P.Coefficient W := by
  refine ⟨P.diagonalExponent, ?_, P.diagonalExponent_annihilates, ?_⟩
  · exact pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level
  · exact P.diagonalExponent_isUnit aW

/-- Kummer class of a global unit with the finite coefficient datum. The class is the connecting
morphism of the Kummer sequence with coefficients inserted into the finite Tate twist.
Construction: the admissible exponent is N with ell^N = char A. The unit t is a map
Z_W -> G_m; pulling back the Kummer sequence 1 -> mu_N -> G_m -> G_m -> 1 along it and
extending scalars to A keeps it exact, since Z_W has projective stalks. Its connecting
morphism A_W -> (mu_N tensor A)[1] is the image of the abelian boundary of t under
zeta -> zeta tensor 1, read through the module/abelian comparison c^1_W; the target is
identified with A_W(1)[1]. A map A_W -> A_W(1)[1] in the derived category is a class in
H^1 R Gamma(W, A_W(1)).
Source: blueprint sec-smooth-purity/sk-prop-an/pur9-def-kummer-class
(blueprint: pur9-def-kummer-class). -/
noncomputable def kummerClass (P : PurityFiniteSetting.{u}) (W : Scheme.{u})
    (aW : W ⟶ Spec (.of P.field.k)) (t : Γ(W, ⊤)ˣ) :
    Etale.constantComplex P.Coefficient W ⟶
      (@Etale.tateTwistObject P.Coefficient (PurityFiniteSetting.coefficientCommRing P)
        (coefficientNeZero P) W 1)⟦(1 : ℤ)⟧ := by
  letI := coefficientNeZero P
  letI := coefficientHasInvertibleExponent P W aW
  exact Etale.kummerClassOf W P.Coefficient t

end WeilConjectures.PurityFiniteSetting
