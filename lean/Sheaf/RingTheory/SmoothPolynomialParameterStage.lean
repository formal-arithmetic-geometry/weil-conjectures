/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.RegularClosedImmersionCodimension
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Regular parameter quotients in a smooth polynomial algebra

Source: Stacks Project, Algebra, Tags 00T4 and 00TA; Algebra, Tag 07NF;
Divisors, Tags 063D and 063G (blueprint: lem-per-smooth-polynomial-parameter-stage).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace IsLocalRing

/-- A smooth polynomial algebra with nonzero origin fibre has regular parameters.
Source: Stacks Project, Algebra, Tags 00T4 and 00TA; Algebra, Tag 07NF;
Divisors, Tags 063D and 063G (blueprint: lem-per-smooth-polynomial-parameter-stage).

Proof: Put P=k[X_i] and J=(f(X_i)). The variables are a regular sequence in P:
a quotient by any initial segment is the polynomial ring on the remaining variables,
and multiplication by the next variable shifts coefficients injectively. Smoothness
gives flatness of P→A (00TA). Tensor the injective multiplication maps on those
prefix quotients with A; the resulting maps are multiplication by f(X_i) on the
corresponding prefix quotients of A. This gives weak regularity. The last quotient
A/J is nonzero by hypothesis, so the sequence is regular. Base change of the smooth
map P→A along evaluation P→k identifies k⊗_P A with A/J, making A/J smooth over k
(00T4). Polynomial rings over fields and fields are regular Noetherian rings, so
smooth ascent (07NF) makes A and A/J regular Noetherian. The surjective quotient
map has kernel J. On the full affine chart its equations are precisely the displayed
regular sequence, of length d, giving the regular closed immersion of codimension d
(063D, 063G). With d=0 the sequence is empty and the quotient map is the identity;
nontriviality of A is exactly the hypothesis.
-/
theorem smooth_polynomial_parameter_stage
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (d : ℕ) (f : MvPolynomial (Fin d) k →ₐ[k] A)
    (hsmooth : Smooth (Spec.map (CommRingCat.ofHom f.toRingHom)))
    (hne : Nontrivial (A ⧸ Ideal.span (Set.range fun i : Fin d ↦ f (MvPolynomial.X i)))) :
    (Nontrivial A ∧ IsRegularRing A ∧ RingTheory.Sequence.IsRegular A
      (List.ofFn fun i : Fin d ↦ f (MvPolynomial.X i))) ∧
    (IsRegularRing (A ⧸ Ideal.span (Set.range fun i : Fin d ↦ f (MvPolynomial.X i))) ∧
      Smooth (Spec.map (CommRingCat.ofHom (algebraMap k
        (A ⧸ Ideal.span (Set.range fun i : Fin d ↦ f (MvPolynomial.X i)))))) ∧
      IsRegularClosedImmersionWithCodimension
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.span (Set.range fun i : Fin d ↦ f (MvPolynomial.X i)))))) (fun _ ↦ d)) := by sorry

end IsLocalRing
