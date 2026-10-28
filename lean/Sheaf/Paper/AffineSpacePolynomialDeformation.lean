/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.AffineLinearTraceAction
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-! # Polynomial deformation of an affine-space automorphism to a linear map

The family below involves only schemes and polynomial coordinates. It contains no
cohomology, trace, coefficient ring, or choice of orientation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Any polynomial automorphism is joined to its linear part by an affine-line family
of polynomial automorphisms. The endpoints and the projection are the actual tower maps.

Source: Furter--Poloni, "On the maximality of the triangular subgroup", Lemma 3.1,
proof, pp. 5--6 (translation followed by rescaling);
https://www.math.u-bordeaux.fr/~jpfurter/onTheMaximalityOfTheTriangularSubgroup.pdf .
For the same rescaling over arbitrary algebraically closed fields, see Blanc,
"Conjugacy classes of special automorphisms of the affine spaces", introduction,
pp. 939--940, https://msp.org/ant/2016/10-5/ant-v10-n5-p01-p.pdf .
The combined family and the characteristic-independent coordinate verification below
are written by agent M2 for the geometric presentation calculation in blueprint
sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: lem-pur-affine-space-polynomial-deformation).

Proof: in polynomial coordinates write F for e and b=F(0). Over k[t] set
H(t,x)=(F(tx)-b)/t+t*b. This is polynomial: every monomial of F-b has positive
x-degree, so its substituted monomial is divisible by t. Its inverse is
J(t,y)=F^{-1}(t*y+(1-t^2)*b)/t. The numerator vanishes at t=0 because F^{-1}(b)=0,
so J is polynomial as well. After inverting t the two substitution composites are
identity. The polynomial ring over the field injects into its localization at t;
therefore both composites are already identity over k[t]. At t=1, H is F. At t=0,
H is the degree-one part of F-b, i.e. its Jacobian at zero. Specializing J at zero
provides its inverse linear map (the derivative of F^{-1} at b). Their matrices
are inverse, giving g in GL_d(k). Transport these polynomial maps through the
coordinate-tower affine-space isomorphisms. The coordinate equations give both
endpoint squares and the equation over the parameter line. For d=0 the tower is
the base and use the identity family and the unique empty invertible matrix.
Algebraic closure is unnecessary; the argument works in every characteristic.
-/
theorem affineSpace_polynomial_deformation
    (k : Type u) [Field k] (d : ℕ)
    (e : affineTraceTower (Spec (.of k)) d ≅ affineTraceTower (Spec (.of k)) d)
    (he : e.hom ≫ affineTraceProjection (Spec (.of k)) d =
      affineTraceProjection (Spec (.of k)) d) :
    ∃ (g : Matrix.GeneralLinearGroup (Fin d) Γ(Spec (.of k), ⊤))
      (E : affineTraceTower (AffineSpace PUnit.{u + 1} (Spec (.of k))) d ≅
        affineTraceTower (AffineSpace PUnit.{u + 1} (Spec (.of k))) d),
      E.hom ≫ affineTraceProjection (AffineSpace PUnit.{u + 1} (Spec (.of k))) d =
        affineTraceProjection (AffineSpace PUnit.{u + 1} (Spec (.of k))) d ∧
      affineTraceMap (AffineSpace.zeroSection PUnit.{u + 1} (Spec (.of k))) d ≫ E.hom =
        affineTraceLinearMap (Spec (.of k)) d g ≫
          affineTraceMap (AffineSpace.zeroSection PUnit.{u + 1} (Spec (.of k))) d ∧
      affineTraceMap (AffineSpace.oneSection PUnit.{u + 1} (Spec (.of k))) d ≫ E.hom =
        e.hom ≫ affineTraceMap
          (AffineSpace.oneSection PUnit.{u + 1} (Spec (.of k))) d := by sorry

end AlgebraicGeometry
