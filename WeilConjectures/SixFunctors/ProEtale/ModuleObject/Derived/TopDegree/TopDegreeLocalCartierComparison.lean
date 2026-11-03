/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopDegree.TopDegreeTraceDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopDegree.TopDegreePointProductSigns
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceCartierBoundaryExistence

/-! # The local positive Cartier comparison

Source: sk-cor-trace, steps 9--10.
(blueprint: lem-pd-local-positive-cartier-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing.TopDegree
open PurityTransport
variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)

/-- The local positive Cartier comparison.
Source: sk-cor-trace, steps 9--10 (blueprint: lem-pd-local-positive-cartier-comparison).

Proof in words.
Fix the supplied affine Cartesian point chart. The existing TraceAffine theorem is
indexed by FiniteFieldDatum and does not apply to a general algebraically closed
k: viewing X over an embedded algebraic closure of F_p does not preserve finite
type when k is transcendental. Use GeneralPurityTransport.AffineNormalized over
the actual k and its composition/base-change/scalar clauses; do not replace k
by a finite-field algebraic closure. The Cartesian etale chart pulls back the
ordered coordinate regular sequence defining its zero fibre. For d=0, its zero-fibre
square identifies the neighbourhood with Spec k. On a distinguished finite coefficient
apply regular immersion purity to that ordered regular parameter list. The orientation of the
identity is the identity,
because its composition equation says gamma_id=gamma_id squared and it is invertible.
The finite regular fundamental class is (-1)^d times the orientation class. Each
finite Cartier divisor map is minus its supported Kummer parameter boundary; hence
the (-1)^d factors cancel and the orientation class is the positive Cartier product.
Closed-support base change produces alpha and fixes it by traceSupportedUnit. Apply
tensor/closed-support projection to the ordered coordinate divisors to get beta;
its quotient unit is traceProductUnit. Identify the supported orientation class
with pointMap by transposing the same proper point-return arrow under the same
normalized smooth adjunction. This proves the positive equation with the exact
LinePullCoordinates maps. Repeat these equations on the full integral Kummer boundary
retained in TraceCartierBoundary. The full pole extension and positive root tower
produce the integral supported morphism directly. Scalar extension and the normalized
counit/source comparisons carry this construction to every listed coefficient,
including arbitrary finite rings. Finite reductions check the normalization but
are not used to infer equality of arbitrary integral derived morphisms. The
negative product and empty tower are handled by the already proved sign lemma.
-/
theorem local_positive_cartier_comparison {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (C : TraceCartierFamily.{u} ell) (hC : TraceCartierBoundary ell C)
    (x : Spec (.of k) ⟶ X.left) [IsClosedImmersion x]
    (hx : x ≫ X.hom = 𝟙 _) (q : PointCoordinates X d x) [IsAffine q.U.left] :
    PositivePointProduct ell c hEll X d C x hx q := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing.TopDegree
