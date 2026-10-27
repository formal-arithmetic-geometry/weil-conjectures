/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.AlgebraicGeometry.LineAlgebraicEquivalence
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

import Sheaf.AlgebraicGeometry.SemiabelianGeometricPowerIntegrality
import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry

/-! # Multiplicative frame torsors of geometric Picard-zero lines

Source: Milne, Abelian Varieties, I Proposition 8.4 and Section 9, Proposition 9.2,
printed pp.35--36 and 41; the semiabelian extension is the agent-formulated argument
recorded in the DAG, using Milne, Algebraic Groups, Proposition 12.48 and Remark 12.50.
(blueprint: lem-sfb-semiabelian-picard-multiplicative-torsor)

The frame scheme is specified by the existing universal-frame model. Its existence,
its commutative group law, the prescribed identity frame, and the scalar action are
conclusions. All module inverse images are tensor inverse images.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

open Scheme.Modules SplitTorusFrames

/-- A geometrically algebraically trivial line on a semiabelian group has a
multiplicative frame torsor over the original field, with any specified identity frame.
The map `c` identifies the total group scheme over H with the representing frame scheme.
The point `s` lies over the identity of H and is both the identity of E and the given
frame `u`. The scalar equation holds on every H-scheme, including nonreduced tests;
the Laurent coordinate specifies the given scalar action, rather than an arbitrary one.

Source: Milne, Abelian Varieties, I Proposition 8.4 and Section 9, Proposition 9.2,
printed pp.35--36 and 41; semiabelian generalization recorded in the DAG, using Milne,
Algebraic Groups, Proposition 12.48 and Remark 12.50, pp.246--247.
(blueprint: lem-sfb-semiabelian-picard-multiplicative-torsor)

Proof:
1. Apply lem-sfb-semiabelian-geometric-power-integrality to the geometric exact
   sequence. The geometric powers of H are nonempty integral separated finite-type
   schemes, as needed for product-unit factorization. Properness of H is not used.
2. By lem-trf-projective-bundle-quotient-geometry, take the open in P(O plus T dual)
   where both summand quotients are isomorphisms. Normalize by the first summand.
   The second is then a frame of T. This gives the universal FrameModel and its
   local charts V times G_m, naturally on all test schemes.
3. Apply lem-sfb-semiabelian-picard-square-triviality to obtain
   phi_0 : p1*T tensor p2*T isomorphic to m*T over k. Its two axis restrictions,
   measured using u, are units a(x), b(y), with c=a(e)=b(e). Replace phi_0 by
   c/(p1*a p2*b) times phi_0. The resulting phi fixes both axes. The product of
   frames v,w is phi(v tensor w), a scheme morphism, bilinear in scalar units.
4. The associativity defect is a regular unit q on H cubed, with
   q(x,y,e)=q(e,e,z)=1. Over the algebraic closure apply
   lem-sfb-rosenlicht-product-unit-factorization to H squared times H, based at
   (e,e),e: q(x,y,z)=q(x,y,e)q(e,e,z)/q(e,e,e)=1. Equality descends to k by
   injectivity of R to R tensor kbar on each affine trivializing chart.
5. The commutativity defect d on H squared has d(x,e)=d(e,y)=1. The same
   product-unit factorization and coefficient injection give d=1. This does not
   assert that every unit on a semiabelian group is constant.
6. Pull phi back along x to (x,-x). With u it gives a perfect rank-one pairing
   T_x tensor T_{-x} isomorphic to k. Define the inverse of v by pairing to 1.
   In local bases its coordinate is (f(x)t) inverse, hence regular; uniqueness
   glues these maps. The group diagrams are those of def-sc-group-scheme.
7. Projection preserves multiplication. Its identity fibre consists of the
   frames of e*T and u identifies it with G_m by a to au. Bilinearity gives
   (au)*v=av and (au)*(bu)=ab u, proving the scalar equation and homomorphism
   property of the embedding. Frames exist Zariski locally; by
   lem-pc-zariski-coverings-are-fppf these give fppf-local lifts. The kernel square
   and local surjectivity prove exactness as fppf sheaves.
-/
theorem semiabelian_picard_multiplicative_torsor
    {k : Type u} [Field k]
    (H : Grp (Over (Spec (.of k)))) [IsCommMonObj H.X]
    [Smooth H.X.hom] [IsClosedImmersion (pullback.diagonal H.X.hom)]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    (r : ℕ) (A : Grp (Over (Spec (.of (AlgebraicClosure k)))))
    [IsCommMonObj A.X] [IsProper A.X.hom] [Smooth A.X.hom]
    [GeometricallyConnected A.X.hom]
    (i : MultiplicativeType.splitTorus (AlgebraicClosure k) r ⟶
      (MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj H)
    (q : (MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj H ⟶ A)
    (hkernel : IsPullback i.hom.hom
      (toUnit (MultiplicativeType.splitTorus (AlgebraicClosure k) r).X)
      q.hom.hom η[A.X])
    (hlocallySurjective : Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (Spec (.of (AlgebraicClosure k))))
      (yoneda.map q.hom.hom))
    (T : H.X.left.Modules) [T.IsInvertible]
    (halgebraicallyTrivial : AreAlgebraicallyEquivalent
      ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj H).X
      ((tensorPullback (pullback.fst H.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))).obj T)
      (unit ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj H).X.left))
    (u : unit (𝟙_ (Over (Spec (.of k)))).left ≅
      (tensorPullback η[H.X].left).obj T) :
    ∃ (E : Grp (Over (Spec (.of k)))) (p : E.X ⟶ H.X)
      (j : StandardGroupSchemes.multiplicative k ⟶ E.X)
      (F : FrameModel T) (c : Over.mk p.left ≅ F.space)
      (s : Over.mk η[H.X].left ⟶ Over.mk p.left),
      IsCommMonObj E.X ∧ IsMonHom p ∧ IsMonHom j ∧
      s.left = η[E.X].left ∧ F.at (s ≫ c.hom) = u ∧
      IsPullback j (toUnit (StandardGroupSchemes.multiplicative k)) p η[H.X] ∧
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of k)))
        (yoneda.map p) ∧
      (∀ (U : Over H.X.left) (x y : (Over.map H.X.hom).obj U ⟶ E.X)
        (hx : x.left ≫ p.left = U.hom) (hy : y.left ≫ p.left = U.hom)
        (z : (Over.map H.X.hom).obj U ⟶ StandardGroupSchemes.multiplicative k),
        y = x * (z ≫ j) →
        (F.at (Over.homMk y.left hy ≫ c.hom)).hom =
          (F.at (Over.homMk x.left hx ≫ c.hom)).hom ≫
            ((tensorPullback U.hom).obj T).smulHom
              (z.left.appTop ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv
                (LaurentPolynomial.T 1)))) := by
  sorry

end AlgebraicGeometry
