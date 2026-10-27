/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.RationalMapExtensionValuationPoint
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Rational fixed points for split tori

Source: Milne, Algebraic Groups (2017), Theorem 16.51, printed p.343,
specialized to a finite product of multiplicative groups.
(blueprint: lem-sfb-split-torus-rational-fixed-point)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- A split torus acting on a proper finite-type scheme with a rational point has a
rational point fixed on every commutative algebra, including nonreduced test algebras.
The internal action `ModObj` supplies its action morphism and both morphism identities.
Properness includes local finite type and quasi-compactness, so finite type is retained.

Source: Milne, Algebraic Groups (2017), Theorem 16.51, printed p.343.
(blueprint: lem-sfb-split-torus-rational-fixed-point)

Proof, following the six steps of the node:
1. Transport the action along the splitting isomorphism. Write H_i for the first i
   coordinate factors and C_{i+1} for the next factor. Starting with a rational point,
   inductively construct a rational point whose H_i-orbit morphism is constant.
   The group and action identities (def-sc-group-scheme) give commutation of these actions.
2. For the C_{i+1}-orbit map G_m → X, use A¹ = Spec k[t] and U = D(t).
   The polynomial-domain lemma (lem-weil-pbc-polynomial-ring-domain) makes A¹ integral.
   It is Noetherian by lem-weil-pbc-finite-type-over-noetherian. Its complement of U
   is the rational origin. Its stalk k[t]_(t) is a valuation ring: every nonzero
   rational function is t^n p/q with p(0)q(0) nonzero, and it belongs to the stalk
   exactly when n is nonnegative.
3. By lem-sfb-rational-map-extension-valuation-point and properness, extend the orbit
   map to a neighbourhood of U and the origin, hence all of A¹. Evaluate at the origin
   to obtain a rational point z.
4. Compare a(u,F(t)) and F(ut) on G_m × A¹. They agree on D(t) by the action law.
   Its coordinate ring k[u,u⁻¹,t] is a domain by the polynomial-domain lemma and
   localization, so the source is reduced and D(t) dense. Properness implies relative
   separatedness (def-weil-proper-morphism). Thus lem-sfb-relative-separated-dominant-ext
   makes the maps equal. Restricting to t = 0 gives C_{i+1}-fixedness of z as morphisms.
5. Likewise compare a(h,F(t)) and F(t) on H_i × A¹. Commutation and H_i-fixedness of
   the previous point give equality on D(t). Its Laurent polynomial coordinate ring
   is a domain by the same argument. Apply lem-sfb-relative-separated-dominant-ext
   and restrict to t = 0 to retain H_i-fixedness, including i = 0.
6. Multiplication identifies H_i × C_{i+1} with H_{i+1}; the action law gives fixedness
   under their product. After r steps transport back to T. For r = 0 keep the initial
   rational point. The constant orbit morphism evaluated on any k-algebra A gives the
   displayed equality, with scalar extension expressed by precomposition with toUnit. -/
theorem exists_rational_fixedPoint_of_splitTorus {k : Type u} [Field k]
    (T : Grp (Over (Spec (.of k)))) (r : ℕ)
    (hsplit : Nonempty (T ≅ MultiplicativeType.splitTorus k r))
    (X : Over (Spec (.of k))) [ModObj T.X X] [IsProper X.hom]
    (hx : Nonempty (𝟙_ (Over (Spec (.of k))) ⟶ X)) :
    ∃ x : 𝟙_ (Over (Spec (.of k))) ⟶ X,
      ∀ (A : Type u) [CommRing A] [Algebra k A]
        (t : StandardGroupSchemes.affine k A ⟶ T.X),
        t • (toUnit (StandardGroupSchemes.affine k A) ≫ x) =
          toUnit (StandardGroupSchemes.affine k A) ≫ x := by
  sorry

end AlgebraicGeometry
