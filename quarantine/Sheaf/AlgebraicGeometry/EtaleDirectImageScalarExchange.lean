/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.Paper.ProperOpenCoefficientRefinement

/-!
# Scalar extension respects ordinary etale direct-image exchange

Source: Stacks Project, sites-cohomology.tex, Tag 0E47,
`remark-compose-base-change-horizontal`, with Tag 07A7, `remark-base-change`
(blueprint: lem-pur-etale-direct-image-scalar-exchange).

The scalar functor is `scalarExtension`; the K-flat-normalized pullback comparison
is `properOpenCoefficientPullbackIso`, the canonical exactness transport of
`scalarPullbackIso`. The map chi is the existing `scalarMate`: transporting its
canonical geometric adjunction along the same exactness isomorphism identifies its
adjunct with scalar extension of the counit after this pullback comparison.
The exchange is the specified `exactDerivedBaseChangeMap`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Scalar extension commutes with the specified ordinary unbounded etale exchange,
naturally in the input complex.

Source: Stacks Project, sites-cohomology.tex, Tag 0E47,
`remark-compose-base-change-horizontal`, with Tag 07A7, `remark-base-change`
(blueprint: lem-pur-etale-direct-image-scalar-exchange).

Proof:
1. Apply lem-sfb-kflat-scalar-comparison-normalization using the constant-ring
   identifications of prop-weil-pbc-inverse-image-modules-exact. Its composition
   formula, inverted, identifies the two scalar/pullback paths around the square.
   Switching B tensor P to P tensor B introduces no sign since B has degree zero.
   Apply the formula to h followed by f and to f' followed by g; square
   commutativity gives the coefficient/pullback cube with the specified square
   compositors of def-kun-unbounded-exchange.
2. The definition of scalarMate and def-weil-pbc-adjunction-mate say that its
   transpose is lambda followed by scalar extension of the A-counit. The
   definition of exactDerivedBaseChangeMap similarly says that its transpose is
   the square comparison followed by pullback of the geometric counit. The
   canonical derived adjunctions are those of def-kun-projection-formula-map,
   transported to exact termwise inverse image.
3. Transpose the left-hand composite under the f'-adjunction with B coefficients.
   Counit naturality, the exchange transpose formula, square naturality, and the
   scalar-mate transpose formula rewrite it as Q(h_A^*(epsilon_f)) after the
   h/f path of the coefficient/pullback cube. Naturality of lambda_h is the last
   rewrite; no invertibility of a direct-image comparison is used.
4. Transpose the right-hand composite under the same adjunction. Use the scalar
   transpose formula for f', naturality of lambda_f', functoriality of Q, and the
   exchange transpose formula with A coefficients. The result is the same
   Q(h_A^*(epsilon_f)) after the f'/g path of that cube.
5. Postcompose the cube identity from Step 1 with Q(h_A^*(epsilon_f)). The two
   transposes agree, so injectivity of the canonical adjunction Hom bijection
   gives the claimed equality. Every map used is natural; whiskering and
   composition therefore make the equality natural in M on the entire unbounded
   derived category, without properness, flatness or boundedness assumptions. -/
theorem exactDerivedBaseChangeMap_scalarExtension
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X' X Y' Y : Scheme.{u}}
    (h : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : ChosenCartesianSquare h f' f g) (M : DerivedCategoryModule A X) :
    D(upperStar (ModuleCat.{u + 1} B) g).map ((scalarMate φ f).app M) ≫
        (exactDerivedBaseChangeMap (ModuleCat.{u + 1} B) sq.toCommSq).app
          ((scalarExtension φ X).obj M) ≫
        R(lowerStar (ModuleCat.{u + 1} B) f').map
          ((properOpenCoefficientPullbackIso φ h).hom.app M) =
      (properOpenCoefficientPullbackIso φ g).hom.app
          (R(lowerStar (ModuleCat.{u + 1} A) f).obj M) ≫
        (scalarExtension φ Y').map
          ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app M) ≫
        (scalarMate φ f').app (D(upperStar (ModuleCat.{u + 1} A) h).obj M) := by
  sorry

end AlgebraicGeometry.Etale
