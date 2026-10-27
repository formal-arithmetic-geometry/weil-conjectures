/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CondensedTateIntegralTowerData

/-! Core normalized tower construction.

Source: smooth-purity transport, construction of the normalized Tate-unit tower.
(blueprint: lem-pur-normalized-tate-tensor-reductions)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

/-- The actual quotient tower of the integral root tensor admits normalized derived
reductions. This is the reduction part, without a common bounded local model or any
constructibility assertion.

Source: smooth-purity transport, the proof of
`lem-pur-normalized-tate-tensor-tower`, Steps 1--3.
(blueprint: lem-pur-normalized-tate-tensor-reductions)

Proof: choose the common pro-etale covering with compatible primitive roots given by
Tate local freeness. In these bases the actual root-limit projections are coefficient
residues. Completion modulo ell^(n+1) therefore identifies the root line quotient
with the finite root sheaf. Iterate ordinary tensor balancing in the prescribed order;
at zero use the coefficient unit and its multiplication. The formula on an arbitrary
scalar times a local root generator is exactly ProjectionBalanced, so it glues.
A locally free line in one degree is K-flat: on the trivializing cover its tensor
with an acyclic complex is that complex, and exact restriction detects acyclicity.
Thus the ordinary quotient computations also compute all derived reductions.
Take the level objects to be these derived quotients of the shifted integral line.
Exact evaluation of the single strict tower gives their evaluation isomorphisms;
the quotient balancing isomorphisms give normalization. On a pure tensor both
successive reductions send ((x tensor c) tensor b) tensor a to
x tensor q(c) q(b) a, proving the transition and cocycle fields, even at equal indices.
Use the finite model isomorphisms to define e; the same single-complex evaluation
formula gives ProjectionNormalized. The root power map, followed by scalar quotient,
is an isomorphism in these bases. It supplies a CoefficientLineComparison for every
comparable pair. Every such comparison has the same map on generators by its
normalization fields. Tensor balancing and the scalar adjunction mates then identify
its proTwistMap with the tower normalization, proving all the asserted squares.
The empty scheme and the empty tensor are included by the same formulas.
-/
theorem normalizedTateTensorTower_core
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ) :
    ∃ (M : AdicTower T (datum.{u} ell))
      (e : ∀ n : ℕ, M.level n ≅ (derivedRealization T ell n).obj (finiteTwist T ell n d))
      (h : M.tower = strictDerivedTower T ell d),
      ProjectionNormalized T ell hT d M e h ∧
      (∀ (b a : ℕ) (hab : a ≤ b), Nonempty
        (CoefficientLineComparison
          (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
          (ell ^ (b + 1)) (ell ^ (a + 1))
          (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)) ∧
        (∀ (b a : ℕ) (hab : a ≤ b)
          (r : CoefficientLineComparison
            (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
            (ell ^ (b + 1)) (ell ^ (a + 1))
            (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T),
          (pbcDerivedExtend (pbcAdicQuotient T (datum.{u} ell) b a hab)).map (e b).hom ≫
              (scalarComparison T ell b a hab).hom.app (finiteTwist T ell b d) ≫
              (derivedRealization T ell a).map (proTwistMap d r) =
            (M.normalization b a hab).hom ≫ (e a).hom) := by
  sorry

end AlgebraicGeometry.Scheme.PurityIntegralTower
