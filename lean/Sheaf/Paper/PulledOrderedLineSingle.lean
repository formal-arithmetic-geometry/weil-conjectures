/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.SmoothPurityTowerGamma

/-! # Exact pullback of an ordered tower Tate line is in one degree

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-factors.proof.md, paragraph (1), removing the common even shift
(blueprint: lem-sp-pulled-ordered-line-single).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- Pullback of an ordered tower line admits a shifted single-sheaf presentation.
The prime is invertible on the source scheme. No orientation or exceptional
comparison is involved; the tower need not be normalized.

Source: latest blueprint, purity-bc-factors proof (1), removing the shift [2d];
Stacks 06XS and exact inverse image of constant-coefficient modules
(blueprint: lem-sp-pulled-ordered-line-single).

Proof:
1. In the section-preserving system model, each unshifted Tate factor is the
single complex of the corresponding sheaf tower. Each is flat: at every
coefficient level the root sheaf is a locally free rank-one sheaf, and
exactness and tensor in strict systems are computed levelwise. Hence every
finite ordered ordinary tensor of these factors is flat as well.
2. Compute the derived tensor on these degree-zero flat complexes. At d=0 the
ordered line is the single of the coefficient unit. At a successor tensor the
preceding single with the single of the first Tate factor shifted by two.
The K-flat tensor comparison identifies this with the single of the ordinary
tensor, shifted by 2d+2. This proves by induction that the ordered line is
isomorphic to a single sheaf tower shifted by 2d. The shift comparisons keep
the tensor order; no choice of generators or normalization of transitions is
used.
3. The supplied geometry uses exact ordinary inverse image of systems. Its
termwise derived functor commutes with singles and shifts. Apply it to the
presentation from step 2. The realization functors come from exact additive
equivalences of sheaf categories, so their derived functors and inverses also
commute with singles and shifts. Transport through the supplied isomorphism
and these equivalences to get the stated presentation on the original tower
category over X'. This includes d=0 and every ramification index. -/
theorem pulled_ordered_line_single
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (b : SpTowerShriek.Base ell E) (o : SpTowerShriek.Operations ell E b)
    (q : SpTowerCalculus.Coordinates ell E b)
    {X X' : Scheme.{u}} (u' : X' ⟶ X) (_hX : IsUnit (ell : Γ(X, ⊤)))
    (w : SpChartAdmissibility.Twists ell E X) (d : ℕ)
    (M : spDerivedCoefficientTowers ell E X (q.abelian X))
    (_line : (SpTowerCalculus.realization ell E b X (q.abelian X)).functor.obj M ≅
      SpTowerGamma.orderedLine ell E b X w d) :
    ∃ F : spCoefficientTowers ell E X',
      Nonempty ((SpTowerCalculus.etalePullback ell E b o q u').obj M ≅
        ((@DerivedCategory.singleFunctor _ _ _ (q.abelian X').hasDerived 0).obj F)⟦
          2 * (d : ℤ)⟧) := by sorry

end AlgebraicGeometry.ProEtale
