/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedERealizationDefinitions

/-! # Normalization of canonical realization exchange
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15; Stacks Tag 07A7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures.CondensedERealization
variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
variable (D : Data l E k)
variable {X' X Y' Y : Base k}
variable {g' : X'.scheme ⟶ X.scheme} {f' : X'.scheme ⟶ Y'.scheme}
  {f : X.scheme ⟶ Y.scheme} {g : Y'.scheme ⟶ Y.scheme}
variable [g'.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))]
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]

/-- The rational mate realizes to the continuous coefficient mate.
Source: Stacks Tag 07A7; Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-weil-pbc-condensed-e-realization-mate-normalization)
Proof. For the two composite morphisms, Data.composition compares rationalComp with
the continuous upper-star compositor. Equality elimination compares their transport
isomorphisms. Cancel the two compositors to obtain the pull-comparison cube for
Data.square and fieldSquare. Apply injectivity of the inverse Hom equivalence of
the final continuous adjunction. Expand its counit formula. The two mate counit
identities replace the adjuncts of Data.mate and fieldBaseChange. Naturality of the
continuous square, the push comparisons and the counit moves comparison maps to the
ends. The supplied counit comparison laws replace the two vertical terms, and the
pull-comparison cube identifies what remains. Cancel the pull-comparison isomorphisms
and conclude by injectivity. The calculation works at every rational object; no
properness, exchange invertibility, or integral existence hypothesis is needed. -/
theorem realizationMate_normalization (sq : CommSq g' f' f g) (K : Rational l E X.scheme) :
    (D.atObject Y').realization.functor.map ((Data.mate l E k D sq).app K) ≫
      (D.along X' Y' f').pushComparison.hom.app ((D.along X' X g').rationalPull.obj K) ≫
      (fieldLowerStar l E k X' Y' f').map
        ((D.along X' X g').pullComparison.hom.app K) =
    (D.along Y' Y g).pullComparison.hom.app ((D.along X Y f).rationalPush.obj K) ≫
      (boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
        (Base.map Y' Y g)).map ((D.along X Y f).pushComparison.hom.app K) ≫
      (fieldBaseChange l E k sq).app ((D.atObject X).realization.functor.obj K) := by
  sorry

end WeilConjectures.CondensedERealization
