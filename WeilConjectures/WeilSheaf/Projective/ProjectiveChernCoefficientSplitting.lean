/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Projective.ProjectiveChernNormalization

/-! # The ordinary coefficient Chern summand

The coefficient arrow is defined before geometric-fibre pullback, tensoring with a
constructible sheaf, or forgetting native Weil structures.
Source: current blueprint, diagonal-tower trace (1).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- Ordinary coefficient modules before geometric base change.
Source: pulled-back condensed coefficients
(blueprint: lem-pur-a3-projective-chern-coefficient-splitting). -/
abbrev ProjectiveChernBaseModules := ProEtale.NativeCartier.Modules l X

/-- The regular coefficient module in degree zero.
Source: diagonal-tower trace (1)
(blueprint: lem-pur-a3-projective-chern-coefficient-splitting). -/
abbrev projectiveChernCoefficientUnit :=
  ProEtale.DiagonalCoefficients.unit (Profinite.padicAlgClRingObj l) X

/-- The positive coefficient Tate line in degree zero.
Source: diagonal-tower trace (1)
(blueprint: lem-pur-a3-projective-chern-coefficient-splitting). -/
abbrev projectiveChernCoefficientLine :=
  (DerivedCategory.singleFunctor (ProjectiveChernBaseModules (l := l) X) 0).obj
    (ProEtale.spQbarTwist X l)

/-- The exact pullback comparison on the regular coefficient module.
Source: module-object derived pullback and its canonical unit comparison
(blueprint: lem-pur-a3-projective-chern-coefficient-splitting). -/
def projectiveChernCoefficientPullUnit :
    (ProEtale.CondensedRing.moduleObjectDerivedPullback
      (Profinite.padicAlgClRingObj l) (ProjectiveLine X ↘ X)).obj
        (projectiveChernCoefficientUnit (l := l) X) ≅
      projectiveChernCoefficientUnit (l := l) (ProjectiveLine X) :=
  (Functor.singleFunctorCompLeftDerivedFunctorIso
    (ProEtale.CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (ProjectiveLine X ↘ X))).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (ProEtale.CondensedRing.upperStarObjRegularIso (Profinite.padicAlgClRingObj l)
        (ProjectiveLine X ↘ X))

/-- The ordinary adjunct of the actual positive infinity class in the given route.
Source: diagonal-tower trace (1), using the actual derived module adjunction
(blueprint: lem-pur-a3-projective-chern-coefficient-splitting). -/
def projectiveChernCoefficientAdjunct (C : ProEtale.NativeCartier.Construction k₀ l) :
    projectiveChernCoefficientUnit (l := l) X ⟶
      (ProEtale.CondensedRing.moduleObjectDerivedPushforward
        (Profinite.padicAlgClRingObj l) (ProjectiveLine X ↘ X)).obj
          ((projectiveChernCoefficientLine (l := l) (ProjectiveLine X))⟦(2 : ℤ)⟧) :=
  (ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction
    (Profinite.padicAlgClRingObj l) (ProjectiveLine X ↘ X)).homEquiv _ _
      ((projectiveChernCoefficientPullUnit (l := l) X).hom ≫
        (C.route (projectiveChernBase (k₀ := k₀) X) (ProjectiveLine.infinity X).ker
          (projectiveChernInfinityCartier X)).class)

/-- The ordinary coefficient Chern adjunct is the second component of a splitting.
This concerns coefficients alone, before geometric base change or tensoring with M.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-trace.proof.md, paragraph (1), and
sk-lem-geo-p1-cohomology/thm-amb-p1-decomposition.proof.md.
(blueprint: lem-pur-a3-projective-chern-coefficient-splitting).

Proof: restrict to affine opens of X. Infinity has positive divisor line O(1).
The source and positive Kummer normalizations in the supplied integral route
identify its strict-system class with the simultaneous reduction of c1(O(1)).
The finite projective-line calculation makes its unit/Chern biproduct invertible
at every level; levelwise cohomology detects invertibility in the strict tower
category. Positively twist and shift this splitting. Restrict to constant Z_l
coefficients and apply the supplied total right-derived limit. The unit and root
comparisons in IntegralRoute.Lifts identify the whole limiting Chern arrow.
Completed restriction is fully faithful on complete objects. Both coefficient
lines are complete, and their proper direct images are complete, so it uniquely
lifts the splitting and identifies its second component with completed. The
specified completed realization and its underlying-sheaf normalization identify
unit and root endpoints. Apply the three actual scalar extensions in
OrdinaryRoute.class, using the proper direct-image comparisons and their unit
and root equations. Each preserves the biproduct isomorphism and its second
component. The resulting second component is exactly the adjunct defined here.
Exact open restriction preserves all these maps. Their cones vanish on the
affine cover, so the global biproduct is invertible. For the first component one
may take the adjunct of the Cartesian Tate pullback; thus this argument does
not glue arbitrary derived morphisms. Empty X and the zero coefficient module
satisfy the same equations. -/
theorem projectiveChern_coefficient_splitting
    (C : ProEtale.NativeCartier.Construction k₀ l) :
    ∃ v : (projectiveChernCoefficientLine (l := l) X)⟦(2 : ℤ)⟧ ⟶
        (ProEtale.CondensedRing.moduleObjectDerivedPushforward
          (Profinite.padicAlgClRingObj l) (ProjectiveLine X ↘ X)).obj
            ((projectiveChernCoefficientLine (l := l) (ProjectiveLine X))⟦(2 : ℤ)⟧),
      IsIso (biprod.desc v (projectiveChernCoefficientAdjunct X C)) := by sorry

end AlgebraicGeometry.WeilComplex
