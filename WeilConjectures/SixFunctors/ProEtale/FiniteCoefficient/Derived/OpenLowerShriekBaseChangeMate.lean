/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekCompactificationBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The base change isomorphism of the extension by zero as a mate

Let `j : U ⟶ Z` be an open immersion. On the unbounded derived categories of pro-étale sheaves,
the extension by zero `j_!` is left adjoint to the derived pullback `Lj^*`
(`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction`).

For a cartesian square `g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions, the mate of the
base change isomorphism `L(g'')^* j_! ≅ j'_! Lg'^*`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso`) along
these adjunctions is the square isomorphism `Lj^* Lg'^* ≅ L(g'')^* Lj'^*` of derived pullbacks.
This is an input for the compatibility of the compact-support exchange maps with the change of
coefficients (blueprint `sk-p-trace-coeff`).

## Main definitions

- `AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction`:
  the adjunction `j_! ⊣ Lj^*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section SquareIso

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The square isomorphism `j^* ⋙ g'^* ≅ g''^* ⋙ j'^*` of pullbacks of a commutative square
`g' ≫ j = j' ≫ g''` is conjugate to the square isomorphism of pushforwards. -/
lemma conjugateEquiv_upperStarCompIso_hom (sq : CommSq g' j' j g'') :
    conjugateEquiv ((upperStarLowerStarAdjunction A g'').comp (upperStarLowerStarAdjunction A j'))
      ((upperStarLowerStarAdjunction A j).comp (upperStarLowerStarAdjunction A g'))
      (upperStarCompIso A sq.w).hom = (ProEtale.squareLowerStarIso A sq).hom := by
  have hc : (upperStarCongr A sq.w).hom = (upperStarCongr A sq.w.symm).inv := by
    simp [upperStarCongr]
  rw [upperStarCompIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    ← conjugateEquiv_comp _ (upperStarLowerStarAdjunction A (g' ≫ j)),
    ← conjugateEquiv_comp _ (upperStarLowerStarAdjunction A (j' ≫ g'')), hc,
    conjugateEquiv_upperStarComp_hom, conjugateEquiv_upperStarCongr_inv,
    conjugateEquiv_upperStarComp_inv]
  simp [ProEtale.squareLowerStarIso]

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The weakly étale base change map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` is the mate, along the
adjunctions `g''^* ⊣ g''_*` and `g'^* ⊣ g'_*`, of the square isomorphism of pullbacks. -/
lemma baseChangeMap_eq_mateEquiv (sq : CommSq g' j' j g'') :
    ProEtale.baseChangeMap A sq =
      (mateEquiv (upperStarLowerStarAdjunction A g'') (upperStarLowerStarAdjunction A g')
        (upperStarCompIso A sq.w).hom).natTrans := by
  have h := iterated_mateEquiv_conjugateEquiv (upperStarLowerStarAdjunction A g'')
    (upperStarLowerStarAdjunction A g') (upperStarLowerStarAdjunction A j)
    (upperStarLowerStarAdjunction A j') (upperStarCompIso A sq.w).hom
  rw [conjugateEquiv_upperStarCompIso_hom A sq] at h
  rw [ProEtale.baseChangeMap]
  congr 1
  rw [Equiv.symm_apply_eq]
  exact (congrArg (TwoSquare.mk _ _ _ _) h).symm

end SquareIso

section Adjunction

variable {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]

end Adjunction

section BaseChange

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

end BaseChange

end AlgebraicGeometry.ProEtale
