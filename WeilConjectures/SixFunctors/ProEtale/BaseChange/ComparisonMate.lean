/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

/-!
# The comparison of direct images is the mate of the comparison of pullbacks

For a quasi-compact quasi-separated morphism `f : X ⟶ Y`, the comparison isomorphism
`ν_Y^* Rf_* ≅ Rf_* ν_X^*` (`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso'`) is
the mate, under the derived adjunctions `f^* ⊣ Rf_*` (étale, bounded below) and
`Lf^* ⊣ Rf_*` (pro-étale), of the inverse of the comparison isomorphism
`ν_X^* f^* ≅ Lf^* ν_Y^*` (`AlgebraicGeometry.ProEtale.leftDerivedUpperStarComparisonIso`).

The underived counterpart (`AlgebraicGeometry.ProEtale.lowerStarComparisonUpperStarBaseChange_eq`)
is formal: both underived comparisons are obtained by taking mates of the same isomorphism
`f_* ν_{X,*} ≅ ν_{Y,*} f_*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Underived

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The underived base change morphism `ν_Y^* f_* ⟶ f_* ν_X^*` is the mate, under the
adjunctions `f^* ⊣ f_*` on the étale and on the pro-étale sites, of the comparison
`ν_Y^* ⋙ f^* ≅ f^* ⋙ ν_X^*` of pullbacks. -/
lemma lowerStarComparisonUpperStarBaseChange_eq :
    lowerStarComparisonUpperStarBaseChange f A =
      mateEquiv (Etale.upperStarLowerStarAdjunction A f)
        (ProEtale.upperStarLowerStarAdjunction A f)
        (comparisonUpperStarCompUpperStarIso A f).hom := by
  rw [lowerStarComparisonUpperStarBaseChange, Equiv.symm_apply_eq]
  ext1
  rw [iterated_mateEquiv_conjugateEquiv]
  exact congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply _).symm

end Underived

end ProEtale

end AlgebraicGeometry
