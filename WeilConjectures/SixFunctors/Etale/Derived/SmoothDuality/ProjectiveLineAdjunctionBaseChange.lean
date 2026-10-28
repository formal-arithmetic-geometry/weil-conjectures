/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineAdjunction
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineBaseChange

/-!
# The projective-line adjunction commutes with base change

For a normalized Tate twist, the projective-line adjunction `Rq_! ⊣ Lq^*(1)[2]` of
`q : ℙ¹_S ⟶ S` (`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction`) commutes with every
base change `S' ⟶ S`, in the sense of
`AlgebraicGeometry.Etale.ProjectiveLineAdjunctionBaseChange` (blueprint `det-sp-p1-adjunction`,
subsection `sk-prop-geo-p1-adjunction`). This is recorded here, for that subsection to prove.

## Main statements

- `AlgebraicGeometry.Etale.projectiveLineAdjunctionBaseChange_of_isNormalized`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Compatibility required from `sk-prop-geo-p1-adjunction` (to be proved there):
blueprint `det-sp-p1-adjunction`.

**The projective-line adjunction commutes with base change.** For a normalized Tate twist and
every scheme `S` on which the exponent of `Λ` is invertible (affine or not), the adjunctions
`Rq_! ⊣ Lq^*(1)[2]` of the projective line `q : ℙ¹_S ⟶ S` and of its base change along any
`g : S' ⟶ S` have counits compatible with the compact-support base change, in the sense of
`AlgebraicGeometry.Etale.ProjectiveLineAdjunctionBaseChange`: the unit and the counit of the
blueprint are built from the cycle class of the diagonal, the trace, proper base change and the
projection formula, all of which commute with base change. -/
theorem projectiveLineAdjunctionBaseChange_of_isNormalized [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ] ⦃S : Scheme.{u}⦄ [HasInvertibleExponent Λ S]
    ⦃S' P' : Scheme.{u}⦄ {g : S' ⟶ S} {q' : P' ⟶ S'} {g' : P' ⟶ ℙ(Option (ULift.{u} (Fin 1)); S)}
    (sq : IsPullback g' q' (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) g) [HasCompactification q']
    [QuasiCompact q'] :
    haveI : HasInvertibleExponent Λ ℙ(Option (ULift.{u} (Fin 1)); S) := .of_hom (_ ↘ S)
    haveI : HasInvertibleExponent Λ P' := .of_hom (g' ≫ _ ↘ S)
    haveI : HasInvertibleExponent Λ S' := .of_hom g
    ∃ (adj : R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_![ModuleCat.{u + 1} Λ] ⊣
        L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
          twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)
      (adj' : R(q')_![ModuleCat.{u + 1} Λ] ⊣
        L((q')^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ P' 1),
      ∀ K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        (rightDerivedLowerShriekBaseChangeMap Λ sq).app
            ((twistShift Λ _ 1).obj
              ((L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
          (R(q')_![ModuleCat.{u + 1} Λ]).map
            ((leftDerivedUpperStarTwistShiftIso Λ g' 1 _).hom ≫
              (twistShift Λ P' 1).map ((derivedSquareUpperStarIso _ sq.toCommSq).inv.app K)) ≫
            adj'.counit.app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) =
          (L((g)^*[ModuleCat.{u + 1} Λ])).map (adj.counit.app K) :=
  sorry

end Etale

end AlgebraicGeometry
