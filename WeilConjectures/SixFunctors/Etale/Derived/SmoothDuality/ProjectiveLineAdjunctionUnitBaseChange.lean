/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.UnitOfCounitSquare
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineAdjunctionBaseChange

/-!
# The unit of the projective-line adjunction commutes with base change

For `q : ℙ¹_S ⟶ S` the projective-line adjunction `Rq_! ⊣ Lq^*(1)[2]`
(`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction`) has the trace counit
`AlgebraicGeometry.Etale.projectiveLineCounit`, which commutes with every base change
`g : S' ⟶ S` (`AlgebraicGeometry.Etale.projectiveLineCounit_baseChange`). The unit is determined by
the counit through the triangle identities, so it commutes with base change as well
(`CategoryTheory.Adjunction.unit_comp_of_counit_comp`): with `g' : ℙ¹_{S'} ⟶ ℙ¹_S` the base
change of `g`, the pullback `Lg'^* η_M` of the unit at `M`, followed by the identification
`Lg'^*(Lq^*(-)(1)[2]) ≅ Lq'^* Lg^*(-)(1)[2]` and by `Ex_! : Lg^* Rq_! ⟶ Rq'_! Lg'^*`, is the unit
at `Lg'^* M`. This is blueprint `proposition-adjunction-projective-line--2`.

## Main statements

- `AlgebraicGeometry.Etale.projectiveLineAdjunction_unit_baseChange`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {S S' : Scheme.{u}} [HasInvertibleExponent Λ S]
  [HasInvertibleExponent Λ S']

/-- Blueprint `proposition-adjunction-projective-line--2`: *the unit of the projective-line
adjunction is compatible with base change*. Let `adj : Rq_! ⊣ Lq^*(1)[2]` and
`adj' : Rq'_! ⊣ Lq'^*(1)[2]` be the projective-line adjunctions of `q : ℙ¹_S ⟶ S` and of its base
change `q' : ℙ¹_{S'} ⟶ S'` along `g : S' ⟶ S`, i.e. the adjunctions whose counits are the trace
counits `AlgebraicGeometry.Etale.projectiveLineCounit`
(`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction`).
Then for every `M ∈ D(ℙ¹_S)` the pullback `Lg'^* η_M` of the unit, followed by the identification
`Lg'^*(Lq^* Rq_! M (1)[2]) ≅ Lq'^* Lg^* Rq_! M (1)[2]` and by `Lq'^*(Ex_!)(1)[2]`, is the unit
`η'_{Lg'^* M}`. -/
theorem projectiveLineAdjunction_unit_baseChange (g : S' ⟶ S)
    (adj : R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_![ModuleCat.{u + 1} Λ] ⊣
      L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)
    (adj' : R((ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S'))_![ModuleCat.{u + 1} Λ] ⊣
      L(((ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S'))^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S') 1)
    (hadj : ∀ K, adj.counit.app K = projectiveLineCounit Λ S K)
    (hadj' : ∀ K, adj'.counit.app K = projectiveLineCounit Λ S' K)
    (M : _root_.DerivedCategory
      (Sheaf ℙ(Option (ULift.{u} (Fin 1)); S).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g)^*[ModuleCat.{u + 1} Λ])).map
        (adj.unit.app M) ≫
      (leftDerivedUpperStarTwistShiftIso Λ
          (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g) 1 _).hom ≫
      (twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S') 1).map
        ((derivedSquareUpperStarIso _
          (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g).toCommSq).inv.app
            ((R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_![ModuleCat.{u + 1} Λ]).obj M)) ≫
      (L(((ℙ(Option (ULift.{u} (Fin 1)); S') ↘ S'))^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S') 1).map
        ((rightDerivedLowerShriekBaseChangeMap Λ
          (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g)).app M) =
      adj'.unit.app ((L((ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g)^*[
        ModuleCat.{u + 1} Λ])).obj M) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ
    (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g)
  have := Adjunction.unit_comp_of_counit_comp adj adj'
    (rightDerivedLowerShriekBaseChangeMap Λ
      (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g))
    (fun K ↦ (leftDerivedUpperStarTwistShiftIso Λ
        (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) g) 1 _).hom ≫
      (twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S') 1).map
        ((derivedSquareUpperStarIso _
          (ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) g).toCommSq).inv.app K))
    (fun K ↦ by
      rw [hadj, hadj']
      exact projectiveLineCounit_baseChange g K) M
  simpa only [Category.assoc] using this

end Etale

end AlgebraicGeometry
