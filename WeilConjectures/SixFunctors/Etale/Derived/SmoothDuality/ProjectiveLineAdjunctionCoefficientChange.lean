/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.UnitOfCounitSquare
public import WeilConjectures.SixFunctors.Etale.Derived.CompactSupportCoefficientChange
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.AffineSpaceTwistAdjunction

/-!
# The projective-line adjunction and change of finite coefficients

Let `Λ` be a finite coefficient ring (the stage `A = A_{E,n}`) and `J` an ideal of `Λ`
(`B = Λ ⧸ J`). As everywhere in the repository (see
`AlgebraicGeometry.Etale.compactSupportCoefficientChangeIso`), the change of coefficients
`- ⊗ᴸ_A B` is realised inside `D(-, Λ)` as the reduction `K ↦ K ⊗ᴸ (Λ ⧸ J)_X`
(`AlgebraicGeometry.Etale.reductionModIdeal`).

For `q : ℙ¹_S ⟶ S` the projective-line adjunction `Rq_! ⊣ Lq^*(1)[2]`
(`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction`, blueprint
`proposition-adjunction-projective-line`) is compatible with this change of coefficients:

* the counit, through the coefficient change of compact support
  `(Rq_! M) ⊗ᴸ B ≅ Rq_!(M ⊗ᴸ B)` (`AlgebraicGeometry.Etale.compactSupportCoefficientChangeIso`)
  and the identification `(Lq^* K)(1)[2] ⊗ᴸ B ≅ Lq^*(K ⊗ᴸ B)(1)[2]`
  (`AlgebraicGeometry.Etale.projectiveLineReductionModIdealIso`)
  (`AlgebraicGeometry.Etale.projectiveLineAdjunction_counit_reductionModIdeal`, blueprint
  `proposition-adjunction-projective-line--5`);
* hence the unit, which is determined by the counit through the triangle identities
  (`AlgebraicGeometry.Etale.projectiveLineAdjunction_unit_reductionModIdeal`, blueprint
  `proposition-adjunction-projective-line--4`).

## Main definitions

- `AlgebraicGeometry.Etale.twistShiftOneReductionModIdealIso`
- `AlgebraicGeometry.Etale.projectiveLineReductionModIdealIso`

## Main statements

- `AlgebraicGeometry.Etale.projectiveLineAdjunction_counit_reductionModIdeal`
- `AlgebraicGeometry.Etale.projectiveLineAdjunction_unit_reductionModIdeal`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ] (J : Ideal Λ)

/-- The twist-and-shift commutes with the reduction of the coefficients:
`K(1)[2] ⊗ᴸ (Λ ⧸ J)_X ≅ (K ⊗ᴸ (Λ ⧸ J)_X)(1)[2]`, naturally in `K`. Both sides are tensor products
with `Λ(1)[2]` and `(Λ ⧸ J)_X`, in two orders, which are exchanged by the braiding. -/
noncomputable def twistShiftOneReductionModIdealIso (X : Scheme.{u}) :
    twistShift Λ X 1 ⋙ reductionModIdeal Λ X J ≅ reductionModIdeal Λ X J ⋙ twistShift Λ X 1 :=
  Functor.isoWhiskerRight (derivedTensorRightShiftIso _ (tateObject Λ X 1) 2).symm _ ≪≫
    derivedTensorFlipObjCompIso Λ X _ _ ≪≫
    (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).flip.mapIso (derivedTensorBraidingIso _ X _ _) ≪≫
    (derivedTensorFlipObjCompIso Λ X _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (derivedTensorRightShiftIso _ (tateObject Λ X 1) 2)

/-- For `q : ℙ¹_S ⟶ S`, the functor `Lq^*(-)(1)[2]` commutes with the reduction of the
coefficients: `(Lq^* K)(1)[2] ⊗ᴸ (Λ ⧸ J)_{ℙ¹_S} ≅ Lq^*(K ⊗ᴸ (Λ ⧸ J)_S)(1)[2]`, naturally in `K`,
by `AlgebraicGeometry.Etale.twistShiftOneReductionModIdealIso` and the commutation of `Lq^*`
with the reduction (`AlgebraicGeometry.Etale.leftDerivedUpperStarReductionModIdealIso`). -/
noncomputable def projectiveLineReductionModIdealIso (S : Scheme.{u}) :
    (L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1) ⋙
        reductionModIdeal Λ ℙ(Option (ULift.{u} (Fin 1)); S) J ≅
      reductionModIdeal Λ S J ⋙
        (L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
          twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (twistShiftOneReductionModIdealIso Λ J _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarReductionModIdealIso Λ J _).symm _ ≪≫
    Functor.associator _ _ _

variable [HasKummerClass.IsNormalized Λ] {S : Scheme.{u}} [HasInvertibleExponent Λ S]

/-- Blueprint `proposition-adjunction-projective-line--5`: *the counit of the projective-line
adjunction is compatible with change of finite coefficients*. For an ideal `J` of `Λ` and
`B = Λ ⧸ J`, the counit `ε_K : Rq_!(Lq^* K (1)[2]) ⟶ K` of the projective-line adjunction
(the trace counit `AlgebraicGeometry.Etale.projectiveLineCounit`) satisfies

`(Rq_! Lq^* K (1)[2]) ⊗ᴸ B ≅ Rq_!((Lq^* K (1)[2]) ⊗ᴸ B) ≅ Rq_!(Lq^*(K ⊗ᴸ B)(1)[2])
  --ε_{K ⊗ᴸ B}--> K ⊗ᴸ B` `= ε_K ⊗ᴸ B`,

through the coefficient change of compact support
(`AlgebraicGeometry.Etale.compactSupportCoefficientChangeIso`) and
`AlgebraicGeometry.Etale.projectiveLineReductionModIdealIso`. -/
theorem projectiveLineCounit_reductionModIdeal
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactSupportCoefficientChangeIso Λ ((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)) J).hom.app
        ((twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1).obj
          ((L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
      (R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_![ModuleCat.{u + 1} Λ]).map
        ((projectiveLineReductionModIdealIso Λ J S).hom.app K) ≫
      projectiveLineCounit Λ S ((reductionModIdeal Λ S J).obj K) =
    (reductionModIdeal Λ S J).map (projectiveLineCounit Λ S K) := by
  sorry

/-- Blueprint `proposition-adjunction-projective-line--5`, for the adjunction: for every
adjunction `adj : Rq_! ⊣ Lq^*(1)[2]` with the trace counit
(`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction`), the counit is compatible with the
change of finite coefficients `- ⊗ᴸ (Λ ⧸ J)`
(`AlgebraicGeometry.Etale.projectiveLineCounit_reductionModIdeal`). -/
theorem projectiveLineAdjunction_counit_reductionModIdeal
    (adj : R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_![ModuleCat.{u + 1} Λ] ⊣
      L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)
    (hadj : ∀ K, adj.counit.app K = projectiveLineCounit Λ S K)
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactSupportCoefficientChangeIso Λ ((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)) J).hom.app
        ((twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1).obj
          ((L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
      (R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_![ModuleCat.{u + 1} Λ]).map
        ((projectiveLineReductionModIdealIso Λ J S).hom.app K) ≫
      adj.counit.app ((reductionModIdeal Λ S J).obj K) =
    (reductionModIdeal Λ S J).map (adj.counit.app K) := by
  rw [hadj, hadj]
  exact projectiveLineCounit_reductionModIdeal Λ J K

/-- Blueprint `proposition-adjunction-projective-line--4`: *the unit of the projective-line
adjunction is compatible with change of finite coefficients*. For every adjunction
`adj : Rq_! ⊣ Lq^*(1)[2]` with the trace counit
(`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction`), an ideal `J` of `Λ` and
`M ∈ D(ℙ¹_S)`, the unit `η_M ⊗ᴸ B` at `M`, followed by the identification
`(Lq^* Rq_! M)(1)[2] ⊗ᴸ B ≅ Lq^*((Rq_! M) ⊗ᴸ B)(1)[2]` and by `Lq^*` of the coefficient change of
compact support `(Rq_! M) ⊗ᴸ B ≅ Rq_!(M ⊗ᴸ B)`, is the unit `η_{M ⊗ᴸ B}`. It follows from the
compatibility of the counit (`AlgebraicGeometry.Etale.projectiveLineCounit_reductionModIdeal`),
the unit being determined by the counit. -/
theorem projectiveLineAdjunction_unit_reductionModIdeal
    (adj : R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_![ModuleCat.{u + 1} Λ] ⊣
      L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)
    (hadj : ∀ K, adj.counit.app K = projectiveLineCounit Λ S K)
    (M : _root_.DerivedCategory
      (Sheaf ℙ(Option (ULift.{u} (Fin 1)); S).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (reductionModIdeal Λ ℙ(Option (ULift.{u} (Fin 1)); S) J).map (adj.unit.app M) ≫
      (projectiveLineReductionModIdealIso Λ J S).hom.app
        ((R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_![ModuleCat.{u + 1} Λ]).obj M) ≫
      (L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1).map
        ((compactSupportCoefficientChangeIso Λ ((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)) J).hom.app
          M) =
      adj.unit.app ((reductionModIdeal Λ ℙ(Option (ULift.{u} (Fin 1)); S) J).obj M) :=
  Adjunction.unit_comp_of_counit_comp adj adj
    (compactSupportCoefficientChangeIso Λ ((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)) J).hom
    (fun K ↦ (projectiveLineReductionModIdealIso Λ J S).hom.app K)
    (projectiveLineAdjunction_counit_reductionModIdeal Λ J adj hadj) M

end Etale

end AlgebraicGeometry
