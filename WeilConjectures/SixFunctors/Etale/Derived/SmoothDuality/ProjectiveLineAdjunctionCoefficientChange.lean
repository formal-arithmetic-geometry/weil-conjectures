/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.UnitOfCounitSquare
public import WeilConjectures.Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.SixFunctors.Etale.Derived.CompactSupportCoefficientChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTraceCounitTensorRight
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
(`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction`) is compatible with this change of
coefficients:

* the counit, through the coefficient change of compact support
  `(Rq_! M) ⊗ᴸ B ≅ Rq_!(M ⊗ᴸ B)` (`AlgebraicGeometry.Etale.compactSupportCoefficientChangeIso`)
  and the identification `(Lq^* K)(1)[2] ⊗ᴸ B ≅ Lq^*(K ⊗ᴸ B)(1)[2]`
  (`AlgebraicGeometry.Etale.projectiveLineReductionModIdealIso`)
  (`AlgebraicGeometry.Etale.projectiveLineAdjunction_counit_reductionModIdeal`);
* and so is the unit
  (`AlgebraicGeometry.Etale.projectiveLineAdjunction_unit_reductionModIdeal`).

## Main definitions

- `AlgebraicGeometry.Etale.twistShiftOneReductionModIdealIso`
- `AlgebraicGeometry.Etale.projectiveLineReductionModIdealIso`

## Main statements

- `AlgebraicGeometry.Etale.projectiveLineCounit_reductionModIdeal`
- `AlgebraicGeometry.Etale.projectiveLineAdjunction_counit_reductionModIdeal`
- `AlgebraicGeometry.Etale.projectiveLineAdjunction_unit_reductionModIdeal`

## Implementation notes

The compatibility of the counit is the general compatibility of trace counits with change of
coefficients (`AlgebraicGeometry.Etale.lowerShriekTraceCounit_reductionModIdeal`), an instance of
the associativity of the projection map
(`AlgebraicGeometry.Etale.traceCounit_derivedTensorRight`). Its statements write the constant
complex `(Λ ⧸ J)_X` as `AlgebraicGeometry.Etale.constantSingle` and the reduction
`K ⊗ᴸ (Λ ⧸ J)_X` with `AlgebraicGeometry.Etale.derivedTensorRight`, as the general statement
does: the kernel cannot compare in reasonable time projection maps evaluated at objects written
differently, such as `AlgebraicGeometry.Etale.constantQuotient` and
`AlgebraicGeometry.Etale.constantSingle`; the only such comparison is made through `HEq`
(`AlgebraicGeometry.Etale.projectionMap_app_app_constantQuotient`).

The unit is determined by the counit through the triangle identities, so its compatibility
follows from that of the counit by `CategoryTheory.Adjunction.unit_comp_of_counit_comp`.
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
`K(1)[2] ⊗ᴸ (Λ ⧸ J)_X ≅ (K ⊗ᴸ (Λ ⧸ J)_X)(1)[2]`, naturally in `K`. It is the associator
`(Λ(1)[2] ⊗ᴸ K) ⊗ᴸ (Λ ⧸ J)_X ≅ Λ(1)[2] ⊗ᴸ (K ⊗ᴸ (Λ ⧸ J)_X)`
(`AlgebraicGeometry.Etale.derivedTensorObjCompDerivedTensorRightIso`), read through the
identifications `K(1)[2] ≅ Λ(1)[2] ⊗ᴸ K` (`AlgebraicGeometry.Etale.twistShiftOneIsoTensor`). -/
noncomputable def twistShiftOneReductionModIdealIso (X : Scheme.{u}) :
    twistShift Λ X 1 ⋙ reductionModIdeal Λ X J ≅ reductionModIdeal Λ X J ⋙ twistShift Λ X 1 :=
  Functor.isoWhiskerRight (twistShiftOneIsoTensor Λ X)
      (derivedTensorRight _ X (constantSingle _ X (ModuleCat.of Λ (Λ ⧸ J)))) ≪≫
    derivedTensorObjCompDerivedTensorRightIso _ X _
      (constantSingle _ X (ModuleCat.of Λ (Λ ⧸ J))) ≪≫
    Functor.isoWhiskerLeft (derivedTensorRight _ X (constantSingle _ X (ModuleCat.of Λ (Λ ⧸ J))))
      (twistShiftOneIsoTensor Λ X).symm

/-- For `q : ℙ¹_S ⟶ S`, the functor `Lq^*(-)(1)[2]` commutes with the reduction of the
coefficients: `(Lq^* K)(1)[2] ⊗ᴸ (Λ ⧸ J)_{ℙ¹_S} ≅ Lq^*(K ⊗ᴸ (Λ ⧸ J)_S)(1)[2]`, naturally in `K`:
the commutation `AlgebraicGeometry.Etale.twistShiftOneReductionModIdealIso` at `Lq^* K`, followed
by the twist-and-shift of `Lq^* K ⊗ᴸ (Λ ⧸ J) ≅ Lq^*(K ⊗ᴸ (Λ ⧸ J))`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarReductionModIdealIso`). -/
noncomputable def projectiveLineReductionModIdealIso (S : Scheme.{u}) :
    (L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1) ⋙
        reductionModIdeal Λ ℙ(Option (ULift.{u} (Fin 1)); S) J ≅
      reductionModIdeal Λ S J ⋙
        (L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
          twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1) :=
  Functor.isoWhiskerLeft L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])
      (twistShiftOneReductionModIdealIso Λ J ℙ(Option (ULift.{u} (Fin 1)); S)) ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarReductionModIdealIso Λ J _).symm
      (twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)

omit [Finite Λ] [HasKummerClass Λ] in
/-- The projection map at the constant complex `(Λ ⧸ J)_Y`, written as
`AlgebraicGeometry.Etale.constantQuotient` or as `AlgebraicGeometry.Etale.constantSingle`. The
proof goes through `HEq`, so that the kernel does not unfold the projection map. -/
lemma projectionMap_app_app_constantQuotient {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app (constantQuotient Λ J Y) =
      ((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app
        (constantSingle _ Y (ModuleCat.of Λ (Λ ⧸ J))) :=
  eq_of_heq (congr_arg_heq (((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app) rfl)

omit [HasKummerClass Λ] in
/-- **Trace counits and change of finite coefficients.** For `f : X ⟶ Y`, a trace
`t : Rf_! T ⟶ Λ_Y` and identifications `γ_K : G K ≅ T ⊗ᴸ Lf^* K`, let
`θ : (G K) ⊗ᴸ (Λ ⧸ J)_X ⟶ G(K ⊗ᴸ (Λ ⧸ J)_Y)` be compatible with `γ` through the associator and
`Lf^*(K ⊗ᴸ (Λ ⧸ J)_Y) ≅ Lf^* K ⊗ᴸ (Λ ⧸ J)_X`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarReductionModIdealIso`). Then the trace counit
(`AlgebraicGeometry.Etale.lowerShriekTraceCounit`) at `K ⊗ᴸ (Λ ⧸ J)_Y`, read through the
coefficient change of compact support
(`AlgebraicGeometry.Etale.compactSupportCoefficientChangeIso`) and `θ`, is the reduction of the
trace counit at `K` (`AlgebraicGeometry.Etale.traceCounit_derivedTensorRight`). -/
theorem lowerShriekTraceCounit_reductionModIdeal {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    (T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (t : (R(f)_![ModuleCat.{u + 1} Λ]).obj T ⟶ 𝟙_ _)
    {G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : ∀ K, G.obj K ≅ ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj T).obj
      ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (θ : (reductionModIdeal Λ X J).obj (G.obj K) ⟶
      G.obj ((derivedTensorRight _ Y (constantSingle _ Y (ModuleCat.of Λ (Λ ⧸ J)))).obj K))
    (hθ : θ ≫
        (γ ((derivedTensorRight _ Y (constantSingle _ Y (ModuleCat.of Λ (Λ ⧸ J)))).obj K)).hom =
      (derivedTensorRight _ X (constantSingle _ X (ModuleCat.of Λ (Λ ⧸ J)))).map (γ K).hom ≫
        (derivedTensorRightTensorIso _ (constantSingle _ X (ModuleCat.of Λ (Λ ⧸ J))) T
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).hom ≫
        ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj T).map
          ((leftDerivedUpperStarReductionModIdealIso Λ J f).app K).inv) :
    (compactSupportCoefficientChangeIso Λ f J).hom.app (G.obj K) ≫
        (R(f)_![ModuleCat.{u + 1} Λ]).map θ ≫
        lowerShriekTraceCounit Λ f T t γ
          ((derivedTensorRight _ Y (constantSingle _ Y (ModuleCat.of Λ (Λ ⧸ J)))).obj K) =
      (reductionModIdeal Λ Y J).map (lowerShriekTraceCounit Λ f T t γ K) := by
  have : IsIso (projectionMap (ModuleCat.{u + 1} Λ) f) := isIso_projectionMap_of_finite Λ f
  have hK : IsIso (((projectionMap (ModuleCat.{u + 1} Λ) f).app T).app K) := inferInstance
  have hKN : IsIso (((projectionMap (ModuleCat.{u + 1} Λ) f).app T).app
      ((derivedTensorRight _ Y (constantSingle _ Y (ModuleCat.of Λ (Λ ⧸ J)))).obj K)) :=
    inferInstance
  rw [compactSupportCoefficientChangeIso_hom_app, projectionMap_app_app_constantQuotient,
    lowerShriekTraceCounit, lowerShriekTraceCounit]
  exact traceCounit_derivedTensorRight _ f T t γ
    (leftDerivedUpperStarSingleConstantSheafIso _ f (ModuleCat.of Λ (Λ ⧸ J))) K _
    (@IsIso.hom_inv_id _ _ _ _ _ hK) (@IsIso.inv_hom_id _ _ _ _ _ hK) _
    (@IsIso.hom_inv_id _ _ _ _ _ hKN) (@IsIso.inv_hom_id _ _ _ _ _ hKN) _ rfl _ rfl
    θ hθ

omit [Finite Λ] in
/-- The identification `q^* K(1)[2] ≅ Λ(1)[2] ⊗ᴸ Lq^* K`
(`AlgebraicGeometry.Etale.projectiveLineTwistShiftIso`) is the component of
`AlgebraicGeometry.Etale.twistShiftOneIsoTensor` at `Lq^* K`. -/
lemma twistShiftOneIsoTensor_hom_app_leftDerivedUpperStar (S : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (twistShiftOneIsoTensor Λ ℙ(Option (ULift.{u} (Fin 1)); S)).hom.app
        ((L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).obj K) =
      (projectiveLineTwistShiftIso Λ S K).hom :=
  rfl

omit [Finite Λ] in
/-- Through `q^* K(1)[2] ≅ Λ(1)[2] ⊗ᴸ Lq^* K`
(`AlgebraicGeometry.Etale.projectiveLineTwistShiftIso`), the identification
`AlgebraicGeometry.Etale.projectiveLineReductionModIdealIso` is the associator followed by
`Lq^* K ⊗ᴸ (Λ ⧸ J) ≅ Lq^*(K ⊗ᴸ (Λ ⧸ J))`. -/
lemma projectiveLineReductionModIdealIso_hom_app_comp (S : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (projectiveLineReductionModIdealIso Λ J S).hom.app K ≫
        (projectiveLineTwistShiftIso Λ S
          ((derivedTensorRight _ S (constantSingle _ S (ModuleCat.of Λ (Λ ⧸ J)))).obj K)).hom =
      (derivedTensorRight _ _
          (constantSingle _ ℙ(Option (ULift.{u} (Fin 1)); S) (ModuleCat.of Λ (Λ ⧸ J)))).map
          (projectiveLineTwistShiftIso Λ S K).hom ≫
        (derivedTensorRightTensorIso _
          (constantSingle _ ℙ(Option (ULift.{u} (Fin 1)); S) (ModuleCat.of Λ (Λ ⧸ J))) _
          ((L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).obj K)).hom ≫
        ((-⊗ᴸ-(ℙ(Option (ULift.{u} (Fin 1)); S))[ModuleCat.{u + 1} Λ]).obj
          ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧)).map
          ((leftDerivedUpperStarReductionModIdealIso Λ J _).app K).inv := by
  have h := Functor.isoWhiskerLeft_trans_isoWhiskerRight_symm_hom_app_comp
    L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])
    (twistShiftOneIsoTensor Λ ℙ(Option (ULift.{u} (Fin 1)); S))
    (derivedTensorObjCompDerivedTensorRightIso _ ℙ(Option (ULift.{u} (Fin 1)); S) _
      (constantSingle _ ℙ(Option (ULift.{u} (Fin 1)); S) (ModuleCat.of Λ (Λ ⧸ J))))
    (leftDerivedUpperStarReductionModIdealIso Λ J (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)) K
  rw [derivedTensorObjCompDerivedTensorRightIso_hom_app,
    twistShiftOneIsoTensor_hom_app_leftDerivedUpperStar,
    twistShiftOneIsoTensor_hom_app_leftDerivedUpperStar, ← Iso.app_inv] at h
  exact h

variable [HasKummerClass.IsNormalized Λ] {S : Scheme.{u}} [HasInvertibleExponent Λ S]

/-- The counit of the projective-line adjunction is compatible with change of finite
coefficients: for an ideal `J` of `Λ` and `B = Λ ⧸ J`, the counit
`ε_K : Rq_!(Lq^* K (1)[2]) ⟶ K` of the projective-line adjunction (the trace counit
`AlgebraicGeometry.Etale.projectiveLineCounit`) satisfies

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
  rw [projectiveLineCounit, projectiveLineCounit]
  exact lowerShriekTraceCounit_reductionModIdeal Λ J _ _ (projectiveLineLowerShriekTrace Λ S)
    (G := L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
      twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)
    (projectiveLineTwistShiftIso Λ S) K _
    (projectiveLineReductionModIdealIso_hom_app_comp Λ J S K)

/-- For every adjunction `adj : Rq_! ⊣ Lq^*(1)[2]` with the trace counit
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

/-- The unit of the projective-line adjunction is compatible with change of finite coefficients:
for every adjunction `adj : Rq_! ⊣ Lq^*(1)[2]` with the trace counit
(`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction`), an ideal `J` of `Λ` and
`M ∈ D(ℙ¹_S)`, the unit `η_M ⊗ᴸ B` at `M`, followed by the identification
`(Lq^* Rq_! M)(1)[2] ⊗ᴸ B ≅ Lq^*((Rq_! M) ⊗ᴸ B)(1)[2]` and by `Lq^*` of the coefficient change of
compact support `(Rq_! M) ⊗ᴸ B ≅ Rq_!(M ⊗ᴸ B)`, is the unit `η_{M ⊗ᴸ B}`. -/
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
