/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.OverSquare

public import Sheaf.Paper.ContinuousIntegralComparisons
import Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-! # Coherence of integral localization and the specified exchange map -/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

private lemma coefficient_counit
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {E₁ : A ⥤ B} {Res₁ : B ⥤ A} (adj₁ : E₁ ⊣ Res₁)
    {E₂ : A' ⥤ B'} {Res₂ : B' ⥤ A'} (adj₂ : E₂ ⊣ Res₂)
    {U₁ : A' ⥤ A} {L₁ : A ⥤ A'} (adjR : U₁ ⊣ L₁)
    {U₂ : B' ⥤ B} {L₂ : B ⥤ B'} (adjS : U₂ ⊣ L₂)
    (e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁) (M : A) :
    U₂.map ((Adjunction.pushHomOfComapIso adj₁ adj₂ e).app M) ≫
      adjS.counit.app (E₁.obj M) =
    (Adjunction.pullIsoOfComapIso adj₁ adj₂ adjR adjS e).inv.app (L₁.obj M) ≫
      E₁.map (adjR.counit.app M) := by
  have hm := iterated_mateEquiv_conjugateEquiv_symm adjR adjS adj₂ adj₁
    (TwoSquare.mk _ _ _ _ e.inv)
  have hc := mateEquiv_counit_symm adjR adjS
    (TwoSquare.mk _ _ _ _ (Adjunction.pushHomOfComapIso adj₁ adj₂ e)) M
  rw [show (mateEquiv adjR adjS).symm
      (TwoSquare.mk _ _ _ _ (Adjunction.pushHomOfComapIso adj₁ adj₂ e)) =
    TwoSquare.mk _ _ _ _
      (Adjunction.pullIsoOfComapIso adj₁ adj₂ adjR adjS e).inv from hm] at hc
  exact hc

private lemma source_normal_form
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (G : C ⥤ C') (H : D ⥤ D')
    (θ : G ⋙ L' ≅ L ⋙ H) (β : R ⋙ G ⟶ H ⋙ R')
    (N : D) (M : C) (A : C') (s : A ⟶ G.obj M) (δ : M ⟶ R.obj N)
    (Q : D) (q : L.obj M ⟶ Q) (r : Q ⟶ N)
    (hb : L'.map (β.app N) ≫ b.counit.app (H.obj N) =
      θ.hom.app (R.obj N) ≫ H.map (a.counit.app N))
    (hc : L.map δ ≫ a.counit.app N = q ≫ r) :
    (b.homEquiv A (H.obj N)).symm ((s ≫ G.map δ) ≫ β.app N) =
      L'.map s ≫ θ.hom.app M ≫ H.map q ≫ H.map r := by
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_counit, hb]
  simp only [Functor.map_comp, Category.assoc]
  have hn := θ.hom.naturality δ
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  rw [← H.map_comp, hc, H.map_comp]

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

private lemma baseChange_adjunct
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
      [IsFinitenessCoefficient ℓ Λ]
    (sq : CommSq g' f' f g) (N : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    (boundedConstructibleUpperStar Λ ℓ (f'.asOver (Spec (.of k)))).map
        ((boundedConstructibleBaseChange Λ ℓ (sq.asOver (Spec (.of k)))).app N) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ (f'.asOver (Spec (.of k)))).counit.app
        ((boundedConstructibleUpperStar Λ ℓ (g'.asOver (Spec (.of k)))).obj N) =
    (boundedConstructiblePullbackSquareComparison Λ ℓ (sq.asOver (Spec (.of k)))).hom.app
        ((boundedConstructibleLowerStar Λ ℓ (f.asOver (Spec (.of k)))).obj N) ≫
      (boundedConstructibleUpperStar Λ ℓ (g'.asOver (Spec (.of k)))).map
        ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ
          (f.asOver (Spec (.of k)))).counit.app N) := by
  exact boundedConstructibleBaseChange_adjunct Λ ℓ (sq.asOver (Spec (.of k))) N

private lemma bounded_counit_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
      [IsFinitenessCoefficient ℓ Λ]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ
      (f.asOver (Spec (.of k)))).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction Λ f).counit.app K.obj := by
  change (ProEtale.boundedConstructible (condensedRingObj Λ X)).ι.map
    ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ
      (f.asOver (Spec (.of k)))).counit.app K) = _
  rw [boundedConstructibleUpperStarLowerStarAdjunction,
    Adjunction.map_restrictFullyFaithful_counit_app]
  dsimp only [boundedConstructibleUpperStar, boundedConstructibleLowerStar,
    ObjectProperty.lift, Functor.comp_obj, ObjectProperty.ι_obj]
  simp [boundedConstructibleUpperStarCompatibility,
    boundedConstructibleLowerStarCompatibility, ObjectProperty.liftCompιIso,
    Iso.symm, Iso.refl, NatTrans.id_app]

private lemma integral_push_counit (K : integralConstructible ℓ E X) :
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
      (f.asOver (Spec (.of k)))).map
        (integralConstructiblePushHom ℓ E k f K) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) ℓ
        (f.asOver (Spec (.of k)))).counit.app
          ((integralScalarConstructible ℓ E X).obj K) =
    (integralConstructiblePullIso ℓ E k f
      ((boundedConstructibleLowerStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k)))).obj K)).inv ≫
      (integralScalarConstructible ℓ E X).map
        ((boundedConstructibleUpperStarLowerStarAdjunction (integralCoeff ℓ E) ℓ
          (f.asOver (Spec (.of k)))).counit.app K) := by
  let : IsCommMonObj (condensedRingObj (integralCoeff ℓ E) X) :=
    ProEtale.isCommMonObj_condensedRingObj _ X
  let : IsCommMonObj (condensedRingObj (integralCoeff ℓ E) Y) :=
    ProEtale.isCommMonObj_condensedRingObj _ Y
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [bounded_counit_hom (ℓ := ℓ) (k := k) (f := f)]
  simp only [integralScalarConstructible, integralConstructiblePushHom,
    integralConstructiblePullIso, boundedConstructibleUpperStar,
    ObjectProperty.lift_map, ObjectProperty.homMk_hom, ObjectProperty.isoMk_inv,
    Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_map, ObjectProperty.ι_obj]
  rw [bounded_counit_hom (ℓ := ℓ) (k := k) (f := f)]
  exact coefficient_counit
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (integralScalarMap ℓ E) X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (integralScalarMap ℓ E) Y))
    (derivedUpperStarLowerStarAdjunction (integralCoeff ℓ E) f)
    (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) f)
    (derivedComapLowerStarIso (integralScalarMap ℓ E) f) K.obj

/-- Normal form for the source side after the bounded f′ adjunction.
Source: Bhatt--Scholze, Remark 6.8.15; ChangeOfCoefficients.lean derived comparisons
and the specified unit-square-counit exchange construction.
(blueprint: lem-weil-pbc-continuous-integral-exchange-source-adjunct).

Proof. Apply the bounded f′ adjunction to the source composite. Expand functoriality, then
replace the exchange adjunct by square transport followed by the f counit. Naturality of the
square comparison moves the f push comparison past it. The iterated mate/conjugation identity
identifies pullback of that push comparison followed by the E counit with the inverse pull
comparison followed by scalar extension of the integral counit. These substitutions give exactly
the displayed composite. -/
theorem integralConstructible_exchange_source_adjunct
    (sq : CommSq g' f' f g) (K : integralConstructible ℓ E X) :
    ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) ℓ
      (f'.asOver (Spec (.of k)))).homEquiv _ _).symm
      (integralConstructibleSourceHom ℓ E k f g K ≫
        (boundedConstructibleBaseChange (Profinite.continuousMapRingObj E) ℓ
          (sq.asOver (Spec (.of k)))).app
          ((integralScalarConstructible ℓ E X).obj K)) =
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
      (f'.asOver (Spec (.of k)))).map
        (integralConstructiblePullHom ℓ E k g
          ((boundedConstructibleLowerStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k)))).obj K)) ≫
      (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ
        (sq.asOver (Spec (.of k)))).hom.app
          ((integralScalarConstructible ℓ E Y).obj
            ((boundedConstructibleLowerStar (integralCoeff ℓ E) ℓ
              (f.asOver (Spec (.of k)))).obj K)) ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
        (g'.asOver (Spec (.of k)))).map
        (integralConstructiblePullIso ℓ E k f
          ((boundedConstructibleLowerStar (integralCoeff ℓ E) ℓ
            (f.asOver (Spec (.of k)))).obj K)).inv ≫
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
        (g'.asOver (Spec (.of k)))).map
        ((integralScalarConstructible ℓ E X).map
          ((boundedConstructibleUpperStarLowerStarAdjunction (integralCoeff ℓ E) ℓ
            (f.asOver (Spec (.of k)))).counit.app K)) := by
  simpa only [integralConstructibleSourceHom] using source_normal_form
    (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) ℓ
      (f.asOver (Spec (.of k))))
    (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) ℓ
      (f'.asOver (Spec (.of k))))
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g.asOver (Spec (.of k))))
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of k))))
    (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ
      (sq.asOver (Spec (.of k))))
    (boundedConstructibleBaseChange (Profinite.continuousMapRingObj E) ℓ (sq.asOver (Spec (.of k))))
    ((integralScalarConstructible ℓ E X).obj K)
    ((integralScalarConstructible ℓ E Y).obj
      ((boundedConstructibleLowerStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k)))).obj K))
    ((integralScalarConstructible ℓ E Y').obj
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj
        ((boundedConstructibleLowerStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k)))).obj K)))
    (integralConstructiblePullHom ℓ E k g
      ((boundedConstructibleLowerStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k)))).obj K))
    (integralConstructiblePushHom ℓ E k f K)
    ((integralScalarConstructible ℓ E X).obj
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k)))).obj
        ((boundedConstructibleLowerStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k)))).obj K)))
    (integralConstructiblePullIso ℓ E k f
      ((boundedConstructibleLowerStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k)))).obj K)).inv
    ((integralScalarConstructible ℓ E X).map
      ((boundedConstructibleUpperStarLowerStarAdjunction (integralCoeff ℓ E) ℓ
        (f.asOver (Spec (.of k)))).counit.app K))
    (baseChange_adjunct ℓ k f g f' g' (Profinite.continuousMapRingObj E) sq _)
    (integral_push_counit ℓ E k f K)

end AlgebraicGeometry.ProEtale.CondensedRing
