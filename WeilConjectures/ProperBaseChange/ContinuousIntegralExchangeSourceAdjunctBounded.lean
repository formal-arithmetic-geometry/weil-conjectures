/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralComparisons
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ChangeOfCoefficients
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Coherence of integral localization and the specified exchange map: bounded counits

The bounded constructible counit identifications used by
`Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct` (split from it for compile time). -/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

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

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
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

/-- `E̲` with the topology and ring structure of the normed field `F`, the coefficient ring of
`integralScalarConstructible`. -/
private noncomputable abbrev normedRing (F : Type) [NormedField F] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  Profinite.continuousMapRingObj.{u} F

section BaseChangeCalculation
-- Match the restricted functors without unfolding their derived implementations.
attribute [local irreducible] boundedConstructibleUpperStar
  ContinuousMapRingObj.boundedConstructibleLowerStar
  ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction
  boundedConstructiblePullbackSquareComparison

end BaseChangeCalculation

/-- The counit of the restriction of `Lf^* ⊣ Rf_*` to bounded constructible complexes, along a
proof `hf` that `Rf_*` preserves them, is the derived counit. -/
private lemma restricted_counit_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {T U : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (h : T ⟶ U)
    (hf : ∀ K : Dᵇc(T.left)⟦Λ⟧,
      boundedConstructible (condensedRingObj Λ U.left) ((R((h.left)_*⟦Λ⟧)).obj K.obj))
    (K : Dᵇc(T.left)⟦Λ⟧) :
    ((Adjunction.restrictFullyFaithful (derivedUpperStarLowerStarAdjunction Λ h.left)
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (boundedConstructibleUpperStarCompatibility Λ ℓ h).symm
      (ObjectProperty.liftCompιIso _ _ hf).symm).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction Λ h.left).counit.app K.obj := by
  refine (Adjunction.map_restrictFullyFaithful_counit_app
    (derivedUpperStarLowerStarAdjunction Λ h.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ h).symm
    (ObjectProperty.liftCompιIso _ _ hf).symm K).trans ?_
  simp [boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso]
  exact Category.id_comp _

/-- The `O̲`-coefficient adjunction `Lf^* ⊣ Rf_*` is the restricted derived adjunction. -/
private lemma unitBall_adjunction_eq {T U : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (h : T ⟶ U) :
    UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E)
        h =
      Adjunction.restrictFullyFaithful
        (derivedUpperStarLowerStarAdjunction (integralCoeff ℓ E) h.left)
        (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
        (boundedConstructibleUpperStarCompatibility (integralCoeff ℓ E) ℓ h).symm
        (ObjectProperty.liftCompιIso _ _
          (UnitBallRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ
            (continuousIntegers ℓ E) h)).symm :=
  rfl

/-- The `E̲`-coefficient adjunction `Lf^* ⊣ Rf_*` is the restricted derived adjunction. -/
private lemma continuousMap_adjunction_eq {T U : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (h : T ⟶ U) :
    ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E h =
      Adjunction.restrictFullyFaithful
        (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) h.left)
        (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
        (boundedConstructibleUpperStarCompatibility (Profinite.continuousMapRingObj E) ℓ h).symm
        (ObjectProperty.liftCompιIso _ _
          (ContinuousMapRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E h)).symm :=
  rfl

private lemma bounded_counit_hom_unitBall
    (K : ProEtale.BoundedConstructible (condensedRingObj (integralCoeff ℓ E) X)) :
    ((UnitBallRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ (continuousIntegers ℓ E)
      (f.asOver (Spec (.of k)))).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction (integralCoeff ℓ E) f).counit.app K.obj :=
  (congrArg (fun a ↦ (a.counit.app K).hom)
    (unitBall_adjunction_eq ℓ E k (f.asOver (Spec (.of k))))).trans
    (restricted_counit_hom ℓ k _ (f.asOver (Spec (.of k))) _ K)

private lemma bounded_counit_hom_continuousMap
    (K : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) :
    ((ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
      (f.asOver (Spec (.of k)))).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction (normedRing E) f).counit.app K.obj :=
  (congrArg (fun a ↦ (a.counit.app K).hom)
    (continuousMap_adjunction_eq ℓ E k (f.asOver (Spec (.of k))))).trans
    (restricted_counit_hom ℓ k _ (f.asOver (Spec (.of k))) _ K)

private lemma upperStar_map_hom {T U : Scheme.{u}} [T.Over (Spec (.of k))]
    [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    {A B : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) U)} (φ : A ⟶ B) :
    ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
      (h.asOver (Spec (.of k)))).map φ).hom = (L((h)^*⟦normedRing E⟧)).map φ.hom :=
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
