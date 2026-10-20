/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.OverSquare

public import Sheaf.Paper.ContinuousIntegralComparisons
import Sheaf.Paper.ContinuousIntegralPushComparison
import Sheaf.Paper.ContinuousIntegralExchangeEquality

/-! # Scalar localization comparison for the specified proper exchange -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]


/-- Source and target comparisons identify the specified integral and E exchange maps.
Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15; scalar localization and
unit-square-counit compatibility in the condensed realization argument.
(blueprint: lem-weil-pbc-continuous-integral-exchange-square).

Proof in words. On compact profinite tests, continuousIntegralFunctions_isLocalization
identifies the coefficient map with inversion of ℓ. Exact inverse image from the point
preserves this localization. Thus scalar extension is exact and commutes with pullback.
For proper f and its base change f', ordinary derived pushforward commutes with the
localization telescope on bounded-below objects: apply qcqs pushforward continuity to
uniformly bounded-below representatives, all with the same lower bound. Compose the
pullback comparison with the pullback of the pushforward comparison to obtain s.
Compose the pushforward comparison with the pushforward of the pullback comparison
to obtain t. Both are invertible by the same continuity result. These comparisons are
mates of restriction-of-scalars comparisons. Hence they preserve units and counits,
and their pullback comparisons preserve coherent composition. Expanding the specified
exchange as unit insertion, square transport and counit contraction gives exactly the
displayed commuting square. Restriction along fully faithful constructible inclusions
preserves these identities. No invertibility of exchange itself enters this argument. -/
theorem continuousIntegral_exchange_square [IsProper f]
    (sq : IsPullback g' f' f g) (M : integralConstructible ℓ E X)
    (hM : ProEtale.boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X)
        ((integralScalarExtension ℓ E X).obj M.obj)) :
    let N : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X) :=
      ⟨(integralScalarExtension ℓ E X).obj M.obj, hM⟩
    ∃ (s : (integralScalarExtension ℓ E Y').obj
          (((boundedConstructibleLowerStar (integralCoeff ℓ E) ℓ (f.asOver (Spec (.of k))) ⋙
            boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj M).obj) ≅
        ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ (f.asOver (Spec (.of k))) ⋙
          boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g.asOver (Spec (.of k)))).obj N).obj)
      (t : (integralScalarExtension ℓ E Y').obj
          (((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k))) ⋙
            boundedConstructibleLowerStar (integralCoeff ℓ E) ℓ (f'.asOver (Spec (.of k)))).obj M).obj) ≅
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of k))) ⋙
          boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ (f'.asOver (Spec (.of k)))).obj N).obj),
      s.hom ≫ ((boundedConstructibleBaseChange (Profinite.continuousMapRingObj E) ℓ (sq.toCommSq.asOver (Spec (.of k)))).app N).hom =
        (integralScalarExtension ℓ E Y').map
          ((boundedConstructibleBaseChange (integralCoeff ℓ E) ℓ (sq.toCommSq.asOver (Spec (.of k)))).app M).hom ≫
            t.hom := by
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
  have hf : IsIso (integralConstructiblePushHom ℓ E k f M) := by
    let ι := (ProEtale.boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) Y)).ι
    have : IsIso (ι.map (integralConstructiblePushHom ℓ E k f M)) :=
      integralScalarPushHom_isIso ℓ E f M
    exact isIso_of_reflects_iso _ ι
  have hf' : IsIso (integralConstructiblePushHom ℓ E k f'
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k)))).obj M)) := by
    let ι := (ProEtale.boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) Y')).ι
    have : IsIso (ι.map (integralConstructiblePushHom ℓ E k f'
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k)))).obj M))) :=
      integralScalarPushHom_isIso ℓ E f'
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k)))).obj M)
    exact isIso_of_reflects_iso _ ι
  have : IsIso (integralConstructibleSourceHom ℓ E k f g M) := by
    unfold integralConstructibleSourceHom integralConstructiblePullHom
    infer_instance
  have : IsIso (integralConstructibleTargetHom ℓ E k f' g' M) := by
    unfold integralConstructibleTargetHom integralConstructiblePullHom
    infer_instance
  let ι := (ProEtale.boundedConstructible
    (condensedRingObj (Profinite.continuousMapRingObj E) Y')).ι
  refine ⟨ι.mapIso (asIso (integralConstructibleSourceHom ℓ E k f g M)),
    ι.mapIso (asIso (integralConstructibleTargetHom ℓ E k f' g' M)), ?_⟩
  exact congrArg (fun a ↦ a.hom)
    (integralConstructible_exchange_equality ℓ E k f g f' g' sq.toCommSq M)

end AlgebraicGeometry.ProEtale.CondensedRing
