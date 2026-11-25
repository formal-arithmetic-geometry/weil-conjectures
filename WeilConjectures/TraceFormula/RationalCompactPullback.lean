/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
public import WeilConjectures.TraceFormula.CompactPullback
public import WeilConjectures.TraceFormula.IntegersToPadicAlgClLowerShriek
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition

/-!
# Frobenius operators with coefficients in a finite extension of `ℚ_ℓ`

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ`. This file defines, for bounded constructible
`E`-complexes, the operators of Frobenius correspondences that
`WeilConjectures.TraceFormula.IntegralCompactPullback` defines for `𝒪_E`-coefficients:

* the isomorphism `Rh_! ≅ Rh_*` for a proper `h`
  (`ProEtale.CondensedRing.ContinuousMapRingObj.boundedConstructibleLowerShriekIsoLowerStar`);
* the pullback `h^♯ : RΓ_c(X, K) ⟶ RΓ_c(Y, Lh^* K)` on compactly supported cohomology along a
  proper morphism `h : Y ⟶ X` (`ProEtale.CondensedRing.ContinuousMapRingObj.compactPullback`);
* the global operator `T_{c_m}(ψ_m) = RΓ_c(X, ψ_m) ∘ Φ_m^♯` of a Frobenius correspondence
  `ψ : LΦ^* K ⟶ K` for a proper `Φ`
  (`ProEtale.CondensedRing.ContinuousMapRingObj.frobeniusCompactOperator`).

It also identifies `Rh_! ≅ Rh_*` and the composition isomorphisms of `Rf_!` with those of the
pushforward datum of `E`, through which they are compared with the `𝒪_E`-versions
(`ContinuousMapRingObj.boundedConstructibleLowerShriekIsoLowerStar_eq_pushforwardData`,
`boundedConstructibleLowerShriekComp_eq_pushforwardData`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : FiniteIntermediateField ℓ)
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

-- The coefficient ring `E`.
set_option quotPrecheck false in
local notation "𝔼" => Profinite.continuousMapRingObj E.1

variable {K : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X.left)}

variable (k) in
/-- The composition isomorphism of `Rf_!` on bounded constructible `E`-complexes is the one of
the pushforward datum of `E`. -/
lemma boundedConstructibleLowerShriekComp_eq_pushforwardData {S : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom] (f : X ⟶ Y)
    (g : Y ⟶ S) :
    haveI := isIso_continuousMapPushforwardData_lowerStarOpenImmersionLowerShriekExchange ℓ E k
      (Compactification.exists_isPullback_overG_overI (compactificationOverField f)
        (compactificationOverField g)).choose_spec
    boundedConstructibleLowerShriekComp ℓ E f g =
      BoundedConstructiblePushforwardData.lowerShriekCompOfCompactifications
        (isIsoRefinementPushforward_continuousMapPushforwardData ℓ k E) _ _ _
        (Compactification.exists_isPullback_overG_overI (compactificationOverField f)
          (compactificationOverField g)).choose_spec := by
  unfold boundedConstructibleLowerShriekComp
    BoundedConstructiblePushforwardData.lowerShriekCompOfCompactifications
  rfl

namespace ContinuousMapRingObj

/-- The isomorphism `Rh_! ≅ Rh_*` on bounded constructible `E`-sheaves for a proper `h`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekIsoLowerStar (h : Y ⟶ X) [IsProper h.left] :
    boundedConstructibleLowerShriek ℓ E h ≅ boundedConstructibleLowerStar ℓ E h :=
  boundedConstructibleLowerShriekOfCompactificationIso ℓ E (compactificationOverField h)
      (.ofIsProper h.left) ≪≫
    (Functor.isoWhiskerRight (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso 𝔼 ℓ h) _ ≪≫
      Functor.leftUnitor _)

variable (k) in
/-- The isomorphism `Rh_! ≅ Rh_*` on bounded constructible `E`-sheaves for a proper `h` is the one
of the pushforward datum of `E`. -/
lemma boundedConstructibleLowerShriekIsoLowerStar_eq_pushforwardData (h : Y ⟶ X)
    [IsProper h.left] :
    boundedConstructibleLowerShriekIsoLowerStar ℓ E h =
      BoundedConstructiblePushforwardData.lowerShriekIsoLowerStar
        (isIsoRefinementPushforward_continuousMapPushforwardData ℓ k E) h := by
  unfold boundedConstructibleLowerShriekIsoLowerStar
  rfl

/-- The *pullback on compactly supported cohomology* `h^♯ : RΓ_c(X, -) ⟶ RΓ_c(Y, Lh^* -)`
along a proper morphism `h : Y ⟶ X`, for `E`-coefficients: the composite
```
Ra_{X!} K ⟶ Ra_{X!} Rh_* Lh^* K ≅ Ra_{X!} Rh_! Lh^* K ≅ R(h ≫ a_X)_! Lh^* K = Ra_{Y!} Lh^* K.
```
-/
noncomputable def compactPullback (h : Y ⟶ X) [IsProper h.left] :
    boundedConstructibleLowerShriek ℓ E (toPoint X) ⟶
      boundedConstructibleUpperStar 𝔼 ℓ h ⋙ boundedConstructibleLowerShriek ℓ E (toPoint Y) :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ E h).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (Functor.whiskerRight
      (boundedConstructibleLowerShriekIsoLowerStar ℓ E h).inv _) ≫
    Functor.whiskerLeft _ ((boundedConstructibleLowerShriekComp ℓ E h (toPoint X)).inv ≫
      eqToHom (by rw [comp_toPoint]))

variable {ℓ E}

/-- The global operator `T_{c_m}(ψ_m) = RΓ_c(X, ψ_m) ∘ Φ_m^♯` on `RΓ_c(X, K)` of a Frobenius
correspondence `ψ : LΦ^* K ⟶ K` with `E`-coefficients. -/
noncomputable def frobeniusCompactOperator {Φ : X ⟶ X} [IsProper Φ.left]
    (ψ : (boundedConstructibleUpperStar 𝔼 ℓ Φ).obj K ⟶ K) (m : ℕ) :
    (boundedConstructibleLowerShriek ℓ E (toPoint X)).obj K ⟶
      (boundedConstructibleLowerShriek ℓ E (toPoint X)).obj K :=
  (compactPullback ℓ E (frobeniusIterate Φ m)).app K ≫
    (boundedConstructibleLowerShriek ℓ E (toPoint X)).map (frobeniusCoefficientIterate ψ m)

end ContinuousMapRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
