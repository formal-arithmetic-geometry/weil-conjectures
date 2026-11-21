/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekCompositionIntegral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriek
public import WeilConjectures.TraceFormula.CompactPullback

/-!

# Frobenius operators with `𝒪_E`-coefficients

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`. This file defines, for
bounded constructible `𝒪_E`-complexes, the operators of a Frobenius correspondence, as
`ProEtale.CondensedRing.frobeniusCompactOperator` does for `ℚ̄_ℓ`-coefficients:

* the pullback `h^♯ : RΓ_c(X, K) ⟶ RΓ_c(Y, Lh^* K)` on compactly supported cohomology along a
  proper morphism `h : Y ⟶ X` (`ProEtale.CondensedRing.PadicIntegersRingObj.compactPullback`),
  the composite of the unit of `Lh^* ⊣ Rh_*`, the identification `Rh_! ≅ Rh_*` and the composition
  isomorphism of the lower shriek;
* for an endomorphism `Φ` and an arbitrary morphism `θ : LΦ^* K ⟶ K`, the operator
  `T_{c_m}(θ_m) = RΓ_c(X, θ_m) ∘ Φ_m^♯` on `RΓ_c(X, K)`
  (`ProEtale.CondensedRing.PadicIntegersRingObj.frobeniusCompactOperator`);
* the stalk map `v_x : K_x ⟶ K_x` of a map `v : Lh^* K ⟶ K` at a rational point `x` fixed by
  `h` (`ProEtale.CondensedRing.PadicIntegersRingObj.graphStalkMap`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The composition isomorphism `Rh_! ⋙ Ra_{X!} ≅ R(h ≫ a_X)_! = Ra_{Y!}` of the lower shriek on
bounded constructible `𝒪_E`-complexes, along `h : Y ⟶ X` and the structure morphism of `X`. -/
noncomputable def boundedConstructibleLowerShriekCompToPoint (h : Y ⟶ X) :
    boundedConstructibleLowerShriek ℓ E h ⋙ boundedConstructibleLowerShriek ℓ E (toPoint X) ≅
      boundedConstructibleLowerShriek ℓ E (toPoint Y) :=
  (boundedConstructibleLowerShriekComp_padicIntegers ℓ E h (toPoint X)).symm ≪≫
    eqToIso (by rw [comp_toPoint])

/-- The *pullback on compactly supported cohomology* `h^♯ : RΓ_c(X, -) ⟶ RΓ_c(Y, Lh^* -)` with
`𝒪_E`-coefficients, along a proper morphism `h : Y ⟶ X`: the composite
```
Ra_{X!} K ⟶ Ra_{X!} Rh_* Lh^* K ≅ Ra_{X!} Rh_! Lh^* K ≅ R(h ≫ a_X)_! Lh^* K = Ra_{Y!} Lh^* K
```
of the unit of `Lh^* ⊣ Rh_*`, the identification `Rh_! ≅ Rh_*` and the composition isomorphism
of the lower shriek. -/
noncomputable def compactPullback (h : Y ⟶ X) [IsProper h.left] :
    boundedConstructibleLowerShriek ℓ E (toPoint X) ⟶
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ h ⋙
        boundedConstructibleLowerShriek ℓ E (toPoint Y) :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ E h).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (Functor.whiskerRight
      (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E h).inv _) ≫
    Functor.whiskerLeft _ (boundedConstructibleLowerShriekCompToPoint ℓ E h).hom

variable {ℓ E}

/-- The *operator in degree `m`* `T_{c_m}(θ_m)` of a Frobenius correspondence
`θ : LΦ^* K ⟶ K` with `𝒪_E`-coefficients, for a proper endomorphism `Φ`:
```
RΓ_c(X, K) --Φ_m^♯--> RΓ_c(X, LΦ_m^* K) --RΓ_c(X, θ_m)--> RΓ_c(X, K).
```
-/
noncomputable def frobeniusCompactOperator {Φ : X ⟶ X} [IsProper Φ.left]
    {K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧}
    (θ : (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ Φ).obj K ⟶ K)
    (m : ℕ) :
    (boundedConstructibleLowerShriek ℓ E (toPoint X)).obj K ⟶
      (boundedConstructibleLowerShriek ℓ E (toPoint X)).obj K :=
  (compactPullback ℓ E (frobeniusIterate Φ m)).app K ≫
    (boundedConstructibleLowerShriek ℓ E (toPoint X)).map (frobeniusCoefficientIterate θ m)

/-- The *stalk map* `v_x : K_x ≅ (Lh^* K)_x ⟶ K_x` of a map `v : Lh^* K ⟶ K` of bounded
constructible `𝒪_E`-complexes at a rational point `x` fixed by `h`, through
`Lx^* Lh^* ≅ L(x ≫ h)^* = Lx^*`. -/
noncomputable def graphStalkMap (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧)
    (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ h).obj K ⟶ K)
    (x : RationalPoint X) (hx : x ≫ h = x) :
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ x).obj K ⟶
      (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ x).obj K :=
  eqToHom (by rw [hx]) ≫
    (boundedConstructibleUpperStarComp (Profinite.padicIntegersRingObj ℓ E) ℓ x h).hom.app K ≫
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ x).map v

end AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj
