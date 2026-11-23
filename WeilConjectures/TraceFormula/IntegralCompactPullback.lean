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

# Frobenius operators with integral coefficients

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`. This file defines, for
bounded constructible `𝒪_E`-complexes, the operators of Frobenius correspondences that
`WeilConjectures.TraceFormula.CompactPullback` defines for `ℚ̄_ℓ`-coefficients:

* the pullback `h^♯ : RΓ_c(X, K) ⟶ RΓ_c(Y, Lh^* K)` on compactly supported cohomology along a
  proper morphism `h : Y ⟶ X` (`ProEtale.CondensedRing.PadicIntegersRingObj.compactPullback`);
* the global operator `T_{c_m}(θ_m) = RΓ_c(X, θ_m) ∘ Φ_m^♯` of an integral Frobenius
  correspondence `θ : LΦ^* K ⟶ K` for a proper `Φ`
  (`ProEtale.CondensedRing.PadicIntegersRingObj.frobeniusCompactOperator`);
* the stalk map `θ_x : K_x ⟶ K_x` at a rational point fixed by an endomorphism
  (`ProEtale.CondensedRing.PadicIntegersRingObj.graphStalkMap`).

The definitions are the same as for `ℚ̄_ℓ`, with the integral lower shriek
`ProEtale.CondensedRing.PadicIntegersRingObj.boundedConstructibleLowerShriek`, its composition
isomorphisms `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicIntegers` and the
identification `ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicIntegers`
of `Rh_!` with `Rh_*` for a proper `h`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The composition isomorphism `Rh_! ⋙ Ra_{X!} ≅ R(h ≫ a_X)_! = Ra_{Y!}` of the integral lower
shriek along `h : Y ⟶ X` and the structure morphism of `X`. -/
noncomputable def boundedConstructibleLowerShriekCompToPoint (h : Y ⟶ X) :
    boundedConstructibleLowerShriek ℓ E h ⋙ boundedConstructibleLowerShriek ℓ E (toPoint X) ≅
      boundedConstructibleLowerShriek ℓ E (toPoint Y) :=
  (boundedConstructibleLowerShriekComp_padicIntegers ℓ E h (toPoint X)).symm ≪≫
    eqToIso (by rw [comp_toPoint])

/-- The *pullback on compactly supported cohomology* `h^♯ : RΓ_c(X, -) ⟶ RΓ_c(Y, Lh^* -)` with
`𝒪_E`-coefficients along a proper morphism `h : Y ⟶ X`: the composite
```
Ra_{X!} K ⟶ Ra_{X!} Rh_* Lh^* K ≅ Ra_{X!} Rh_! Lh^* K ≅ R(h ≫ a_X)_! Lh^* K = Ra_{Y!} Lh^* K
```
of the unit of `Lh^* ⊣ Rh_*`, the identification `Rh_! ≅ Rh_*` and the composition isomorphism
of the lower shriek, as for `ℚ̄_ℓ` (`ProEtale.CondensedRing.compactPullback`). -/
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

lemma compactPullback_app (h : Y ⟶ X) [IsProper h.left]
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (compactPullback ℓ E h).app K =
      (boundedConstructibleLowerShriek ℓ E (toPoint X)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ E h).unit.app K) ≫
        (boundedConstructibleLowerShriek ℓ E (toPoint X)).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E h).inv.app _) ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ E h).hom.app _ := by
  simp only [compactPullback, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.id_comp]

variable {ℓ E} {Φ : X ⟶ X} {K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧}

variable (ℓ E) in
/-- The *global operator in degree `m`* `T_{c_m}(θ_m) = RΓ_c(X, θ_m) ∘ Φ_m^♯` of an integral
Frobenius correspondence `θ : LΦ^* K ⟶ K` for a proper `Φ`:
```
RΓ_c(X, K) --Φ_m^♯--> RΓ_c(X, LΦ_m^* K) --RΓ_c(X, θ_m)--> RΓ_c(X, K),
```
with `θ_m` the iterates `ProEtale.CondensedRing.frobeniusCoefficientIterate`. This is the
`𝒪_E`-coefficient version of `ProEtale.CondensedRing.frobeniusCompactOperator`. -/
noncomputable def frobeniusCompactOperator [IsProper Φ.left]
    (θ : (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ Φ).obj K ⟶ K)
    (m : ℕ) :
    (boundedConstructibleLowerShriek ℓ E (toPoint X)).obj K ⟶
      (boundedConstructibleLowerShriek ℓ E (toPoint X)).obj K :=
  (compactPullback ℓ E (frobeniusIterate Φ m)).app K ≫
    (boundedConstructibleLowerShriek ℓ E (toPoint X)).map (frobeniusCoefficientIterate θ m)

variable (K) in
/-- The *stalk map* `v_x : K_x ⟶ K_x` of an integral coefficient map `v : Lh^* K ⟶ K` at a
rational point `x` fixed by the endomorphism `h`:
```
K_x = L(x ≫ h)^* K ≅ Lx^* Lh^* K --Lx^* v--> Lx^* K = K_x.
```
This is the `𝒪_E`-coefficient version of `ProEtale.CondensedRing.Correspondence.graphStalkMap`;
for `h = Φ_m` and `v = θ_m` it is the stalk map `θ_{m, x}`. -/
noncomputable def graphStalkMap (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ h).obj K ⟶ K)
    (x : RationalPoint X) (hx : x ≫ h = x) :
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ x).obj K ⟶
      (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ x).obj K :=
  eqToHom (by rw [hx]) ≫
    (boundedConstructibleUpperStarComp (Profinite.padicIntegersRingObj ℓ E) ℓ x h).hom.app K ≫
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ x).map v

end AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj
