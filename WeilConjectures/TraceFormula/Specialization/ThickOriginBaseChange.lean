/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Exchange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.TopInvariance

/-!

# Base change along universal homeomorphisms on module objects

Let `Λ` be a commutative condensed ring and `r : X ⟶ Y` a universal homeomorphism of schemes. By
topological invariance of the small pro-étale topos
(`ProEtale.isEquivalence_lowerStar_of_isUniversalHomeomorphism`), the pullback `r^*` of module
objects over `Λ` is an equivalence of categories
(`ProEtale.CondensedRing.isEquivalence_upperStar_of_isUniversalHomeomorphism`). Consequently, for a
cartesian square
```
X' --g'--> X
|          |
p'         p
v          v
Y' --g---> Y
```
whose horizontal maps are universal homeomorphisms, the derived base change map
`Lg^* Rp_* ⟶ Rp'_* Lg'^*` is an isomorphism
(`ProEtale.CondensedRing.isIso_baseChangeMap_of_isUniversalHomeomorphism`): the pullbacks are
exact equivalences, so they have exact left adjoints (their inverses), and the underived
exchange morphism is invertible.

For nearby cycles, a morphism of models whose square of geometric generic fibres is cartesian and
whose morphisms of total spaces and of geometric generic fibres are universal homeomorphisms has
an invertible pullback exchange
(`ProEtale.CondensedRing.NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isUniversalHomeomorphism`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Topological invariance for module objects**: the pullback `r^*` of module objects over `Λ`
along a universal homeomorphism `r` is an equivalence of categories. The lift of the adjunction
`r^* ⊣ r_*` of sheaves to module objects has invertible unit and counit, these being computed on
the underlying sheaves, and the extension of scalars along `α_r` is an equivalence. -/
theorem isEquivalence_upperStar_of_isUniversalHomeomorphism {X Y : Scheme.{u}} (r : X ⟶ Y)
    [IsUniversalHomeomorphism r] : (r)^*⟦Λ⟧.IsEquivalence := by
  have := ProEtale.isEquivalence_lowerStar_of_isUniversalHomeomorphism Ab.{u + 1} r
  have := ProEtale.isEquivalence_upperStar_of_isUniversalHomeomorphism Ab.{u + 1} r
  let adj₀ := ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} r
  have : IsIso adj₀.unit := adj₀.unit_isIso_of_L_fully_faithful
  have : IsIso adj₀.counit := adj₀.counit_isIso_of_R_fully_faithful
  let adj := adj₀.mapModAdjunction (condensedRingObj Λ Y)
  have : IsIso adj.unit := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M ↦ ?_
    have : IsIso ((Mod.forget _).map (adj.unit.app M)) := by
      rw [Mod.forget_map, Adjunction.mapModAdjunction_unit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have : IsIso adj.counit := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun N ↦ ?_
    have : IsIso ((Mod.forget _).map (adj.counit.app N)) := by
      rw [Mod.forget_map, Adjunction.mapModAdjunction_counit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have : ((r)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).IsEquivalence :=
    adj.toEquivalence.isEquivalence_functor
  unfold upperStar
  infer_instance

set_option maxHeartbeats 1000000 in
-- the instances of the general lemma are found for each of the categories of module objects
/-- **Base change along universal homeomorphisms on the ambient derived categories**: for a
cartesian square `g' ≫ p = p' ≫ g` of schemes with `g` a universal homeomorphism, the base change
map `Lg^* Rp_* ⟶ Rp'_* Lg'^*` of module objects over `Λ` is an isomorphism, for every morphism `p`
and on all complexes. The pullbacks along `g` and `g'` are equivalences, so they have exact left
adjoints, and the underived exchange morphism is invertible. -/
theorem isIso_baseChangeMap_of_isUniversalHomeomorphism {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y}
    {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' p' p g)
    [IsUniversalHomeomorphism g] : IsIso (baseChangeMap Λ sq.toCommSq) := by
  have : IsUniversalHomeomorphism g' := MorphismProperty.of_isPullback sq.flip inferInstance
  have := isEquivalence_upperStar_of_isUniversalHomeomorphism Λ g
  have := isEquivalence_upperStar_of_isUniversalHomeomorphism Λ g'
  have : IsIso (Adjunction.exchangeRight (upperStarLowerStarAdjunction Λ p)
      (upperStarLowerStarAdjunction Λ p') (upperStarSquareComparison Λ sq.toCommSq)) :=
    Adjunction.isIso_exchangeRight_of_isEquivalence _ _ _
  let a : (g)^*⟦Λ⟧.inv ⊣ (g)^*⟦Λ⟧ := (g)^*⟦Λ⟧.asEquivalence.symm.toAdjunction
  let a' : (g')^*⟦Λ⟧.inv ⊣ (g')^*⟦Λ⟧ := (g')^*⟦Λ⟧.asEquivalence.symm.toAdjunction
  rw [baseChangeMap, pullbackSquareComparison_eq_leftDerivedFunctorSquareIso]
  exact Adjunction.isIso_exchangeRight_derivedAdjunction_leftDerivedFunctorSquareIso_of_leftAdjoint
    (upperStarLowerStarAdjunction Λ p) (upperStarLowerStarAdjunction Λ p')
    a a' (upperStarSquareComparison Λ sq.toCommSq)

namespace NearbyCyclesModel.Hom

variable {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')

/-- If the square of geometric generic fibres of a morphism of models is cartesian and its
morphism of total spaces is a universal homeomorphism, the pullback exchange
`α : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` is an isomorphism: the base change morphism of the square of geometric
generic fibres is invertible by `isIso_baseChangeMap_of_isUniversalHomeomorphism`. -/
lemma isIso_pullbackExchange_of_isUniversalHomeomorphism
    (hφ : IsPullback φ.generic M.j N.j φ.total) [IsUniversalHomeomorphism φ.total] :
    IsIso (φ.pullbackExchange Λ) := by
  have : IsIso (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j).hom).natTrans := by
    have := isIso_baseChangeMap_of_isUniversalHomeomorphism Λ hφ
    rwa [baseChangeMap, Adjunction.exchangeRight_eq_mateEquiv] at this
  unfold pullbackExchange
  infer_instance

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
