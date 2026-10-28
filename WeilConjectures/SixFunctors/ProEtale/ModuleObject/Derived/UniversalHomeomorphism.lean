/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomologyCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.TopInvariance

/-!

# Derived pullback along universal homeomorphisms reflects isomorphisms

Let `Λ` be a commutative condensed ring and `r : X ⟶ Y` a universal homeomorphism of schemes. By
topological invariance of the small pro-étale topos, the pullback `r^*` of module objects over
`Λ` is an equivalence of categories
(`ProEtale.CondensedRing.isEquivalence_upperStar_of_isUniversalHomeomorphism`). Since the derived
pullback `L(r^*)` commutes with the homology functors and a morphism of the derived category is an
isomorphism as soon as it induces isomorphisms on all homology objects, the derived pullback
`L(r^*)` reflects isomorphisms
(`ProEtale.CondensedRing.isIso_of_isIso_leftDerivedUpperStar_map`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

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

/-- The derived pullback `L(r^*)` of module objects over `Λ` along a universal homeomorphism `r`
reflects isomorphisms: the homology of `L(r^*)(g)` is `r^*` applied to the homology of `g`, and
`r^*` is an equivalence. -/
theorem isIso_of_isIso_leftDerivedUpperStar_map {X Y : Scheme.{u}} (r : X ⟶ Y)
    [IsUniversalHomeomorphism r]
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))}
    (g : K ⟶ L) (h : IsIso (L((r)^*⟦Λ⟧).map g)) : IsIso g := by
  have := isEquivalence_upperStar_of_isUniversalHomeomorphism Λ r
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso ((r)^*⟦Λ⟧.map ((DerivedCategory.homologyFunctor _ n).map g)) :=
    (NatIso.isIso_map_iff (leftDerivedUpperStarHomologyIso Λ r n) g).2 (by
      rw [Functor.comp_map]
      infer_instance)
  exact isIso_of_reflects_iso _ (r)^*⟦Λ⟧

/-- The derived pullback along a universal homeomorphism reflects isomorphisms. -/
instance reflectsIsomorphisms_leftDerivedUpperStar {X Y : Scheme.{u}} (r : X ⟶ Y)
    [IsUniversalHomeomorphism r] : L((r)^*⟦Λ⟧).ReflectsIsomorphisms where
  reflects g h := isIso_of_isIso_leftDerivedUpperStar_map Λ r g h

end AlgebraicGeometry.ProEtale.CondensedRing
