/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.ProfinitePointPullback

/-!
# Vanishing of extension by zero on a disjoint inverse image

Source: Stacks Project, Tags 09AG and 09AH. Disjoint inverse images are empty;
use the two adjunctions and then exactness on homology.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option backward.isDefEq.respectTransparency false in
private theorem openRestrictionPushforwardZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    IsZero ((upperStar Λ j).obj ((lowerStar Λ i).obj M)) := by
  have hdisjoint : Set.range i.base ∩ Set.range j.base = ∅ := by
    exact Set.disjoint_iff_inter_eq_empty.mp hij
  have hz : IsZero ((ProEtale.openImmersionRestriction Ab.{u + 1} j).obj
      ((ProEtale.lowerStar Ab.{u + 1} i).obj M.X)) := by
    refine Sheaf.isZero_of_isZero_obj _ ?_
    rintro ⟨T⟩
    let V := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j)).obj T)
    have hempty : IsEmpty V.left := by
      refine ⟨fun z ↦ ?_⟩
      have hz : (pullback.fst (T.hom ≫ j) i ≫ T.hom ≫ j).base z ∈
          Set.range i.base ∩ Set.range j.base := by
        refine ⟨?_, ⟨T.hom.base (pullback.fst (T.hom ≫ j) i z), ?_⟩⟩
        · rw [pullback.condition]
          exact ⟨_, rfl⟩
        · rfl
      rw [hdisjoint] at hz
      exact hz
    exact (isZero_zero Ab.{u + 1}).of_iso
      ((Scheme.ProEt.isTerminalSectionsOfIsEmpty M.X V).uniqueUpToIso
        HasZeroObject.zeroIsTerminal)
  have hz' : IsZero ((ProEtale.upperStar Ab.{u + 1} j).obj
      ((ProEtale.lowerStar Ab.{u + 1} i).obj M.X)) :=
    hz.of_iso ((ProEtale.upperStarIsoOpenImmersionRestriction Ab.{u + 1} j).app _)
  have hz'' := hz'.of_iso ((profinitePointModuleForgetPullbackIso Λ j).app
    ((lowerStar Λ i).obj M))
  apply (IsZero.iff_id_eq_zero _).2
  apply (Mod.forget (condensedRingObj Λ U)).map_injective
  exact hz''.eq_of_src _ _

/-- Restriction of an extended module complex along a disjoint morphism vanishes.
Source: Stacks Project, Tags 09AG and 09AH.
(blueprint: lem-sfb-module-disjoint-open-extension)

Proof: the open restriction of the direct image along the disjoint morphism
vanishes, since each section is evaluated on an empty fibre product. The coefficient
pullback isomorphism transports this calculation to module objects. The adjunctions
`g^* ⊣ g_*` and `j! ⊣ j^*` then identify endomorphisms of `g^* j! M` with maps
into zero, proving that object zero. All functors on the left are exact, so their
derived composites commute with every homology object and hence vanish on every
complex. The argument includes empty schemes and the zero complex. -/
theorem isZero_module_derived_pullback_openExtension_of_disjoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (g : Z ⟶ X)
    (hd : Disjoint (Set.range g.base) (Set.range j.base))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))) :
    IsZero ((upperStar Λ g).leftDerivedFunctor.obj
      ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K)) := by
  have hz (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
      IsZero ((upperStar Λ g).obj ((openImmersionLowerShriek Λ j).obj M)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply ((upperStarLowerStarAdjunction Λ g).homEquiv _ _).injective
    apply ((openImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv _ _).injective
    exact (openRestrictionPushforwardZero Λ g j hd _).eq_of_tgt _ _
  apply IsZero.of_iso ?_ ((leftDerivedUpperStarIsoMapDerivedCategory Λ g).app _)
  apply (DerivedCategory.isZero_iff _).2
  intro n
  exact (hz _).of_iso
    (((upperStar Λ g).mapDerivedCategoryHomologyFunctorIso n).symm.app _ ≪≫
      (upperStar Λ g).mapIso
        (((openImmersionLowerShriek Λ j).mapDerivedCategoryHomologyFunctorIso n).symm.app K))

end AlgebraicGeometry.ProEtale.CondensedRing
