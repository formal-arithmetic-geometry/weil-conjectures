/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AdicSites.Morphism.CompletionMateComparison
import all WeilConjectures.CategoryTheory.AdicSites.CompletionFiniteReductionSupplement

/-! # Reduction inverts the completion unit

Source: Stacks 099M, 091N; the reduction step of fix-lem-exchanges Step 5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.AdicSites

private theorem finiteRestriction_complete (S : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) [IsNoetherianRing A] (n : ℕ)
    (M : S.derived (quotientRing A I n)) :
    S.IsComplete A I ((S.finiteRestriction A I n).obj M) := by
  let R := S.ring A
  let B := S.ring (quotientRing A I n)
  let φ := ConstantCompletion.quotient S.topology A I n
  let : HasDerivedCategory.{u + 1} (ConstantCompletion.Mod R) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} (ConstantCompletion.Mod B) :=
    HasDerivedCategory.standard _
  let : ∀ U : S.objects, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((siteModuleRings R).over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let : ∀ U : S.objects, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((siteModuleRings B).over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let P := DerivedCategory.Q.objPreimage M
  let L := (ConstantCompletion.Q R).obj
    (((ConstantCompletion.res φ).mapHomologicalComplex (.up ℤ)).obj P)
  have hL : S.IsComplete A I L := by
    apply (ConstantCompletion.complete_iff_constantElements S.topology A I L).mpr
    intro a ha U
    apply (restrictScalars_completeElement_iff S.topology R B φ M U _).mpr
    apply completeElement_nilpotent S.topology B M U _ (n + 1)
    rw [← map_pow]
    apply RingHom.mem_ker.mp
    rw [(ConstantCompletion.flat_and_quotients S.topology A I).2.2 n U |>.2]
    apply Ideal.subset_span
    refine ⟨⟨a ^ (n + 1), Ideal.pow_mem_pow ha (n + 1)⟩, ?_⟩
    simp only [ConstantCompletion.constantSection, map_pow]
  let e : L ≅ (S.finiteRestriction A I n).obj M :=
    (ConstantCompletion.resFactors φ).app P ≪≫
      (ConstantCompletion.dres φ).mapIso (DerivedCategory.Q.objObjPreimageIso M)
  exact complete_iso S A I e hL

private theorem finiteReduction_unit_isIso (S : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) [IsNoetherianRing A]
    (N : S.derived A) (n : ℕ) :
    IsIso ((S.finiteReduction A I n).map ((S.unit A I).app N)) := by
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  obtain ⟨_, _, _, hh, _⟩ :=
    ConstantCompletion.koszul_quotient_reflector S.topology A I false r a ha
  apply isIso_of_coyoneda_map_bijective
  intro M
  have hbij := hh N ((S.finiteRestriction A I n).obj M)
    (finiteRestriction_complete S A I n M)
  let adj := S.finiteAdjunction A I n
  constructor
  · intro x y hxy
    apply (adj.homEquiv _ _).injective
    apply hbij.injective
    change (S.unit A I).app N ≫ (adj.homEquiv _ _) x =
      (S.unit A I).app N ≫ (adj.homEquiv _ _) y
    rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left]
    exact congrArg (adj.homEquiv _ _) hxy
  · intro y
    obtain ⟨x, hx⟩ := hbij.surjective ((adj.homEquiv _ _).toFun y)
    refine ⟨(adj.homEquiv _ _).symm x, ?_⟩
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
    exact hx

/-- Reduction of the specified quotient-completion unit is invertible on every object.
Source: Stacks 099M and 091N; fix-lem-exchanges Step 5, reduced unit.
(blueprint: lem-sf-cbc-small-site-reduced-unit)

Proof: complexes over each quotient are complete because ideal elements act nilpotently.
The completion reflector and finite scalar-extension adjunction therefore make finite
reduction of the unit invertible. Strict-tower cohomology is levelwise, so these finite
isomorphisms make reduction of the unit invertible before evaluation. -/
theorem reductionCompletionUnit_isIso (S : Site.{u}) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    IsIso (Functor.whiskerRight (S.unit A I) (S.reduction A I)) := by
  let (N : S.derived A) : IsIso
      ((Functor.whiskerRight (S.unit A I) (S.reduction A I)).app N) := by
    change IsIso ((S.reduction A I).map ((S.unit A I).app N))
    rw [DerivedCategory.isIso_iff]
    intro i
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro n
    let E := S.evaluateModule A n.unop
    have hf := finiteReduction_unit_isIso S A I N n.unop
    have he : IsIso ((S.evaluate A n.unop).map
        ((S.reduction A I).map ((S.unit A I).app N))) :=
      (NatIso.isIso_map_iff (S.finiteEvaluationIso A I n.unop)
        ((S.unit A I).app N)).mpr (by dsimp only [Functor.comp_map]; infer_instance)
    exact (NatIso.isIso_map_iff (E.mapDerivedCategoryHomologyFunctorIso i)
      ((S.reduction A I).map ((S.unit A I).app N))).mpr
        (by dsimp only [Functor.comp_map]; infer_instance)
  exact NatIso.isIso_of_isIso_app _

end CategoryTheory.AdicSites
