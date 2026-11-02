/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerIntrinsicTransitions
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerGenericTransitions

/-! # Strict transitions in intrinsic coefficient coordinates

Source: Zheng, Construction 4.1; Stacks 07A6; the first step of the
coefficient-tower transition compatibility argument.
-/

@[expose] public noncomputable section
-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

section ExactLocalization

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]

-- The supplied comparison on a complex, with its terminal evaluation factor exposed.
end ExactLocalization

private theorem genericCoefficientMap_system (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n) :
    SemilinearSections.coefficientMap (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h =
      (spCoefficientCommRings l E T).map (homOfLE h).op := by
  let t : SemilinearSections.rings (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) ⟶
      spCoefficientCommRings l E T :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [SemilinearSections.rings, Functor.ofOpSequence_map_homOfLE_succ,
        Category.comp_id, Category.id_comp]
      rfl)
  exact (Category.comp_id _).symm.trans
    ((t.naturality (homOfLE h).op).trans (Category.id_comp _))

private theorem hom_function_heq {R : Type*} [Ring R]
    {M M' N N' : ModuleCat R} (hM : M = M') (hN : N = N')
    {f : M ⟶ N} {g : M' ⟶ N'} (hfg : HEq f g) :
    HEq (fun x ↦ f x) (fun x ↦ g x) := by
  cases hM
  cases hN
  cases hfg
  rfl

-- Match the horizontal coefficient maps before using the heterogeneous module equalities.
set_option maxHeartbeats 4000000 in
-- Unfolding the coefficient presentations requires a larger elaboration budget.
private theorem transition_functions (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (a : SpCoefficientTowersAbelian l E T)
    (M : spCoefficientTowers l E T) {m n : ℕ} (h : m ≤ n) (U : T.ProEtᵒᵖ) :
    HEq (fun x ↦ ((SemilinearSections.transition (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).app
          ((b.realization T).functor.obj M)).val.app U x)
      (fun x ↦ ((a.equivalence.functor.obj M).transition h).val.app U x) := by
  have hg := (SemilinearSections.transition_exists (ProEt.topology T)
    (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).exists.choose_spec
      ((b.realization T).functor.obj M) U
  apply hg.trans
  have hB := b.restrictions T M (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
  have hD := a.transitions M h U
  refine hom_function_heq
    (eq_of_heq ((b.sections T M n U).trans (a.sections M n U).symm)) ?_
    (hB.trans hD.symm)
  have hm :
      ((SemilinearSections.ring (coefficientSequenceTopology (ProEt.topology T))
        (SemilinearSections.systemRing (ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))).obj.map
          (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op).hom =
      (((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            ((spCoefficientCommRings l E T).map (homOfLE h).op)).hom.app U).hom := by
    change ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((((SemilinearSections.rings (ProEt.topology T) (SpTowerShriek.B l E T)
        (SpTowerShriek.tau l E T)).map (homOfLE h).op).hom.app U) ≫
          (SpTowerShriek.B l E T m).obj.map (𝟙 U))).hom = _
    erw [(SpTowerShriek.B l E T m).obj.map_id U, Category.comp_id]
    change (((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (SemilinearSections.coefficientMap (ProEt.topology T)
            (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h)).hom.app U).hom = _
    rw [genericCoefficientMap_system l E T h]
  rw [hm]
  exact congrArg (ModuleCat.restrictScalars
    (((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((spCoefficientCommRings l E T).map (homOfLE h).op)).hom.app U).hom).obj
    (eq_of_heq ((b.sections T M m U).trans (a.sections M m U).symm))

private theorem heq_apply {A B A' B' : Type v} {f : A → B} {g : A' → B'}
    (hA : A = A') (hB : B = B') (hf : HEq f g) {x : A} {y : A'} (hx : HEq x y) :
    HEq (f x) (g y) := by
  cases hA
  cases hB
  cases hf
  cases hx
  rfl

end AlgebraicGeometry.ProEtale.SpTowerCalculus
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
