/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation

/-!
# Small diagrams of module sheaves form a Grothendieck category

Source: Stacks Project, Injectives, Tags 05AB, 079B and 079Q.
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory

/-- Small diagrams of left module sheaves over an arbitrary ring sheaf are Grothendieck abelian.
Source: Stacks Project, Injectives, Tags 05AB, 079B and 079Q, with the small-diagram extension. -/
theorem smallModuleDiagrams_isGrothendieckAbelian
    {C : Type u} [SmallCategory C] (τ : GrothendieckTopology C)
    (R : Sheaf τ RingCat.{u}) (J : Type u) [SmallCategory J] :
    IsGrothendieckAbelian.{u} (J ⥤ ringedSiteModules.{u} R) := by
  let : IsGrothendieckAbelian.{u} (ringedSiteModules.{u} R) :=
    SheafOfModules.isGrothendieckAbelian R
  let G := separator (ringedSiteModules.{u} R)
  have hG := isSeparator_separator (ringedSiteModules.{u} R)
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : J ↦ (evaluationLeftAdjoint (ringedSiteModules.{u} R) j).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight (ringedSiteModules.{u} R) j
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (J ⥤ ringedSiteModules.{u} R) :=
    ⟨_, hS.isSeparator_coproduct⟩
  let : Limits.HasFilteredColimitsOfSize.{u, u} (J ⥤ ringedSiteModules.{u} R) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{u, u} (J ⥤ ringedSiteModules.{u} R) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  exact {}

end CategoryTheory
