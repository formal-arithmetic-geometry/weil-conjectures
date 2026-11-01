/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.RingTheory.Ideal.Span
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Equality of section ideals on common slice refinements

Source: Stacks Project, algebraization.tex, Tag 099E.
(blueprint: lem-weil-pbc-ringed-generating-lists-local-equality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite
open scoped BigOperators
namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})
variable (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
variable (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))

private theorem generatingList_section_value
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U))
    (σ : (I.over U).GeneratingSections) (e : σ.I ≃ Fin r)
    (h : ∀ i, (SheafOfModules.sectionsMap (ι.over U) (σ.s i)).val
      (op (Over.mk (𝟙 U))) = f (e i))
    (W : C) (a : W ⟶ U) (i : σ.I) :
    ι.val.app (op W) ((σ.s i).val (op (Over.mk a))) = O.obj.map a.op (f (e i)) := by
  let k : Over.mk a ⟶ Over.mk (𝟙 U) := Over.homMk a (by simp)
  have hn := (SheafOfModules.sectionsMap (ι.over U) (σ.s i)).property k.op
  change O.obj.map a.op
    ((SheafOfModules.sectionsMap (ι.over U) (σ.s i)).val (op (Over.mk (𝟙 U)))) = _ at hn
  rw [h] at hn
  exact hn.symm

end CategoryTheory
