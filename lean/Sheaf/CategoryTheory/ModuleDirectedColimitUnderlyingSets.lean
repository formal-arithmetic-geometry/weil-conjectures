/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Underlying sheaves of sets and directed colimits of module sheaves

Source: Stacks Project, modules.tex, Lemma 01AH (line 204), together with
Sheaves Lemmas 007O and 0087 and Section 009E (blueprint:
lem-weil-pbc-module-directed-colimit-underlying-sets).
-/

@[expose] public section

universe u r

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {X : Type u} [TopologicalSpace X]

/-- The underlying sheaf of sets of a directed colimit of sheaves of modules is the
colimit of the underlying sheaves of sets. Source: Stacks Project, Modules 01AH(2),
Sheaves 007O(7), 0087(1), and Section 009E(3); directed sets are nonempty preorders
as in Categories, Definition `definition-directed-set`.

First form the sectionwise presheaf module colimit
(`lem-weil-pbc-presheaf-modules-colimits-sectionwise`). Its sheafification is the module
colimit by `lem-weil-pbc-module-sheaves-colimits-forgetful`, hence canonically isomorphic
as a cocone to the given colimit. For every open, the filtered module colimit has underlying
set the colimit of underlying sets (`lem-weil-pbc-filtered-colimit-modules-elementwise`),
compatibly with restrictions. Second, module sheafification has underlying sheaf of sets
the sheafification of the underlying presheaf
(`lem-weil-pbc-module-sheafification-underlying-sets`); transport this identification to
the given cocone, preserving its structure maps. Third, sheafifying the objectwise
presheaf colimit gives a colimit of sheaves of sets
(`lem-weil-pbc-sheaves-colimit-sheafification`). This proves the asserted universal property
for the underlying cocone (blueprint: lem-weil-pbc-module-directed-colimit-underlying-sets). -/
theorem underlying_directed_colimit_isColimit
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{r})
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ SheafOfModules.{u} O) (c : Cocone F) (_hc : IsColimit c) :
    Nonempty (IsColimit (((toSheaf O ⋙
      sheafCompose (Opens.grothendieckTopology X)
        (CategoryTheory.forget AddCommGrpCat.{u}))).mapCocone
        c)) := by
  sorry

end SheafOfModules
