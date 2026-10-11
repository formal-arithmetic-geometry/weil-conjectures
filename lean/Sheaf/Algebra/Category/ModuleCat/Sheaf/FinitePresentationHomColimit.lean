/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Sheaf Hom out of a module of finite presentation commutes with directed colimits

Source: literature/stacks-project/modules.tex, Modules, Lemma 0GMV (blueprint:
lem-weil-pbc-sheaf-hom-finite-presentation-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace SheafOfModules

/-- Sheaf Hom out of a finitely presented module on a ringed space commutes with
directed colimits.

Source: Stacks Project, Modules, Lemma 0GMV.
(blueprint: lem-weil-pbc-sheaf-hom-finite-presentation-colimit).

Proof follows Lemma 0GMV step by step:
1. Colimits commute with restriction to opens
   [lem-weil-pbc-ringed-space-colimit-restriction]. Internal Hom restricts to internal
   Hom [def-pur-sheaf-hom], so restrict to an open where G has a finite presentation.
   Isomorphisms can be checked on this cover
   [lem-weil-pbc-sheaf-isomorphism-local-open-cover].
2. Apply [lem-weil-pbc-sheaf-hom-finite-presentation-kernel] to the presentation and
   each F.obj i, and to c.pt. This identifies their internal Homs with the kernels
   of the maps from the n-fold direct sums to the m-fold direct sums. Transition
   maps and cocone legs induce a commutative diagram of these exact rows.
3. Form the colimit of the Hom diagram by sheafifying the sectionwise colimit
   [lem-weil-pbc-module-sheaves-colimits-forgetful]. Filtered colimits are exact by
   the same result, and commute with finite direct sums. The colimit row therefore
   has the same kernel presentation as homObj G c.pt. The last two comparison
   arrows are isomorphisms, hence so is the induced kernel comparison u.
   The colimit universal property [def-weil-pbc-category-colimit] gives exactly
   the displayed compatibility with every leg and uniqueness among all morphisms.
-/
theorem hom_finitePresentation_colimit
    (X : Type u) [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj R))
    [G.IsFinitePresentation]
    (F : I ⥤ SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj R))
    (c : Cocone F) (hc : IsColimit c) :
    ∃ (cH : Cocone (F ⋙ (SheafOfModules.homFunctor R).obj (op G))),
      Nonempty (IsColimit cH) ∧
      ∃ (u : cH.pt ⟶ SheafOfModules.homObj (R := R) G c.pt),
        IsIso u ∧
        (∀ i : I,
          cH.ι.app i ≫ u =
            SheafOfModules.homObjMap (R := R) (𝟙 G) (c.ι.app i)) ∧
        (∀ v : cH.pt ⟶ SheafOfModules.homObj (R := R) G c.pt,
          (∀ i : I,
            cH.ι.app i ≫ v =
              SheafOfModules.homObjMap (R := R) (𝟙 G) (c.ι.app i)) → v = u) := by
  sorry

end SheafOfModules
