/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.FreeModuleSheafConstruction
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.Paper.SheafSliceOrdinarySquare
import Sheaf.CategoryTheory.RingedPresentationTransport
import Sheaf.CategoryTheory.RingedSheafSliceAdjunction
import Sheaf.CategoryTheory.Sites.DirectImageInjectiveEvaluationAcyclic
import Sheaf.CategoryTheory.RingedToposSitePresentation

/-!
# Direct images of injective modules are totally acyclic

Source: Stacks Project, Cohomology on Sites, Tags 072Y and 072Z, Section 079X
(blueprint: lem-sfb-injective-pushforward-totally-acyclic).

Sections over a sheaf of sets are represented by the existing free module sheaf on
that sheaf. The right derived functor is computed in the module category, using
its Grothendieck abelian structure to supply injective resolutions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Sections over an arbitrary sheaf of sets, as an additive functor on modules.
Source: Stacks Project, Cohomology on Sites, Section 079X, before Tag 072Y
(blueprint: lem-sfb-injective-pushforward-totally-acyclic).

Restriction to the canonical generators of `B[E]` identifies this group with
`Hom(E, N_sets)`. The existing free-module construction is sheafification of the
sectionwise free module, so extension sends a finite sum to the same sum of its
coefficients times the chosen generator images. Thus addition in this Hom group
is precisely pointwise addition of sections. Postcomposition is the sections map.
No site object representing E is assumed. -/
abbrev moduleSheafSections {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (B : Sheaf J CommRingCat.{u}) (E : Sheaf J (Type u)) :
    ringedSiteModules.{u} (SheafFreeModule.ring B) ⥤ AddCommGrpCat.{u} :=
  preadditiveCoyoneda.obj (op ((SheafFreeModule.free B).obj E))

/-- The module-derived cohomology of sections over a sheaf of sets.
Source: Stacks Project, Cohomology on Sites, Section 079X, before Tag 072Y
(blueprint: lem-sfb-injective-pushforward-totally-acyclic).

The existing Grothendieck theorem supplies enough injectives; Mathlib's
`rightDerived` applies the additive sections functor to an injective resolution
in `Mod(B)` and takes its degree-q homology. In particular this does not derive
sections after forgetting to abelian sheaves. -/
def moduleSheafSectionCohomology {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (B : Sheaf J CommRingCat.{u})
    (E : Sheaf J (Type u)) (q : ℕ) :
    ringedSiteModules.{u} (SheafFreeModule.ring B) ⥤ AddCommGrpCat.{u} :=
  letI := SheafOfModules.isGrothendieckAbelianOfUniverses.{u, u, u, u}
    J (SheafFreeModule.ring B)
  (moduleSheafSections B E).rightDerived q

/-- Direct image of an injective module is totally acyclic, without flatness.
Source: Stacks Project, Cohomology on Sites, Tags 072Z and 072Y
(blueprint: lem-sfb-injective-pushforward-totally-acyclic).

Proof (the five steps of the DAG node):
1. All module categories on the small sites, their element sites, and replacement
   sites are Grothendieck abelian by lem-weil-pbc-ring-sheaves-grothendieck, hence
   have enough injectives by lem-sp-grothendieck-enough-injectives.
2. For E on the target put B' = f.inverse(E). Restriction to either element site
   is exact with exact additive left adjoint by
   lem-weil-pbc-ringed-sheaf-slice-adjunction, so it preserves injectives by the
   lifting property in def-sp-injective-resolutions. Compatible sections indexed
   by (U,s), s in E(U), are exactly maps E to the underlying set sheaf. Applying
   restriction to an injective resolution identifies H^q(E,-) with derived global
   sections on the element site. The same assertion applies to B'.
3. The module square of lem-sbc-ringed-sheaf-slice-ordinary-square identifies the
   restriction of f_*I with f_{E*} of the restricted injective module. This is an
   ordinary module identity, including its structural scalar action.
4. Apply lem-weil-pbc-ringed-topos-site-presentation to f_E and transport along
   lem-weil-pbc-ringed-presentation-transport. The exact module equivalences
   preserve injectives and global sections, hence derived global sections. The
   resulting ringed-site morphism is induced by a continuous finite-limit functor.
5. Its target site has a terminal object T. Global sections are evaluation at T.
   The direct image has sections I'(v(U)) and scalar action through the adjunct
   structural map, by def-weil-pbc-ringed-topos-morphism and
   def-weil-pbc-sites-and-cohomology. Apply
   lem-weil-pbc-ringed-site-direct-image-injective-evaluation-acyclic at T and
   transport its positive-degree vanishing back through steps 4, 3, and 2.
   E was arbitrary, giving exactly total acyclicity. No assertion that f_*I is
   injective, no flatness, and no site presentation of the original f is used. -/
theorem ringedTopos_directImage_injective_totally_acyclic
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism (SheafFreeModule.ring A) (SheafFreeModule.ring B))
    (I : ringedSiteModules.{u} (SheafFreeModule.ring A)) [Injective I]
    (E : Sheaf K (Type u)) (q : ℕ) (hq : 0 < q) :
    IsZero ((moduleSheafSectionCohomology B E q).obj (f.modules.obj I)) := by
  sorry

end CategoryTheory
