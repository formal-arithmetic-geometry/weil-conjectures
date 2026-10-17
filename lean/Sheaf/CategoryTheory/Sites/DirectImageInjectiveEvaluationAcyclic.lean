/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic
import Sheaf.CategoryTheory.SiteCechVanishingCriterion
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.CategoryTheory.SiteCechVanishingCriterion

/-!
# Object evaluation acyclicity of direct images of injective modules

Source: Stacks Project, Cohomology on Sites, Tags 072Z and 0731 (1)
(blueprint: lem-weil-pbc-ringed-site-direct-image-injective-evaluation-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- A module pushforward of an injective has zero positive derived object evaluation.

Source: Stacks Project, Cohomology on Sites, Tags 072Z and 0731 (1), using 03FD
(blueprint: lem-weil-pbc-ringed-site-direct-image-injective-evaluation-acyclic).

The precoverage instances are the site axioms. `hcover` and `hpullback` express
Stacks continuity (00WV); `IsContinuous` is its sheaf-theoretic consequence, used
only to type the pushforward. Finite-limit and finite-colimit preservation of the
set-sheaf pullback express that this continuous functor presents a morphism of sites.
All site, ring, module and covering-index universes are `u`. Evaluation followed by
scalar forgetting is exactly the additive left exact functor to abelian groups.
Positive integers are represented by positive naturals, since these are precisely
the degrees of right derived functors computed using injective resolutions.

Proof:
1. For any covering of an object of C, `hcover` gives its image covering in D.
   The comparisons of `hpullback`, iterated and compatible with each projection,
   identify their Cech complexes for the pushforward and I, including all
   alternating restriction differentials (def-weil-pbc-site-cech-complex).
   The scalar action through rho plays no role in this additive comparison.
2. Apply lem-weil-pbc-ringed-site-injective-module-cech-acyclic to I and each image
   covering. Exact abelian sheafification (lem-weil-pbc-sheafification-exact) and
   lem-weil-pbc-site-sheafification-iso-locally-bijective supply its sheafification
   hypotheses on these small sites. Thus all positive Cech groups vanish.
3. Apply lem-weil-pbc-site-cech-vanishing-criterion with all objects and all
   coverings. Intersections remain objects, and every covering refines itself.
   This gives positive abelian-sheaf object cohomology vanishing.
4. Apply lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison to the
   pushforward module: module-derived evaluation agrees with this abelian-sheaf
   cohomology. Enough injectives is assumed in both module categories. No step
   requires flatness of rho or injectivity of the pushforward module. -/
theorem ringedSite_directImage_injective_evaluation_isZero
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (F : C ⥤ D)
    (hcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map F ∈ K (F.obj X))
    (hpullback : ∀ (X Y Z : C) (S : Presieve X), S ∈ J X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), S f → PreservesLimit (cospan f g) F)
    [F.IsContinuous J.toGrothendieck K.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback F (Type u) J.toGrothendieck K.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback F (Type u) J.toGrothendieck K.toGrothendieck)]
    (R : Sheaf J.toGrothendieck RingCat.{u}) (S : Sheaf K.toGrothendieck RingCat.{u})
    (rho : R ⟶ (F.sheafPushforwardContinuous RingCat.{u}
      J.toGrothendieck K.toGrothendieck).obj S)
    [EnoughInjectives (ringedSiteModules.{u} R)]
    [EnoughInjectives (ringedSiteModules.{u} S)]
    (I : ringedSiteModules.{u} S) [Injective I] (U : C) (q : ℕ) (hq : 0 < q) :
    IsZero (((SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf R.obj ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj
        ((SheafOfModules.pushforward.{u} rho).obj I)) := by
  sorry

end CategoryTheory
