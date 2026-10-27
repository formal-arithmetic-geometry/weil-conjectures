/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.CategoryTheory.Sites.RingedSiteSectionFunctors
import Sheaf.CategoryTheory.FiniteTypeRestrictionExact
import Sheaf.ProperBaseChange.SingletonSiteModuleComparison
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact

/-! # Evaluation of a direct-image resolution

Source: Stacks Project, Cohomology on Sites, Tags 0D6H, 0D6G and 0D6E.
(blueprint: lem-sfb-leray-section-resolution-quasi-iso).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.RingedSiteSectionFunctors

namespace CategoryTheory.UnboundedSectionsLocalization

/-- A K-injective resolution of the direct image of a K-injective complex is a
quasi-isomorphism after evaluation at any target site object and forgetting scalars.

Source: Stacks Project, Cohomology on Sites, Tag 0D6H (lemma-Leray-unbounded),
second assertion, using Tags 0D6G and 0D6E.
(blueprint: lem-sfb-leray-section-resolution-quasi-iso).

Proof: Fix V and restrict I and T to the slice sites C/u(V) and D/V.
Restriction preserves K-injectivity by Tag 08FI and is exact, so the restriction
of j is still a K-injective resolution. The localized ringed-site morphism has
module direct image canonically equal to the restriction of the original direct
image, including its section-ring action (Tag 04J0). On D/V, constant
sheafification is left adjoint to evaluation at the terminal object id_V and
preserves finite limits. The identity of B(V) therefore defines a morphism from
this ringed topos to the punctual topos with ring B(V). Under the exact
singleton-site module equivalence, its module direct image is evaluation at id_V.
Apply the K-injective-resolution normalization in Tag 0D6E to the localized
morphism followed by this punctual morphism. It says precisely that evaluation
of the restricted j at id_V is a quasi-isomorphism of B(V)-module complexes.
The sectionwise direct-image identity identifies its source with I(u(V)) and
its target with T(V). Forgetting scalars preserves and reflects cohomology,
so the resulting map of abelian group complexes is a quasi-isomorphism.
This argument uses neither flatness of the ring map nor K-injectivity of f_*I. -/
theorem leraySectionResolution_quasiIso
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (u : D ⥤ C) [u.IsContinuous K J]
    (a : B ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj A)
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)]
    (I : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) ℤ) [I.IsKInjective]
    (T : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)) ℤ) [T.IsKInjective]
    (j : ((SheafOfModules.pushforward.{u} (sectionModuleMap u a)).mapHomologicalComplex
      (.up ℤ)).obj I ⟶ T) [QuasiIso j] (V : D) :
    QuasiIso (((sectionEvaluation
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B) V).mapHomologicalComplex
        (.up ℤ)).map j) := by sorry

end CategoryTheory.UnboundedSectionsLocalization
