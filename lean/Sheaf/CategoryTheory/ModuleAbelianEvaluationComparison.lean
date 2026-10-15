/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Precoverage
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

import Sheaf.CategoryTheory.DeltaFunctor
import Sheaf.CategoryTheory.SiteCechComplex
import Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechExact
import Sheaf.CategoryTheory.InjectiveModulePresheaf
import Sheaf.CategoryTheory.SiteCechVanishingCriterion
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.DeltaFunctor
import WeilConjectures.CategoryTheory.SiteCechComplex

/-!
# Module and abelian evaluation cohomology on a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 03FD, second displayed equality
(blueprint: lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The right derived evaluation of module sheaves agrees naturally with the right
 derived evaluation of their underlying abelian sheaves. The equation in degree zero
 identifies the two augmentations from sections, so the comparison is the identity
 on sections under the canonical degree-zero identifications. The final clause characterizes
 the canonical map by every lift from a module resolution to an abelian resolution.

Source: Stacks Project, Cohomology on Sites, Tag 03FD, objectwise equality
(blueprint: lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison).

Proof: (1) Module evaluation is additive and left exact. The right-derived universal
 delta-functor theorem gives its universal delta-functor. Exact additive forgetting
 (moduleSheaves_colimits_forgetful, using exact sheafification) precomposes the abelian
 evaluation delta-functor to another delta-functor on module sheaves, with the same
 degree zero. (2) An injective module sheaf is injective as a module presheaf by
 injective_module_sheaf_injective_presheaf. The injective-presheaf Cech cocycle-lifting
 theorem makes all its positive Cech cohomology zero; forgetting leaves this complex
 unchanged. (3) Apply the site Cech vanishing criterion with all objects and all covers:
 fibre products stay in the collection and each cover refines itself. This proves
 positive abelian evaluation cohomology vanishes on injective module sheaves.
 (4) Embed any module sheaf into an injective one. The preceding vanishing effaces
 the positive-degree functors, so effaceable_deltaFunctor_isUniversal applies.
 (5) Universality extends the identity on degree zero in both directions. Uniqueness
 makes the composites identities, giving natural additive isomorphisms normalized
 as stated. For any comparison lift of resolutions, dimension shifting identifies
 the resulting homology map with this unique delta-functor comparison; homotopic lifts
 induce the same map. No flatness or injectivity after forgetting is used. -/
theorem module_abelian_evaluation_comparison
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (R : Sheaf J.toGrothendieck RingCat.{u})
    [EnoughInjectives (ringedSiteModules.{u} R)] (U : C) :
    ∃ e : ∀ q : ℕ,
      (SheafOfModules.toSheaf R ⋙
        (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).rightDerived q ≅
      SheafOfModules.toSheaf R ⋙
        (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q,
      ((SheafOfModules.toSheaf R ⋙
        (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))).toRightDerivedZero ≫
          (e 0).hom =
        Functor.whiskerLeft (SheafOfModules.toSheaf R)
          ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).toRightDerivedZero)) ∧
      ∀ (M : ringedSiteModules.{u} R) (I : InjectiveResolution M)
        (K : InjectiveResolution ((SheafOfModules.toSheaf R).obj M))
        (φ : ((SheafOfModules.toSheaf R).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
          K.cocomplex)
        (_hφ : (SheafOfModules.toSheaf R).map (I.ι.f 0) ≫ φ.f 0 = K.ι.f 0) (q : ℕ),
        (e q).hom.app M ≫
            (K.isoRightDerivedObj
              (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
                (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).hom =
          (I.isoRightDerivedObj
            (SheafOfModules.toSheaf R ⋙
              (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
                (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))) q).hom ≫
            HomologicalComplex.homologyMap
              (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
                (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
                  (.up ℕ)).map φ) q := by
  sorry

end CategoryTheory
