/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback

/-!
# Composition of unbounded derived direct images of ringed topoi

Source: Stacks Project, Cohomology on Sites, Tag 0D6E
(blueprint: lem-weil-pbc-ringed-topoi-derived-pushforward-composition).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option maxHeartbeats 800000 in
-- Repeated module localizations and their comparison-unit equations require more elaboration steps.
/-- The total derived module direct images compose canonically, including the normalization
on arbitrary K-injective resolutions of the intermediate direct image.

Source: Stacks Project, Cohomology on Sites, Tag 0D6E
(blueprint: lem-weil-pbc-ringed-topoi-derived-pushforward-composition).

The three existential functors and their units are total right derived functors, computed
on K-injectives as asserted by the invertibility clauses. The direct image of the composite
is the composite module functor. The unit equation characterizes the canonical comparison.
The final equation identifies its component with the class of `g_*j`: the comparison units
at `I` and `J` and the inverse of `Q(j)` are precisely the resolution identifications.

Proof plan:
1. Use the tensor module pullback adjunction for each ringed-topos map. Pass termwise to
   homotopy categories. K-injective resolutions exist on each small ringed site by
   prop-pur-kinjective-resolutions-exist. Apply lem-weil-pbc-kinjective-total-derived and
   lem-pc-derived-adjoint-functors to obtain the canonical derived adjunctions, normalized
   by the fraction formula of lem-pc-pre-derived-adjoint-functors-general.
2. The underlying direct images and the structural coefficient actions identify the
   composite module direct image with g_*f_*. Conjugation of this identification gives
   the underived module pullback composition and its composite counit equation.
3. Choose a K-flat resolution with flat terms using lem-pc-kflat-resolution. Pullback
   preserves these representatives. The termwise pullback comparison descends through
   the K-flat localization (lem-weil-pbc-site-derived-tensor-descent) to a natural derived
   pullback composition isomorphism, independently of the resolution.
4. Conjugate that isomorphism through the canonical derived adjunctions to obtain kappa.
   The adjunction hom bijections characterize it and give its inverse and naturality.
5. For a K-injective I and a resolution j:f_*I→J, represent maps into Qg_*f_*I by right
   fractions, and refine the denominator by a K-flat resolution with flat terms.
6. Apply the canonical fraction adjunction formula twice. Naturality of the module
   counits cancels Q(j) against its inverse in D(B). The composite counit equation from
   step 2 identifies the resulting map with the adjunct of Q(g_*j). Hence Q(g_*j) is
   exactly the kappa component under the displayed resolution identifications.
7. Since that component is invertible, the cohomology criterion implies g_*j is a
   quasi-isomorphism. Uniqueness of maps into K-injectives in the derived category gives
   resolution independence; all comparisons are natural. Universal uniqueness of the
   total right derived functor makes the unit characterization unique. No claim that
   f_* preserves K-injectives is used. -/
theorem ringedToposDerivedPushforwardComposition
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E)
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (R : Sheaf L CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat
      RingCat)).obj
      A))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat
      RingCat)).obj
      B))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose L (forget₂ CommRingCat
      RingCat)).obj
      R))]
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (g : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj R)) :
    ∃ (Rf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
      CommRingCat
      RingCat)).obj
      A)) ⥤
          DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat
            RingCat)).obj
            B)))
      (Rg : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂
        CommRingCat
        RingCat)).obj
        B)) ⥤
          DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose L (forget₂ CommRingCat
            RingCat)).obj
            R)))
      (Rgf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
        CommRingCat
        RingCat)).obj A)) ⥤
          DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose L (forget₂ CommRingCat
            RingCat)).obj
            R)))
      (ηf : f.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ Rf)
      (ηg : g.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ Rg)
      (ηgf : (f.modules ⋙ g.modules).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ Rgf),
      Rf.IsRightDerivedFunctor ηf
          (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
            CommRingCat
            RingCat)).obj A)) (ComplexShape.up ℤ)) ∧
      Rg.IsRightDerivedFunctor ηg
          (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂
            CommRingCat
            RingCat)).obj B)) (ComplexShape.up ℤ)) ∧
      Rgf.IsRightDerivedFunctor ηgf
          (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
            CommRingCat
            RingCat)).obj A)) (ComplexShape.up ℤ)) ∧
      (∀ (I : CochainComplex (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat
        RingCat)).obj A)) ℤ),
        I.IsKInjective → IsIso (ηf.app I) ∧ IsIso (ηgf.app I)) ∧
      (∀ (T : CochainComplex (ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat
        RingCat)).obj B)) ℤ),
        T.IsKInjective → IsIso (ηg.app T)) ∧
      ∃! κ : Rgf ≅ Rf ⋙ Rg,
        (∀ (M : CochainComplex (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat
          RingCat)).obj A)) ℤ),
          ηgf.app M ≫ κ.hom.app (DerivedCategory.Q.{w}.obj M) =
            ηg.app ((f.modules.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
              Rg.map (ηf.app M)) ∧
        ∀ (I : CochainComplex (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat
          RingCat)).obj A)) ℤ),
          I.IsKInjective → ∀ (T : CochainComplex (ringedSiteModules.{u, u, u, u} ((sheafCompose K
            (forget₂
            CommRingCat RingCat)).obj B)) ℤ),
          T.IsKInjective →
          ∀ (j : (f.modules.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ T),
          ∀ [QuasiIso j],
          QuasiIso ((g.modules.mapHomologicalComplex (ComplexShape.up ℤ)).map j) ∧
          ηgf.app I ≫ κ.hom.app (DerivedCategory.Q.{w}.obj I) =
            DerivedCategory.Q.{w}.map
                ((g.modules.mapHomologicalComplex (ComplexShape.up ℤ)).map j) ≫
              ηg.app T ≫ Rg.map (inv (DerivedCategory.Q.{w}.map j) ≫ ηf.app I) := by
  sorry

end CategoryTheory
