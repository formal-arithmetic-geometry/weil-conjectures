/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Derived direct image and strict tower limits

Source: Stacks Project, Cohomology on Sites, Tags 0A07 and 0940
(blueprint: lem-weil-ringed-tower-pushforward-limit-comparison).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option maxHeartbeats 1200000 in
-- Repeated tower localizations and composite-unit equations require extra elaboration steps.
/-- The canonical comparison of derived direct image with strict tower inverse limit.

Source: Stacks Project, Cohomology on Sites, Tags 0A07, 0940 and 0941
(blueprint: lem-weil-ringed-tower-pushforward-limit-comparison).

`ℕ` indexes the positive levels by `n + 1`. The functors and their units are total
right derived functors with K-injective normalization. `E_R`, `E_S` evaluate derived
strict towers, including transitions; `εR`, `εS` identify them with evaluation on
complexes. The underived comparison `c` is characterized by `limit.post`, hence is
exactly the common-direct-image identification. The unit equation for `a` gives its
common-direct-image normalization, and the final equation is compatibility with every
projection. The equation for `e` fixes the evaluation identifications on K-injectives.

Proof plan:
1. Realize strict towers as module sheaves on the small tower site C × ℕ, with the
   constant coefficient ring. Its projection has exact constant-tower inverse image
   and inverse-limit direct image. Apply the geometric morphism and its structural
   map levelwise. The square of ringed topoi gives `c`, with the stated projections.
2. Resolve a tower complex by a K-injective tower. Evaluation preserves K-injectives
   by lem-weil-tower-evaluation-kinjective. Thus both evaluation routes are computed
   by the same levelwise direct-image complex, with identical transitions.
3. The exact constant-tower adjunction and lem-weil-pbc-right-adjoint-preserves-kinjective
   imply that inverse limit preserves K-injectives. Use
   lem-weil-pbc-ringed-strict-tower-homotopy-limit to compute its derived functor.
   Resolve the levelwise direct image again; it need not preserve K-injectives.
4. Apply lem-weil-pbc-ringed-topoi-derived-pushforward-composition to the two sides
   of the tower-site square. Their comparisons to the common total derived direct
   image give `a`; its unit normalization is precisely the displayed equation.
5. Naturality of strict projections gives q_n lim(j) = j_n f_*(p_n) as chain maps.
   Invert Q(j_n) to obtain the final projection equality under `e`.
6. Use lem-weil-pbc-kinjective-hom-derived to represent morphisms between resolved
   towers by chain maps up to homotopy. Evaluation, inverse limit and levelwise
   direct image preserve homotopies. All comparisons are therefore natural and
   independent of resolutions, without boundedness or product-exactness assumptions. -/
theorem ringedTowerPushforwardLimitComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J RingCat.{u}) (S : Sheaf K RingCat.{u})
    (_hcommR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (_hcommS : ∀ (U : Dᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u} R)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u} S)]
    [HasDerivedCategory.{w} ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R))]
    [HasDerivedCategory.{w} ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S))]
    (f : RingedToposMorphism R S) :
    ∃ (Rf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} R) ⥤ DerivedCategory.{w}
      (ringedSiteModules.{u, u, u, u} S))
      (Rt : DerivedCategory.{w} ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) ⥤ DerivedCategory.{w}
        ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S)))
      (LR : DerivedCategory.{w} ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) ⥤ DerivedCategory.{w}
        (ringedSiteModules.{u, u, u, u} R))
      (LS : DerivedCategory.{w} ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S)) ⥤ DerivedCategory.{w}
        (ringedSiteModules.{u, u, u, u} S))
      (ηf : (f.modules).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ Rf)
      (ηt : (((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u, u, u, u} R) (ringedSiteModules.{u,
        u, u, u} S)).obj f.modules)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ Rt)
      (ηR : ((lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R) ⥤ ringedSiteModules.{u, u, u, u}
        R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ LR)
      (ηS : ((lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S) ⥤ ringedSiteModules.{u, u, u, u}
        S)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ LS),
      Rf.IsRightDerivedFunctor ηf
        (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u} R) (ComplexShape.up ℤ)) ∧
      (∀ (I : CochainComplex (ringedSiteModules.{u, u, u, u} R) ℤ), I.IsKInjective → IsIso (ηf.app
        I)) ∧
      Rt.IsRightDerivedFunctor ηt
        (HomologicalComplex.quasiIso ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) (ComplexShape.up ℤ))
          ∧
      (∀ (I : CochainComplex ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) ℤ), I.IsKInjective → IsIso
        (ηt.app I)) ∧
      LR.IsRightDerivedFunctor ηR
        (HomologicalComplex.quasiIso ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) (ComplexShape.up ℤ))
          ∧
      (∀ (I : CochainComplex ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) ℤ), I.IsKInjective → IsIso
        (ηR.app I)) ∧
      LS.IsRightDerivedFunctor ηS
        (HomologicalComplex.quasiIso ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S)) (ComplexShape.up ℤ))
          ∧
      (∀ (I : CochainComplex ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S)) ℤ), I.IsKInjective → IsIso
        (ηS.app I)) ∧
      ∃ (E_R : DerivedCategory.{w} ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) ⥤ (ℕᵒᵖ ⥤
        DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} R)))
        (E_S : DerivedCategory.{w} ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S)) ⥤ (ℕᵒᵖ ⥤
          DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} S)))
        (εR : DerivedCategory.Q.{w} ⋙ E_R ≅ HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
          (Functor.whiskeringRight ℕᵒᵖ (CochainComplex (ringedSiteModules.{u, u, u, u} R) ℤ)
          (DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} R))).obj DerivedCategory.Q.{w})
        (εS : DerivedCategory.Q.{w} ⋙ E_S ≅ HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
          (Functor.whiskeringRight ℕᵒᵖ (CochainComplex (ringedSiteModules.{u, u, u, u} S) ℤ)
          (DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} S))).obj DerivedCategory.Q.{w})
        (pR : ∀ n : ℕᵒᵖ, LR ⟶ E_R ⋙ (evaluation ℕᵒᵖ (DerivedCategory.{w} (ringedSiteModules.{u, u,
          u, u} R))).obj n)
        (pS : ∀ n : ℕᵒᵖ, LS ⟶ E_S ⋙ (evaluation ℕᵒᵖ (DerivedCategory.{w} (ringedSiteModules.{u, u,
          u, u} S))).obj n)
        (c : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R) ⥤ ringedSiteModules.{u, u, u, u} R) ⋙
          f.modules ≅ ((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u, u, u, u} R)
          (ringedSiteModules.{u, u, u, u} S)).obj f.modules) ⋙ (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u,
          u, u, u} S) ⥤ ringedSiteModules.{u, u, u, u} S))
        (e : Rt ⋙ E_S ≅ E_R ⋙
          (Functor.whiskeringRight ℕᵒᵖ (DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} R))
            (DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} S))).obj Rf)
        (a : LR ⋙ Rf ≅ Rt ⋙ LS),
        (∀ H : (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R), c.hom.app H = limit.post H f.modules) ∧
        (∀ (X : CochainComplex ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) ℤ) (n : ℕᵒᵖ),
          ηR.app X ≫ (pR n).app (DerivedCategory.Q.{w}.obj X) ≫ (εR.hom.app X).app n =
            DerivedCategory.Q.{w}.map ((NatTrans.mapHomologicalComplex
              (lim.π n : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R) ⥤ ringedSiteModules.{u, u,
                u, u} R) ⟶ (evaluation ℕᵒᵖ (ringedSiteModules.{u, u, u, u} R)).obj n)
                (ComplexShape.up ℤ)).app X)) ∧
        (∀ (X : CochainComplex ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S)) ℤ) (n : ℕᵒᵖ),
          ηS.app X ≫ (pS n).app (DerivedCategory.Q.{w}.obj X) ≫ (εS.hom.app X).app n =
            DerivedCategory.Q.{w}.map ((NatTrans.mapHomologicalComplex
              (lim.π n : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S) ⥤ ringedSiteModules.{u, u,
                u, u} S) ⟶ (evaluation ℕᵒᵖ (ringedSiteModules.{u, u, u, u} S)).obj n)
                (ComplexShape.up ℤ)).app X)) ∧
        (∀ (I : CochainComplex ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) ℤ), I.IsKInjective → ∀ n :
          ℕᵒᵖ,
          (E_S.map (ηt.app I)).app n ≫ (e.hom.app (DerivedCategory.Q.{w}.obj I)).app n ≫
              Rf.map ((εR.hom.app I).app n) =
            (εS.hom.app (((((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u, u, u, u} R)
              (ringedSiteModules.{u, u, u, u} S)).obj f.modules)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)).app n ≫ ηf.app (I.asFunctor.obj n)) ∧
        (∀ X : CochainComplex ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) ℤ,
          ηf.app ((((lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R) ⥤ ringedSiteModules.{u, u, u, u}
            R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫ Rf.map (ηR.app X) ≫
              a.hom.app (DerivedCategory.Q.{w}.obj X) =
            DerivedCategory.Q.{w}.map ((NatTrans.mapHomologicalComplex c.hom (ComplexShape.up
              ℤ)).app X) ≫
              ηS.app (((((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u, u, u, u} R)
                (ringedSiteModules.{u, u, u, u} S)).obj f.modules)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj X) ≫ LS.map (ηt.app X)) ∧
        (∀ (M : DerivedCategory.{w} ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R))) (n : ℕᵒᵖ),
          a.hom.app M ≫ (pS n).app (Rt.obj M) ≫ (e.hom.app M).app n =
            Rf.map ((pR n).app M)) := by
  sorry

end CategoryTheory
