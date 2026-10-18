# CategoryTheory.ringedTowerPushforwardLimitComparison proof context

## Reason

The assigned module `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison` gains private,
proved generic helpers. Their universes and section-scoped variables and the two backward
elaboration options trigger the stage-3 gate's conservative check for non-declaration commands.
This record documents those commands. The existing theorem signature, public imports, and
mathematical meaning are identical. Options affect elaboration in this file; the helper section
ends before the existing theorem. No private helper occurs in a public signature or public data
definition. There is no definition repair and no target statement or target meaning changes.

## Old

The original context was `universe u w`, followed by the existing open command and namespace.
The existing signature, verbatim:

```lean
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
            Rf.map ((pR n).app M))
```

## New

The added context is the following, with only private helpers under `section Helpers`:

```lean
universe u w uA uB vA vB

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

section Helpers

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
```

The same private helper section later adds the following scoped assumptions:

```lean
variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
variable [HasLimitsOfShape ℕᵒᵖ A]
```

`end Helpers` closes that section before the two private ringed-site limit helpers and the
existing theorem. The existing signature remains verbatim:

```lean
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
            Rf.map ((pR n).app M))
```

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison --uses
CategoryTheory.ringedTowerPushforwardLimitComparison` reported zero downstream modules and only
the declaration's own occurrence. No consumer fails or needs adaptation. Both delivered modules
compile cleanly in import order; the existing signature was also compared byte-for-byte.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison | S1 | Private proof context and proof only; public imports and existing signature unchanged. |

## Status

landed 20261018T093506-L-3541548 2026-10-18 (merge of deliver/S1/Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison)
