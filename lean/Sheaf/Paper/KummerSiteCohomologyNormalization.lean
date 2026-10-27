/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q153
-/
module

public import Sheaf.AlgebraicGeometry.RelativeKummerStrictLocalInvariance
public import Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
public import Sheaf.Paper.SiteComparisonEdgeSection
public import WeilConjectures.SixFunctors.ProEtale.ForgetModuleCohomology
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-! # Scalar Kummer classes under the etale/pro-etale comparison

Source: latest blueprint, sk-prop-a1-kummer/prop-pur-gm-relative-kummer.proof.md,
opening paragraph and Step 3; Stacks Tags 03FD, 099W, 09A6 and 072W
(blueprint: def-pur-kummer-site-cohomology-normalization).

The scalar identifications are constructed from the derived evaluation comparison
and the constant-integers adjunction. Only inverses of specified bijections are chosen.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Evaluate an abelian Ext class by the constant-integers/terminal-evaluation adjunction.
Source: Stacks 03FD and 099W (blueprint: def-pur-kummer-site-cohomology-normalization). -/
@[irreducible]
def kummerSiteAbelianEvaluation
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
    [PreservesFiniteLimits (constantSheaf J AddCommGrpCat.{u + 1})]
    (t : C) (ht : IsTerminal t) (F : Sheaf J AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H F q) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).obj
      ((Sheaf.sectionsFunctorAt J t).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  let R := (Sheaf.sectionsFunctorAt J t).rightDerivedFunctor
  let P := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let a := ((constantSheafAdj J AddCommGrpCat.{u + 1} ht).ofNatIsoRight
    (sheafSectionsNatIsoEvaluation J AddCommGrpCat.{u + 1}))
    |>.mapDerivedCategoryRightDerivedAdjunction
  let b := (constantSheaf J AddCommGrpCat.{u + 1}).mapDerivedCategorySingleFunctor 0
  let y := a.homEquiv _ _ (b.hom.app P ≫ x.hom)
  let z := DerivedCategory.homSingleToHomology P 0 _ y
  let e := (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).mapIso
      ((R.commShiftIso (q : ℤ)).app ((DerivedCategory.singleFunctor _ 0).obj F)) ≪≫
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).shiftIso (q : ℤ) 0 q
      (by simp)).app _ ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).mapIso
      ((Sheaf.sectionsFunctorAt J t).rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).symm
  e.hom (z (ULift.up 1))

/-- The terminal evaluation identification is the specified bijection, including degree zero.
Source: Stacks 03FD (blueprint: def-pur-kummer-site-cohomology-normalization).
Proof: the derived constant/evaluation adjunction identifies Ext with maps from Z[0]
to shifted derived sections. The lifted integers are projective, so taking H0 and
evaluating at 1 is bijective. The shift and D+/unbounded comparisons are isomorphisms. -/
theorem kummerSiteAbelianEvaluation_bijective
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
    [PreservesFiniteLimits (constantSheaf J AddCommGrpCat.{u + 1})]
    (t : C) (ht : IsTerminal t) (F : Sheaf J AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective (kummerSiteAbelianEvaluation J t ht F q) := by
  sorry

section Scalar

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A]
    [HasSheafify J AddCommGrpCat.{u + 1}] [HasSheafify J (ModuleCat.{u + 1} A)]
    [J.HasSheafCompose (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
    [PreservesFiniteLimits (constantSheaf J AddCommGrpCat.{u + 1})]
    [(sheafCompose J (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).Additive]
    [PreservesFiniteLimits
      (sheafCompose J (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}))]
    [PreservesFiniteColimits
      (sheafCompose J (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}))]

/-- The canonical derived scalar-forgetting evaluation comparison, obtained from the
identity of underived evaluation functors. No preservation of injectives is assumed.
Source: Stacks 03FD (blueprint: def-pur-kummer-site-cohomology-normalization). -/
@[irreducible]
def kummerSiteDerivedScalarMap (t : C) :=
  Functor.rightDerivedFunctorPlusBaseChange
    (G := sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙ (evaluation _ _).obj (op t))
    (G' := Sheaf.sectionsFunctorAt J t)
    (β := sheafCompose J (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}))
    (γ := forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) (𝟙 _)

/-- Scalar forgetting on global cohomology: derive the identity on evaluation, identify
exact forgetting with Hq, and use the inverse of the specified constant-integers bijection.
Source: Stacks 03FD (blueprint: def-pur-kummer-site-cohomology-normalization). -/
@[irreducible]
def kummerSiteScalarMap (t : C) (ht : IsTerminal t)
    (F : Sheaf J (ModuleCat.{u + 1} A)) (q : ℕ)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).obj
      (((sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op t)).rightDerivedFunctorPlus).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :
    Sheaf.H ((sheafCompose J
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj F) q :=
  let V := forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}
  let U := sheafCompose J V
  let G := sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙ (evaluation _ _).obj (op t)
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let d := (V.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app
    (G.rightDerivedFunctorPlus.obj K)
  let c := (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).map
    ((kummerSiteDerivedScalarMap J A t).app K ≫
      (Sheaf.sectionsFunctorAt J t).rightDerivedFunctorPlus.map
        ((U.mapDerivedCategoryPlusSingleFunctor 0).hom.app F))
  (Equiv.ofBijective _ (kummerSiteAbelianEvaluation_bijective J t ht (U.obj F) q)).symm
    (c (d x))

/-- The scalar identification is invertible for module sheaves on a site.
Source: Stacks 03FD (blueprint: def-pur-kummer-site-cohomology-normalization).
Proof: forgotten injective module sheaves are acyclic for abelian evaluation.
The comparison derived from the identity on sections is therefore invertible
(lem-pe-left-module-derived-evaluation-forget). Exact forgetting, the single-object
comparison and the inverse abelian evaluation bijection preserve bijectivity. -/
theorem kummerSiteScalarMap_bijective (t : C) (ht : IsTerminal t)
    (F : Sheaf J (ModuleCat.{u + 1} A)) (q : ℕ) :
    Function.Bijective (kummerSiteScalarMap J A t ht F q) := by
  sorry

end Scalar

/-- Module cohomology of the etale root line is terminal derived evaluation.
Source: Stacks 03FD (blueprint: def-pur-kummer-site-cohomology-normalization). -/
abbrev kummerSiteEtaleH (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ) :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).obj
    ((siteComparisonEtaleSections T A).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))

/-- Pro-etale module cohomology with its coefficient sheaf placed in degree zero.
Source: Stacks 03FD (blueprint: def-pur-kummer-site-cohomology-normalization). -/
abbrev kummerSiteProEtaleH (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) (q : ℕ) :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).obj
    ((siteComparisonProEtaleSections T A).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))

/-- The recorded derived-unit comparison, followed by its canonical single-sheaf
identification. Source: Stacks 099W
(blueprint: def-pur-kummer-site-cohomology-normalization). -/
@[irreducible]
def kummerSiteComparison (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ) :
    kummerSiteEtaleH T A F q ⟶
      kummerSiteProEtaleH T A ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F) q :=
  siteComparisonCohomologyMap T A F q ≫
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).map
      ((siteComparisonProEtaleSections T A).rightDerivedFunctorPlus.map
        ((Functor.mapDerivedCategoryPlusSingleFunctor
          (comparisonUpperStar (ModuleCat.{u + 1} A) T) 0).hom.app F))

/-- The scalar-extended Kummer class in module cohomology, uniquely determined by its
ordinary abelian boundary. Source: blueprint relative Kummer proof, opening paragraph
(blueprint: def-pur-kummer-site-cohomology-normalization). -/
@[irreducible]
def kummerSiteEtaleClass (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (hr : IsUnit (m : Γ(T, ⊤))) (w : Γ(T, ⊤)ˣ) :
    kummerSiteEtaleH T A (Scheme.finiteEtaleTateLine T m A hA) 1 :=
  (Equiv.ofBijective _ (kummerSiteScalarMap_bijective T.smallEtaleTopology A
    (Scheme.Etale.mk (𝟙 T)) (Scheme.Etale.isTerminalMkId T) _ 1)).symm
      (Etale.relativeKummerClass A m hA T hr w)

/-- The actual pro-etale abelian Kummer class, via canonical abelian cohomology pullback
and the specified scalar-forgetting coefficient isomorphism. Source: Stacks 099W
(blueprint: def-pur-kummer-site-cohomology-normalization). -/
@[irreducible]
def kummerSiteProAbelianClass (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (hr : IsUnit (m : Γ(T, ⊤))) (w : Γ(T, ⊤)ˣ) :=
  Sheaf.H.map
    ((sheafComposeForget₂CompComparisonUpperStarIso A T).hom.app
      (Scheme.finiteEtaleTateLine T m A hA)) 1
    (comparisonCohomologyMap T _ 1 (Etale.relativeKummerClass A m hA T hr w))

/-- The same pro-etale class in module cohomology, using the inverse of the specified
scalar-forgetting bijection. Source: Stacks 03FD and 099W
(blueprint: def-pur-kummer-site-cohomology-normalization). -/
@[irreducible]
def kummerSiteProEtaleClass (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (hr : IsUnit (m : Γ(T, ⊤))) (w : Γ(T, ⊤)ˣ) :
    kummerSiteProEtaleH T A
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (Scheme.finiteEtaleTateLine T m A hA)) 1 :=
  (Equiv.ofBijective _ (kummerSiteScalarMap_bijective (Scheme.ProEt.topology T) A
    (Scheme.ProEt.mk (𝟙 T)) (Scheme.ProEt.isTerminalMkId T) _ 1)).symm
      (kummerSiteProAbelianClass T A m hA hr w)

end AlgebraicGeometry.ProEtale
