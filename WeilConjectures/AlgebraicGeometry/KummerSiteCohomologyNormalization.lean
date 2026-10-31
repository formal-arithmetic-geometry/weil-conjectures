/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
public import WeilConjectures.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.ComparisonForgetScalars
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.RelativeKummerStrictLocalInvariance
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Canonical evaluation and scalar Kummer classes on the two small sites

Source: Stacks Project, Tags 03FD and 099W; the opening comparison paragraph of
`prop-pur-gm-relative-kummer.proof.md` in the current blueprint
(blueprint: def-pur-kummer-site-cohomology-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

section Site

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}

/-- Terminal evaluation, the section functor whose right derived functor is used here.
Source: Stacks, 01FT (blueprint: def-pur-kummer-site-cohomology-normalization). -/
abbrev kummerSiteEvaluation (B : Type v) [Category.{w} B] (t : C) : Sheaf J B ⥤ B :=
  sheafToPresheaf J B ⋙ (evaluation Cᵒᵖ B).obj (op t)

/-- The specified Ext-to-evaluation map: transpose the Ext morphism under the derived
constant-integer/evaluation adjunction, take H0, evaluate at one, and undo the shift.
Source: Stacks, 01FT (blueprint: def-pur-kummer-site-cohomology-normalization). -/
def kummerSiteAbelianEvaluation (t : C) (ht : IsTerminal t)
    (F : Sheaf J AddCommGrpCat.{u + 1}) (q : ℕ) (x : Sheaf.H F q) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).obj
      ((kummerSiteEvaluation AddCommGrpCat.{u + 1} t).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  let Z := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let L := constantSheaf J AddCommGrpCat.{u + 1}
  let G := (sheafSections J AddCommGrpCat.{u + 1}).obj (op t)
  letI : G.Additive := inferInstanceAs
    (kummerSiteEvaluation AddCommGrpCat.{u + 1} t).Additive
  let f : (DerivedCategory.Plus.singleFunctor _ 0).obj (L.obj Z) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧ :=
    (ObjectProperty.fullyFaithfulι DerivedCategory.TStructure.t.plus).preimage
      (x.hom ≫ (DerivedCategory.Plus.ι.commShiftIso (q : ℤ)).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  let a := (constantSheafAdj J AddCommGrpCat.{u + 1} ht).derivedPlus.homEquiv
    ((DerivedCategory.Plus.singleFunctor _ 0).obj Z)
    (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧)
      (((L.mapDerivedCategoryPlusSingleFunctor 0).app Z).hom ≫ f)
  let b := a ≫ (G.rightDerivedFunctorPlus.commShiftIso (q : ℤ)).hom.app
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  exact (((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} 0).shiftIso
      (q : ℤ) 0 q (add_zero _)).hom.app
        (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    (((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} 0).map b)
      (((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := AddCommGrpCat.{u + 1}) 0).inv.app Z) (ULift.up 1)))

/-- The specified abelian evaluation map is bijective.
Source: Stacks, 01FT (blueprint: def-pur-kummer-site-cohomology-normalization).
Proof: Ext is Hom between single objects with the indicated shift. Both single objects
and their shifts lie in D+, whose inclusion is fully faithful. The derived adjunction
transposes this Hom bijectively. Hom from Z[0] into a bounded below derived abelian group
is H0, since Z is projective. Evaluation at one and the canonical H0/shift identification
therefore give a bijection, including q=0. -/
theorem kummerSiteAbelianEvaluation_bijective (t : C) (ht : IsTerminal t)
    (F : Sheaf J AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective (kummerSiteAbelianEvaluation t ht F q) := by
  sorry

variable {A : Type (u + 1)} [CommRing A]

/-- The existing exact coefficient-forgetting functor, with its coefficient universe fixed.
Source: Stacks, 03FD (blueprint: def-pur-kummer-site-cohomology-normalization). -/
abbrev kummerSiteCoefficientForget (A : Type (u + 1)) [CommRing A] :
    ModuleCat.{u + 1} A ⥤ AddCommGrpCat.{u + 1} :=
  forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}

/-- Use Mathlib's fixed-universe coefficient colimit-preservation instance.
Source: Stacks, 03FD (blueprint: def-pur-kummer-site-cohomology-normalization). -/
instance (priority := high) kummerSiteCoefficientForget_preservesColimits :
    PreservesColimits (kummerSiteCoefficientForget A) :=
  ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} A

/-- Forget the coefficient action sectionwise.
Source: Stacks, 03FD (blueprint: def-pur-kummer-site-cohomology-normalization). -/
abbrev kummerSiteForget : Sheaf J (ModuleCat.{u + 1} A) ⥤
    Sheaf J AddCommGrpCat.{u + 1} :=
  sheafCompose J (kummerSiteCoefficientForget A)

/-- Derive the literal scalar-forgetting square and normalize its target single object.
Source: Stacks, 03FD (blueprint: def-pur-kummer-site-cohomology-normalization). -/
def kummerSiteDerivedScalarMap (t : C) (F : Sheaf J (ModuleCat.{u + 1} A)) :
    (kummerSiteCoefficientForget A).mapDerivedCategoryPlus.obj
      ((kummerSiteEvaluation (ModuleCat.{u + 1} A) t).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶
    (kummerSiteEvaluation AddCommGrpCat.{u + 1} t).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (kummerSiteForget.obj F)) := by
  let U : ModuleCat.{u + 1} A ⥤ AddCommGrpCat.{u + 1} := kummerSiteCoefficientForget A
  let S := sheafCompose J U
  letI : PreservesColimitsOfSize.{0, 0} S :=
    (Sheaf.forget₂CoinduceAdj.{u + 1, u, u + 1} J A).leftAdjoint_preservesColimits
  letI : PreservesFiniteColimits S := inferInstance
  letI : PreservesFiniteLimits S := by
    have : PreservesFiniteLimits (S ⋙ sheafToPresheaf J AddCommGrpCat.{u + 1}) :=
      inferInstanceAs (PreservesFiniteLimits
        (sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙
          (Functor.whiskeringRight _ _ _).obj U))
    exact preservesFiniteLimits_of_reflects_of_preserves S
      (sheafToPresheaf J AddCommGrpCat.{u + 1})
  let e : kummerSiteEvaluation (ModuleCat.{u + 1} A) t ⋙ U ⟶
      S ⋙ kummerSiteEvaluation AddCommGrpCat.{u + 1} t := 𝟙 _
  exact (Functor.rightDerivedFunctorPlusBaseChange e).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
    (kummerSiteEvaluation AddCommGrpCat.{u + 1} t).rightDerivedFunctorPlus.map
      ((S.mapDerivedCategoryPlusSingleFunctor 0).hom.app F)

/-- Scalar forgetting on cohomology, followed by the inverse of the specified abelian
Ext/evaluation bijection. Source: Stacks, 03FD
(blueprint: def-pur-kummer-site-cohomology-normalization). -/
def kummerSiteScalarMap (t : C) (ht : IsTerminal t)
    (F : Sheaf J (ModuleCat.{u + 1} A)) (q : ℕ)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).obj
      ((kummerSiteEvaluation (ModuleCat.{u + 1} A) t).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :
    Sheaf.H (kummerSiteForget.obj F) q :=
  (Equiv.ofBijective (kummerSiteAbelianEvaluation t ht (kummerSiteForget.obj F) q)
    (kummerSiteAbelianEvaluation_bijective t ht (kummerSiteForget.obj F) q)).symm
      ((((kummerSiteCoefficientForget A).mapDerivedCategoryPlusHomologyFunctorIso q).hom.app
            ((kummerSiteEvaluation (ModuleCat.{u + 1} A) t).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).map
          (kummerSiteDerivedScalarMap t F)) x)

/-- The specified scalar-forgetting map is bijective without flatness or preservation of
injectives by coefficient forgetting. Source: Stacks, 03FD
(blueprint: def-pur-kummer-site-cohomology-normalization).
Proof: a module-injective resolution becomes an abelian evaluation-acyclic resolution
by Tag 03FD. The canonical derived comparison therefore is an isomorphism, computed
by the same evaluated complex on both sides. Exact coefficient forgetting commutes
with homology. Compose these bijections with the inverse abelian evaluation bijection. -/
theorem kummerSiteScalarMap_bijective (t : C) (ht : IsTerminal t)
    (F : Sheaf J (ModuleCat.{u + 1} A)) (q : ℕ) :
    Function.Bijective (kummerSiteScalarMap t ht F q) := by
  sorry

end Site

/-- Module cohomology on the small etale site by terminal evaluation.
Source: Stacks, 01FT (blueprint: def-pur-kummer-site-cohomology-normalization). -/
abbrev kummerSiteEtaleH (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ) :
    ModuleCat.{u + 1} A :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).obj
    ((kummerSiteEvaluation (ModuleCat.{u + 1} A)
      (Scheme.Etale.mk (𝟙 T))).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))

/-- Module cohomology on the small pro-etale site by terminal evaluation.
Source: Stacks, 01FT/099W (blueprint: def-pur-kummer-site-cohomology-normalization). -/
abbrev kummerSiteProEtaleH (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) (q : ℕ) :
    ModuleCat.{u + 1} A :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).obj
    ((kummerSiteEvaluation (ModuleCat.{u + 1} A)
      ((Scheme.toProEt T).obj (Scheme.Etale.mk (𝟙 T)))).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))

/-- Hq of the actual derived-unit comparison, with its canonical exact-functor
single-object identification. Source: Stacks, 099W
(blueprint: def-pur-kummer-site-cohomology-normalization). -/
def kummerSiteComparison (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ) :
    kummerSiteEtaleH T A F q ⟶ kummerSiteProEtaleH T A
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F) q :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).map
    ((Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} A)).inv.app _ ≫
      (finiteComparisonGlobalSections T A).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      (kummerSiteEvaluation (ModuleCat.{u + 1} A)
        ((Scheme.toProEt T).obj (Scheme.Etale.mk (𝟙 T)))).rightDerivedFunctorPlus.map
          (((comparisonUpperStar
            (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlusSingleFunctor 0).hom.app F))

/-- The etale module Kummer class is the inverse scalar-forgetting image of the ordinary
Kummer boundary followed by the existing pure-tensor coefficient morphism.
Source: Stacks, 03PL/03FD (blueprint: def-pur-kummer-site-cohomology-normalization). -/
def kummerSiteEtaleClass (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (hm : IsUnit (m : Γ(T, ⊤))) (w : Γ(T, ⊤)ˣ) :
    kummerSiteEtaleH T A (Scheme.finiteEtaleTateSheaf A m T hA 1) 1 :=
  (Equiv.ofBijective
    (kummerSiteScalarMap (Scheme.Etale.mk (𝟙 T))
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)
      (Scheme.finiteEtaleTateSheaf A m T hA 1) 1)
    (kummerSiteScalarMap_bijective (Scheme.Etale.mk (𝟙 T))
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)
      (Scheme.finiteEtaleTateSheaf A m T hA 1) 1)).symm
        (Etale.relativeKummerClass A m hA T hm w)

/-- The pro-etale abelian Kummer class uses the abelian comparison pullback first and
then its canonical scalar-forgetting coefficient isomorphism.
Source: Stacks, 099W/03PL (blueprint: def-pur-kummer-site-cohomology-normalization). -/
def kummerSiteProAbelianClass (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (hm : IsUnit (m : Γ(T, ⊤))) (w : Γ(T, ⊤)ˣ) :
    Sheaf.H (kummerSiteForget.obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (Scheme.finiteEtaleTateSheaf A m T hA 1))) 1 :=
  Sheaf.H.map ((forgetComparisonIso A T).hom.app
    (Scheme.finiteEtaleTateSheaf A m T hA 1)) 1
      (comparisonCohomologyMap T
        (kummerSiteForget.obj (Scheme.finiteEtaleTateSheaf A m T hA 1)) 1
          (Etale.relativeKummerClass A m hA T hm w))

/-- The pro-etale module Kummer class is the inverse scalar-forgetting image of the
specified pro-etale abelian class, for every scheme.
Source: Stacks, 03FD/099W (blueprint: def-pur-kummer-site-cohomology-normalization). -/
def kummerSiteProEtaleClass (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (hm : IsUnit (m : Γ(T, ⊤))) (w : Γ(T, ⊤)ˣ) :
    kummerSiteProEtaleH T A
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (Scheme.finiteEtaleTateSheaf A m T hA 1)) 1 :=
  (Equiv.ofBijective
    (kummerSiteScalarMap ((Scheme.toProEt T).obj (Scheme.Etale.mk (𝟙 T)))
      ((MorphismProperty.Over.mkIdTerminal
        @AlgebraicGeometry.Etale T).isTerminalObj (Scheme.toProEt T))
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (Scheme.finiteEtaleTateSheaf A m T hA 1)) 1)
    (kummerSiteScalarMap_bijective ((Scheme.toProEt T).obj (Scheme.Etale.mk (𝟙 T)))
      ((MorphismProperty.Over.mkIdTerminal
        @AlgebraicGeometry.Etale T).isTerminalObj (Scheme.toProEt T))
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (Scheme.finiteEtaleTateSheaf A m T hA 1)) 1)).symm
          (kummerSiteProAbelianClass T A m hA hm w)

end AlgebraicGeometry.ProEtale
