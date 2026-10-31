/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.K.KInjectiveHomComparisonDescent

/-! # Descent on the actual ringed sheaf-Hom models

Source: Stacks Project, Tags 0A95 and 08J7; the localization step of the ringed-forgetting
argument (blueprint: lem-sf-ringed-sheaf-hom-comparison-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe wb wa c v r d vd s
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [U.PreservesKInjectiveComplexes]
  [Abelian.HasKInjectiveResolutions (RingedTensorModules.{c, v, r} J R)]
  (ρB : ∀ (K I : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ) [I.IsKInjective],
    (derivedInternalHomOfUniverses.{c, v, r, wb} J R).obj (op (DerivedCategory.Q.obj K),
      DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj ((Functor.uncurry.obj (homComplexFunctor (R := R))).obj (op K, I)))
  (ρA : ∀ (K I : CochainComplex (RingedTensorModules.{d, vd, s} J' R') ℤ) [I.IsKInjective],
    (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R').obj (op (DerivedCategory.Q.obj K),
      DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj ((Functor.uncurry.obj (homComplexFunctor (R := R'))).obj (op K, I)))
  (nB : ∀ (K K' I I' : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ) [I.IsKInjective]
    [I'.IsKInjective]
    (f : K' ⟶ K) (g : I ⟶ I'),
    (derivedInternalHomOfUniverses.{c, v, r, wb} J R).map ((DerivedCategory.Q.map f).op,
      DerivedCategory.Q.map g) ≫ (ρB K' I').hom =
      (ρB K I).hom ≫ DerivedCategory.Q.map ((Functor.uncurry.obj (homComplexFunctor (R := R))).map
        (f.op, g)))
  (nA : ∀ (K K' I I' : CochainComplex (RingedTensorModules.{d, vd, s} J' R') ℤ) [I.IsKInjective]
    [I'.IsKInjective]
    (f : K' ⟶ K) (g : I ⟶ I'),
    (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R').map ((DerivedCategory.Q.map f).op,
      DerivedCategory.Q.map g) ≫ (ρA K' I').hom =
      (ρA K I).hom ≫ DerivedCategory.Q.map ((Functor.uncurry.obj (homComplexFunctor (R := R'))).map
        (f.op, g)))
  (chain : (Functor.uncurry.obj (homComplexFunctor (R := R))) ⋙ U.mapHomologicalComplex (.up ℤ) ≅
    ((U.mapHomologicalComplex (.up ℤ)).op.prod (U.mapHomologicalComplex (.up ℤ))) ⋙
      (Functor.uncurry.obj (homComplexFunctor (R := R'))))

include nB nA

/-- The generic descent comparison specialized to the actual ringed sheaf-Hom models.
Source: Stacks Project, Tags 0A95 and 08J7; step 5 of the ringed-forgetting comparison
(blueprint: lem-sf-ringed-sheaf-hom-comparison-descent).
Proof: apply kInjectiveHomComparisonDescent to the actual complex-Hom and derived-Hom
bifunctors on the two ringed sites, with the given representative isomorphisms, their
naturality squares, and the chain comparison. The localization factor legs in its conclusion
are exactly the factors for U, so the representative equality is unchanged. -/
theorem sheafHomComparisonDescent :
    ∃ derived : (derivedInternalHomOfUniverses.{c, v, r, wb} J R) ⋙ U.mapDerivedCategory ≅
        (U.mapDerivedCategory.op.prod U.mapDerivedCategory) ⋙
          derivedInternalHomOfUniverses.{d, vd, s, wa} J' R',
      ∀ (K I : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ) [K.IsKInjective]
        [I.IsKInjective],
        derived.hom.app (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I) ≫
            (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R').map
              (X := (op (U.mapDerivedCategory.obj (DerivedCategory.Q.obj K)),
                U.mapDerivedCategory.obj (DerivedCategory.Q.obj I)))
              (Y := (op (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj K)),
                DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj I)))
              ((U.mapDerivedCategoryFactors.inv.app K).op,
                U.mapDerivedCategoryFactors.hom.app I) ≫
            (ρA ((U.mapHomologicalComplex (.up ℤ)).obj K)
              ((U.mapHomologicalComplex (.up ℤ)).obj I)).hom =
          U.mapDerivedCategory.map (ρB K I).hom ≫
            U.mapDerivedCategoryFactors.hom.app
              ((Functor.uncurry.obj (homComplexFunctor (R := R))).obj (op K, I)) ≫
            DerivedCategory.Q.map (chain.hom.app (op K, I)) := by
  exact kInjectiveHomComparisonDescent U
    (Functor.uncurry.obj (homComplexFunctor (R := R)))
    (Functor.uncurry.obj (homComplexFunctor (R := R')))
    (derivedInternalHomOfUniverses.{c, v, r, wb} J R)
    (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R')
    ρB ρA nB nA chain

end CategoryTheory
