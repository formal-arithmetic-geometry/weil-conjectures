/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # The canonical underlying Hom comparison for derived coinduction

Source: Stacks Project, dualizing.tex, construction before Tag 0A70 and Tag 0A71.
(blueprint: def-trf-derived-coinduction).

The existing coinduction and underlying Hom constructions are reexported. The comparison
below has data from composition of right derived functors and exact restriction of scalars.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wA wB

open CategoryTheory

namespace ModuleCat

/-- Forgetting the B-action on derived coinduction gives ordinary RHom_A(B[0],-).
This is the canonical derived-composition comparison, using exact restriction to identify
its right derived functor with its localization functor. Coinduction preserves K-injective
complexes because it is right adjoint to exact restriction. No isomorphism is selected from
an existence theorem or specified separately on each object.
Source: Stacks Project, dualizing.tex, construction before Tag 0A70 and Tag 0A71
(blueprint: def-trf-derived-coinduction). -/
def derivedCoinductionUnderlyingComparison
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} B)] :
    derivedCoinduction f ⋙ (restrictScalars f).mapDerivedCategory ≅
      derivedCoinductionUnderlyingHom f :=
  letI := (restrictCoextendScalarsAdj.{u, u, u} f).right_adjoint_additive
  letI := (restrictCoextendScalarsAdj.{u, u, u} f).preservesKInjectiveComplexes
  Functor.isoWhiskerLeft (coextendScalars f).rightDerivedFunctor
      (restrictScalars f).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    (Functor.rightDerivedFunctorCompIso (coextendScalars f) (restrictScalars f)).symm

end ModuleCat
