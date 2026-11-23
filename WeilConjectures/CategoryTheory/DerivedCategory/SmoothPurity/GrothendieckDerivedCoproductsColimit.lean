/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import all WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.CategoryTheory.DerivedModuleDirectSums

/-! # Statements of the new targets (batch 2) about `GrothendieckDerivedCoproducts`

Kept in their own module so that `Sheaf.CategoryTheory.GrothendieckDerivedCoproducts`,
which the first task's targets use, is unchanged.
-/

@[expose] public section

universe t u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Termwise coproducts of arbitrary unbounded cochain complexes compute coproducts
in the derived category of a Grothendieck abelian category, with the specified
termwise coprojections. No nonemptiness or boundedness assumption is made.

Source: Stacks Project, Injectives, Tag 07D9, Lemma,
assertions (1)-(2). -/
theorem isColimit_mapCocone_grothendieckSum
    (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [HasDerivedCategory.{t} A] (I : Type w) (K : I → CochainComplex A ℤ) :
    Nonempty (IsColimit ((Q (C := A)).mapCocone
      (HomologicalComplex.coconeOfHasColimitEval (Discrete.functor K)))) := by
  classical
  let : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{w}
  have : PreservesColimit (Discrete.functor K) (Q (C := A)) := by
    apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K)
    refine (isColimitMapCoconeCofanMkEquiv _ _ _).symm ?_
    simpa using (CategoryTheory.derivedCoproductCofan I (fun i ↦ Q.obj (K i))
      K (fun i ↦ Iso.refl _)).some
  exact ⟨isColimitOfPreserves (Q (C := A))
    (HomologicalComplex.isColimitCoconeOfHasColimitEval (Discrete.functor K))⟩

end DerivedCategory
