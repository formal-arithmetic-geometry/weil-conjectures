/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveInjective
import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveSurjective

@[expose] public section

universe w uA vA

open CategoryTheory

namespace CategoryTheory

/-- Zeroth cohomology computes maps from any derived object into an injective
object concentrated in degree zero. -/
theorem derived_homology_injective_bijective
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (I : A) [Injective I] :
    Function.Bijective
      ((DerivedCategory.homologyFunctor A 0).map :
        (K ⟶ (DerivedCategory.singleFunctor A 0).obj I) →
      ((DerivedCategory.homologyFunctor A 0).obj K ⟶
          (DerivedCategory.homologyFunctor A 0).obj
            ((DerivedCategory.singleFunctor A 0).obj I))) := by
  constructor
  · exact derived_homology_injective_injective K I
  · exact derived_homology_injective_surjective K I

end CategoryTheory
