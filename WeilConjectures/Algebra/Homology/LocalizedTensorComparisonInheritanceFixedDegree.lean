/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonGenerators
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosure
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration

/-!
# Fixed-degree tensor inheritance for localized cohomology comparisons

## References

* Stacks Project, Tag 0DJA(1), local computation using Tag 0BYJ (perfect.tex)
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

/-- Fixed-degree local computation underlying tensor inheritance: the single-degree component
assembled by `localizedTensorComparison_inheritance`. -/
theorem localizedTensorComparison_inheritance_fixed_degree
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    (hC : Module.Flat (A ⊗[R] B) C)
    (U Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (N : CochainComplex (ModuleCat.{u} C) ℤ)
    (hU : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} B)
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    ∀ (t : F.obj Q ⟶ N)
      (m : BaseDerivedTensorCohomologyModel R A B Q C)
      (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C)
      (i : ℤ),
      (∀ j : ℤ, IsIso (m.localizedComparison j ≫ HomologicalComplex.homologyMap t j)) →
      IsIso (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
        ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (ModuleCat.{u} B)
  dsimp
  intro t m mU i h
  obtain ⟨hcop, htri, hret⟩ :=
    localizedTensorComparisonProperty_closure R A B C Q N t hC hQ
  have hgen := localizedTensorComparisonProperty_generators R A B C Q N t hQ m h
  have hp := derivedModuleFreeGeneration.{u, 0} A (DerivedCategory.Q.obj U)
    (localizedTensorComparisonProperty R A B C Q N t) hgen hcop htri hret
  exact hp U ⟨Iso.refl _⟩ hU mU i

end ModuleCat
