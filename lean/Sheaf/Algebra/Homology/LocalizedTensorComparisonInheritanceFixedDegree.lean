module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

@[expose] public section
universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

/-- Fixed-degree local computation underlying tensor inheritance.

Source: Stacks Project, perfect.tex, Tag 0DJA(1), local computation using Tag 0BYJ.
The localizing-subcategory argument, mixed-ring associator, and flat scalar-extension
comparison prove the asserted isomorphism in one cohomological degree.  This is the
single-degree component assembled by `localizedTensorComparison_inheritance`.
(blueprint: lem-pc-localized-tensor-comparison-inheritance-fixed-degree) -/
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
      (IsIso (m.localizedComparison i ≫ HomologicalComplex.homologyMap t i)) →
      IsIso (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
        ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i) := by sorry

end ModuleCat
