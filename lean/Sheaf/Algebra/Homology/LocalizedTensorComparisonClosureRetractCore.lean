module

public import Sheaf.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.CategoryTheory.Retract
public import Mathlib.RingTheory.Flat.Basic
import Sheaf.Algebra.Homology.KFlatDerivedTensorAssociator

@[expose] public section
universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat
variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

/-- Core component of retract closure, with the representative and model quantifiers exposed.
Source: Stacks Project, Tag 0DJA(1), retract part.
(blueprint: lem-pc-localized-tensor-comparison-closure-retracts-core) -/
theorem localizedTensorComparisonProperty_retract_core
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    {X Y : DerivedCategory (ModuleCat.{u} A)} (hXY : Retract X Y)
    (hY : localizedTensorComparisonProperty R A B C Q N t Y) :
    ∀ (U : CochainComplex (ModuleCat.{u} A) ℤ),
    Nonempty (DerivedCategory.Q.obj U ≅ X) →
    (∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic) →
    ∀ (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C) (i : ℤ),
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    IsIso (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i) := by
  sorry
end ModuleCat
