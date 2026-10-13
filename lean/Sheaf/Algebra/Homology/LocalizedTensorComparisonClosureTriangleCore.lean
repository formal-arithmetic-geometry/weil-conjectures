module

public import Sheaf.Algebra.Homology.LocalizedTensorComparisonProperty
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

/-- The fixed-representative and fixed-model step in the triangle closure argument.
Source: Stacks Project, Tags 0DJA(1), 0BYJ and 09PB.

Proof: tensor the distinguished triangle with the K-flat representative and apply the
base-derived tensor model.  The resulting source and target long exact cohomology
sequences are connected by the canonical comparison maps.  Flatness of C over
A tensor_R B makes extension exact.  Naturality, including the connecting maps and
shifts, gives a morphism of exact sequences; the five lemma at the chosen degree
proves the displayed comparison is an isomorphism.  The construction is independent
of the chosen representative and model by the counit and associator identities.
(blueprint: lem-pc-localized-tensor-comparison-closure-triangles-core). -/
theorem localizedTensorComparisonProperty_triangle_core
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    (T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ Pretriangulated.distinguishedTriangles)
    (h1 : localizedTensorComparisonProperty R A B C Q N t T.obj₁)
    (h2 : localizedTensorComparisonProperty R A B C Q N t T.obj₂)
    (U : CochainComplex (ModuleCat.{u} A) ℤ)
    (hU : Nonempty (DerivedCategory.Q.obj U ≅ T.obj₃))
    (hUK : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic)
    (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C)
    (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    IsIso (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i) := by
  sorry

end ModuleCat
