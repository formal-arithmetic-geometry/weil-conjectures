/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.CategoryTheory.Retract
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosureCoproduct
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosureTriangle
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosureRetract

/-!
# Closure of the localized tensor comparison predicate

## References

* Stacks Project, Tag 0DJA(1), using Tags 0BYJ and 09PB
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

/-- The localized tensor comparison predicate is closed under coproducts, triangles and
retracts. -/
theorem localizedTensorComparisonProperty_closure
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) :
    let P := localizedTensorComparisonProperty R A B C Q N t
    (∀ {I : Type u} (G : I → DerivedCategory (ModuleCat.{u} A))
      (S : DerivedCategory (ModuleCat.{u} A)) (ι : ∀ i : I, G i ⟶ S),
      CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofan.mk S ι) →
      (∀ i : I, P (G i)) → P S) ∧
    (∀ T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} A)),
      T ∈ Pretriangulated.distinguishedTriangles → P T.obj₁ → P T.obj₂ → P T.obj₃) ∧
    (∀ {X Y : DerivedCategory (ModuleCat.{u} A)}, Retract X Y → P Y → P X) := by
  dsimp
  exact ⟨localizedTensorComparisonProperty_closure_coproducts R A B C Q N t hQ,
    localizedTensorComparisonProperty_closure_triangles R A B C Q N t hC hQ,
    localizedTensorComparisonProperty_closure_retracts R A B C Q N t hQ⟩

end ModuleCat
