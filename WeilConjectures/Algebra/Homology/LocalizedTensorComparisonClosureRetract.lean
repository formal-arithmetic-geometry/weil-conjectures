/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.CategoryTheory.Retract
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosureRetractCore

/-!
# Retract closure of the localized tensor comparison predicate

## References

* Stacks Project, Tags 0DJA(1), 0BYJ and 09PB
-/

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

/-- The localized tensor comparison predicate is closed under retracts. -/
theorem localizedTensorComparisonProperty_closure_retracts
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) :
    ∀ {X Y : DerivedCategory (ModuleCat.{u} A)}, Retract X Y →
      localizedTensorComparisonProperty R A B C Q N t Y →
      localizedTensorComparisonProperty R A B C Q N t X := by
  intro X Y hXY hY
  exact localizedTensorComparisonProperty_retract_core R A B C Q N t hQ hXY hY

end ModuleCat
