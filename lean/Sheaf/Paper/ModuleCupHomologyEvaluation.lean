/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Paper.ModuleCupHomologyFunctorLinear
public import Mathlib.Algebra.Homology.SingleHomology

/-! # Canonical evaluation of derived morphisms on the single-complex generator

Source: Stacks Project, Tag 064B, Lemma 13.19.8.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable (k : Type u) [CommRing k] [HasDerivedCategory.{u} (ModuleCat.{u} k)]

/-- Apply homology to a derived morphism and evaluate on the canonical class of 1.
The generator is constructed by the single-complex homology isomorphism and the
homology factorization, without choosing a witness of an existence theorem.
Source: Stacks Project, Tag 064B, Lemma 13.19.8.
(blueprint: def-sc-module-cup-homology-evaluation) -/
def cupHomologyEvaluation (A : DerivedCategory (ModuleCat.{u} k)) (n : ℤ) :
    (DerivedCategory.Q.obj ((HomologicalComplex.single
      (ModuleCat.{u} k) (ComplexShape.up ℤ) n).obj (ModuleCat.of k k)) ⟶ A) →ₗ[k]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj A := by
  let : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).Linear k :=
    cupHomologyFunctor_linear k n
  let S := (HomologicalComplex.single
    (ModuleCat.{u} k) (ComplexShape.up ℤ) n).obj (ModuleCat.of k k)
  let c := ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).app S).inv
    ((HomologicalComplex.singleObjHomologySelfIso
      (ComplexShape.up ℤ) n (ModuleCat.of k k)).inv (1 : k))
  exact {
    toFun := fun f ↦ (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).map f c
    map_add' := by intro f g; simp [Functor.map_add]
    map_smul' := by intro r f; simp [Functor.map_smul]
  }

end
end AlgebraicGeometry.Scheme.Modules
