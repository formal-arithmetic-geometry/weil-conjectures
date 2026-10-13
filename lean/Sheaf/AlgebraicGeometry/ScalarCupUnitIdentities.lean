/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.ScalarUnitCohomologyCoordinates
import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import Sheaf.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality

/-! # Cup with one on one scheme is the identity on structure-sheaf H1

Source: Stacks Project, Cohomology, Tags 0FKU and 01F7.
(blueprint: lem-sc-scalar-cup-unit-identities).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

noncomputable local instance instScalarCupUnitIdentitiesMonoidal (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} X.ringCatSheaf) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- Cup with the canonical class of one is the identity on structure-sheaf H¹.
Source: Stacks Project, Cohomology, section-cup-product, Lemma 20.31.1 (Tag 0FKU).
(blueprint: lem-sc-scalar-cup-unit-identities).

Proof: Evaluate morphisms from the structure sheaf at one in an injective resolution.
The augmentation representing the canonical degree-zero class corresponds to the
identity of the structure sheaf in degree-zero Ext. After restriction to k-vector
sheaves and precomposition by the scalar unit, its scalar Ext class is mk₀ of
scalarUnitMorphism. Expand scalarExtCup. Tensoring this degree-zero morphism on
either side and composing with scalarTensorCoefficient and the structure-sheaf
unitor gives the identity on the other coefficient: on sections the two composites
send s tensor one and one tensor s to s. The tensor universal property and the
sheafification adjunction give these equalities on sheaves. Naturality of the
unitors for exact-functor transport on Ext, and associativity of Ext composition,
and equality of the two unitors at the tensor unit
therefore reduce both products to the original Ext class. The cohomology-to-Ext
comparison is natural in coefficients, so transport this equality back along its
injective equivalence. Degree zero introduces no sign. This argument uses neither
an acyclic cover nor quasi-coherence. -/
theorem scalar_cup_unit_identities (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) :
    let U := SheafOfModules.unit X.ringCatSheaf
    (∀ a : scalarCohomology f U 1,
      scalarCohomologyMap f (λ_ U).hom 1
        (scalarCohomologyCup f U U 1 0 a (scalarUnitCohomologyClass f)) = a) ∧
    (∀ a : scalarCohomology f U 1,
      scalarCohomologyMap f (λ_ U).hom 1
        (scalarCohomologyCup f U U 0 1 (scalarUnitCohomologyClass f) a) = a) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
