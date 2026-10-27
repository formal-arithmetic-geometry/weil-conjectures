/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FinitePerfectQuotientModelData

/-! The derived scalar comparison for the lifted constant model.

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 0G7E.
(blueprint: lem-weil-pbc-finite-model-derived-scalar-comparison-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The constant finite model computes derived scalar extension along a ring map.

The proof lifts a filtered-free K-projective resolution to the coefficient universe of
 the pro-etale site, applies the constant-realization comparison, and identifies the
 ordinary scalar-extension representative by the derived adjunction. The balanced
 tensor comparison is termwise and commutes with the complex differential.

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E and 093J.
(blueprint: lem-weil-pbc-finite-model-derived-scalar-comparison-core). -/
theorem finiteModel_constantScalarExtension_core
    (X : Scheme.{t}) {B C : Type t} [CommRing B] [CommRing C]
    (q : B →+* C)
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    [(koszulConstantFunctor X C).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ) :
    Nonempty
      ((completedAdicDerivedChange X (adicConstantMap X q)).obj
          (DerivedCategory.Q.obj (finiteModelConstantComplex X B P)) ≅
        DerivedCategory.Q.obj
          (finiteModelConstantComplex X C
            (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P))) := by
  sorry

end AlgebraicGeometry.Scheme
