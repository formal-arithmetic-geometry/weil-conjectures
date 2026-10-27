/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FinitePerfectQuotientModelData
public import Sheaf.Paper.ConstantRealizationDerivedScalarExtension
import Sheaf.Paper.ConstantRealizationDerivedScalarExtension

/-! Lifted constant-realization scalar comparison.

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E and 093J.
(blueprint: lem-weil-pbc-finite-model-lift-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Derived constant realization of the lifted complex is the lifted finite model
of ordinary scalar extension. This is the termwise balanced-tensor comparison,
transported through the derived localization.
Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E and 093J.
(blueprint: lem-weil-pbc-finite-model-lift-comparison). -/
theorem finiteModel_constantScalarExtension_liftComparison
    (X : Scheme.{t}) {B C : Type t} [CommRing B] [CommRing C]
    (q : B →+* C)
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    [(koszulConstantFunctor X C).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ) :
    Nonempty
      ((ConstantScalarRealization.derivedExtension (ProEt.topology X)
          (RingHom.ulift.{t + 1, t + 1} q)).obj
          ((commutativeSiteDerivedConstantModuleFunctor (ProEt.topology X)
            (ULift.{t + 1} B)).obj
            (DerivedCategory.Q.obj
              (((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                ModuleCat.restrictScalars.{t + 1}
                  (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).mapHomologicalComplex
                    (.up ℤ)).obj P))) ≅
        DerivedCategory.Q.obj
          (finiteModelConstantComplex X C
            (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P))) := by
  sorry

end AlgebraicGeometry.Scheme
