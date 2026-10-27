/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FinitePerfectQuotientModelData
public import Sheaf.Paper.ConstantRealizationDerivedScalarExtension
import Sheaf.Paper.ConstantRealizationDerivedScalarExtension

/-! Bridge from the chosen completed derived change to constant realization.

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 0G7E.
(blueprint: lem-weil-pbc-finite-model-derived-change-bridge).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The selected completed derived-change functor agrees with the derived constant
realization extension on the finite model. The comparison is obtained by uniqueness
of left derived functors, after identifying the underlying ordinary tensor functors.
Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 0G7E.
(blueprint: lem-weil-pbc-finite-model-derived-change-bridge). -/
theorem finiteModel_constantScalarExtension_derivedChangeBridge
    (X : Scheme.{t}) {B C : Type t} [CommRing B] [CommRing C]
    (q : B →+* C)
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    [(koszulConstantFunctor X C).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ) :
    Nonempty
      ((completedAdicDerivedChange X (adicConstantMap X q)).obj
          (DerivedCategory.Q.obj (finiteModelConstantComplex X B P)) ≅
        (ConstantScalarRealization.derivedExtension (ProEt.topology X)
          (RingHom.ulift.{t + 1, t + 1} q)).obj
          ((commutativeSiteDerivedConstantModuleFunctor (ProEt.topology X)
            (ULift.{t + 1} B)).obj
            (DerivedCategory.Q.obj
              (((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                ModuleCat.restrictScalars.{t + 1}
                  (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).mapHomologicalComplex
                    (.up ℤ)).obj P)))) := by
  sorry

end AlgebraicGeometry.Scheme
