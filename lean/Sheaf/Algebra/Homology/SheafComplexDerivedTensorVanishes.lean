/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.Single


public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
-- r4: side KFlat instances (global there), as local instances of the live theorems
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

/-! # Derived tensor vanishing for a complex on a ringed site

Source: Stacks Project, Tags 06YS and 06YU, used in Tag 0DHY
(blueprint: def-trf-ringed-complex-derived-tensor-vanishing).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

/-- Vanishing of the derived tensor of a complex `K` with a module sheaf `F` in degree `i`.
A quasi-isomorphism from a K-flat complex supplies the derived tensor computation.
There is no boundedness requirement and the resolution is required to exist.
Source: Stacks Project, Tags 06YS and 06YU
(blueprint: def-trf-ringed-complex-derived-tensor-vanishing). -/
def sheafDerivedTensorVanishes
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u v})
    (K : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (F : SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))
    (i : ℤ) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ,
    IsAcyclicTensorKFlat (R := R) P ∧ ∃ q : P ⟶ K, QuasiIso q ∧
      IsZero ((mapBifunctor P
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory R))).homology i)

end CochainComplex
