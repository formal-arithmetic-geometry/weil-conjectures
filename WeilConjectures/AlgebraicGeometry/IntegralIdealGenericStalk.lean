/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import WeilConjectures.AlgebraicGeometry.IntegralIdealGenericStalkEquivalences
import WeilConjectures.AlgebraicGeometry.IntegralIdealAffineSections

/-!
# Nonzero ideals on integral schemes and their generic stalks

## References

* Stacks Project, Cohomology of Schemes, Lemma 01YL.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section

namespace AlgebraicGeometry.Scheme

/-- A quasi-coherent ideal `J` on an integral scheme (`Scheme.IdealSheafData`, with ideal
sheaf `J.toModules ⊆ 𝒪_X`) is nonzero exactly when its sections on every nonempty affine
open are nonzero, exactly when its generic stalk is nonzero, and exactly when its generic
stalk is the whole generic local ring, which is a field. The stalk map of the inclusion
`J.toModulesι` at the generic point is injective; equality of its image with the whole
local ring is surjectivity of this map (independent of the identification of the stalk of
`𝒪_X` as a module with `𝒪_{X,η}`). (Stacks, Tag 01YL) -/
theorem integral_ideal_generic_stalk (X : Scheme.{u}) [IsIntegral X]
    (J : X.IdealSheafData) :
    IsField (X.presheaf.stalk (genericPoint X)) ∧
      Function.Injective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace (genericPoint X)).map
          J.toModulesι).hom ∧
      (J ≠ ⊥ ↔ ∀ U : X.affineOpens, Nonempty U.1 → J.ideal U ≠ ⊥) ∧
      (J ≠ ⊥ ↔
        Nontrivial ((RingedSpace.moduleStalkFunctor X.toRingedSpace (genericPoint X)).obj
          J.toModules)) ∧
      (J ≠ ⊥ ↔
        Function.Surjective
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace (genericPoint X)).map
            J.toModulesι).hom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (inferInstance : Field X.functionField).toIsField
  · exact (quasi_coherent_ideal_zero_set_affine X J).1 _
  · exact integral_ideal_nonzero_iff_affine_sections X J
  · exact (integral_ideal_nonzero_iff_generic_stalk X J).1
  · exact (integral_ideal_nonzero_iff_generic_stalk X J).2

end AlgebraicGeometry.Scheme
