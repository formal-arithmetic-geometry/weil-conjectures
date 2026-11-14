/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
import WeilConjectures.AlgebraicGeometry.ScalarCupZeroGlobalSections
import WeilConjectures.AlgebraicGeometry.ScalarPullbackZeroGlobalSections
import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # Degree-zero external cup on ordinary sections

## References

* Stacks Project, Tags 01DZ, 01F7, 0FKV and 0BED
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

/-- Degree-zero external cup is the tensor of the two pulled-back sections
(Stacks, Tags 01DZ, 01F7, 0FKV and 0BED). -/
theorem externalCup_zero_globalSections
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules)
    (a : scalarCohomology f F 0) (b : scalarCohomology g G 0) :
    scalarGlobalSectionsEquiv (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)
        (externalCup f g F G 0 0 a b) =
      externalGlobalSectionsTensor f g F G
        (scalarGlobalSectionsEquiv f F a ⊗ₜ[k] scalarGlobalSectionsEquiv g G b) := by
  unfold externalCup
  rw [scalarCohomologyCup_zero_globalSections,
    scalarCohomologyPullback_zero_globalSections,
    scalarCohomologyPullback_zero_globalSections]
  rfl

end AlgebraicGeometry.Scheme.Modules
