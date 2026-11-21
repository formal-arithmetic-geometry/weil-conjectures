/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all WeilConjectures.SixFunctors.ProEtale.InternalFirstResidueRingIso
import WeilConjectures.SixFunctors.ProEtale.InternalFirstResidueSheafPushout

/-! # The first-residue pushout of the actual coefficient rings

## References

* [Stacks, Tag 093M](https://stacks.math.columbia.edu/tag/093M)
* [Stacks, Tag 099L](https://stacks.math.columbia.edu/tag/099L)
* [Stacks, Tag 09C1](https://stacks.math.columbia.edu/tag/09C1)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint

/-- The first constant and continuous quotient maps form a pushout of ring sheaves. -/
theorem internal_first_residue_ring_pushout
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    let a := IntegralModelsStacks.scalarMap l E X ≫
      coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X
    ∃ e : Mon.mk (DerivedNakayama.quotientRing l E 1) ≅
        Mon.mk (IntegralModelsStacks.discreteObj (Padic.coefficientExtensionRing l E 1)),
      IsPushout (IntegralModelsStacks.smallMap X a)
        (IntegralModelsStacks.smallMap X (IntegralModelsStacks.residueMap l E X))
        (IntegralModelsStacks.smallMap X
          (AdicCompletion.quotient l E X 0 ≫ coefficientMap e.hom.hom X)) (𝟙 _) := by
  dsimp only
  let e := firstResidueIso l E
  refine ⟨e, internal_first_residue_sheaf_pushout l E X e ?_⟩
  have h := congrArg ((upperStarFromPoint X).map)
    (firstResidueIso_normalization l E)
  dsimp only [e, IntegralModelsStacks.scalarMap, IntegralModelsStacks.residueMap,
    coefficientMap, AdicCompletion.quotient]
  simpa only [Functor.map_comp, Category.assoc] using h

end AlgebraicGeometry.ProEtale
