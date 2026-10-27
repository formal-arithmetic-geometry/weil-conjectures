/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B8
-/
module

public import Sheaf.Paper.IntegralDirectImageTowerData

import Sheaf.Paper.TowerCompactSupportProjectionFormula
import Sheaf.Paper.SmoothPurityReductionDerivedMonoidalTower
import Sheaf.Paper.CompleteProjectionMateDescent
import Sheaf.Paper.CompleteCompactificationLimitRealization
import Sheaf.Paper.IntegralModels
import Sheaf.Paper.IntegralTensorPullback
import Sheaf.Paper.IntegralTensorProduct
import Sheaf.Paper.SmoothPurityNormalizedEquivalence

/-! # Components of the integral direct-image tower argument -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Invertibility of the actual integral proper and open compact-support projection mates.
Source: blueprint latest direct-image.proof.md paragraph (3), final sentence.
Proof: pullback and tensor preserve bounded integral constructibility. Reduce the two inputs
and use the tower compact-support projection formula, which makes its proper counit and open
unit mates invertible. The scalar/tensor and scalar/pullback comparisons on flat-term
K-flat representatives identify the reduced integral mates with these actual strict tower
mates; quotient augmentation normalization identifies the completion units. Apply complete
projection-mate descent separately to the proper factor and to the exact open factor,
using image reconstruction for M and M tensor f* K. Each integral mate is conjugate to the
limit of the corresponding invertible tower mate by completion units. It is therefore
invertible. The compact-open map includes the invertible pullback factorization and the
proper image of the open mate. This proof does not use faithfulness of level evaluations
or monoidality of the limit. Zero inputs and empty compactifications are covered.
(blueprint: lem-sp-integral-tower-projection-mates). -/
theorem integral_projection_mates :
    ∀ (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
      (X Y : Scheme.{u}) [X.Over (Spec (.of k))]
      [Y.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of k))]
      [QuasiCompact (Y ↘ Spec (.of k))]
      [IsSeparated (Y ↘ Spec (.of k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
      (d : ℕ) [SmoothOfRelativeDimension d f],
    ∀ (c : Compactification f) (M : Constructible l E X) (K : Constructible l E Y),
        IsIso (properProjection l E c M.obj K.obj) ∧
        IsIso (compactOpenProjection l E c M.obj K.obj) := by sorry

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
