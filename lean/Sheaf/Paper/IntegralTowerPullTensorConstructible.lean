/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B8
-/
module

public import Sheaf.Paper.IntegralDirectImageTowerData
import Sheaf.Paper.IntegralTensorPullback
import Sheaf.Paper.IntegralTensorProduct

import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Components of the integral direct-image tower argument -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Ordinary integral pullback and tensor preserve the constant-model constructible category.
Source: blueprint latest direct-image.proof.md paragraph (3), first three sentences;
det-lem-int-tensor-pullback and det-lem-int-tensor-product.
Proof: identify spIntegralCondensed with the continuous condensed integer coefficient
presentation of DerivedNakayama.integerRing, retaining multiplication and scalar action.
Transport the existing preserves_and_completed theorem through this coefficient
identification and through leftDerivedUpperStarIsoMapDerivedCategory. Its first clause
is precisely ordinary derived pullback preservation, with no completion. Transport the
first clause of integralTensorProduct through the same coefficient identification and
the existing relative derived tensor presentation. These equivalences preserve cohomology
and finite scalar local models, so the constant-model constructibility predicates agree.
The characteristic hypotheses give p=ringChar k>0 and p≠l. No smoothness is needed.
Zero objects, empty schemes and the tensor unit have the same constructions.
(blueprint: lem-sp-integral-tower-pull-tensor-constructible). -/
theorem integral_pull_tensor_constructible
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    (∀ K : Constructible l E Y,
      constantModelBoundedConstructible (spIntegralCondensed l E) X
        ((pull l E f).obj K.obj)) ∧
    (∀ (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))] (M N : Integral l E T),
      constantModelBoundedConstructible (spIntegralCondensed l E) T M →
      constantModelBoundedConstructible (spIntegralCondensed l E) T N →
      constantModelBoundedConstructible (spIntegralCondensed l E) T
        (((tensor l E T).obj M).obj N))  := by sorry

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
