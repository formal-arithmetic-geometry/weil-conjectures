/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralHomReductionModels
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # Existence of the normalized integral tensor model

This is the tensor and evaluation part of
`lem-sf-integral-hom-models-exist`.

Source: Stacks Tags 06YS, 06YU, 08J9, 08JA, 07A4 and 07A6;
blueprint order 2478, proof step 2
(blueprint: lem-sf-integral-hom-models-exist-tensor).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- A normalized tensor presentation exists.

Source: Stacks Tags 06YS, 06YU, 08J9 and 0A8X; blueprint order 2478,
proof step 2 (blueprint: lem-sf-integral-hom-models-exist-tensor).

Proof: choose flat-term K-flat resolutions in both variables and a K-injective
resolution in the target. Sectionwise currying gives the signed evaluation
formula, and localization gives the representative square. The cone criterion
makes the construction independent of the chosen resolutions.
-/
theorem tensor_presentation_exists :
    Nonempty (TensorPresentation.{t, u} Y
        (completedIntegralCommRingSheaf l E Y D hl)) := by sorry

end WeilConjectures.IntegralHom
