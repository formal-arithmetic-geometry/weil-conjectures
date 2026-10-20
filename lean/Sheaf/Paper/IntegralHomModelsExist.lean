/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.Paper.IntegralHomReductionModels
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # Existence of normalized integral tensor-Hom models

Source: Stacks Tags 06YS, 06YU, 08J9, 08JA, 07A4 and 07A6;
blueprint order 2478, proof steps 2-3
(blueprint: lem-sf-integral-hom-models-exist).
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

/-- The ordinary uncompleted tensor and its coefficient comparisons admit the
normalizations specified by the existing presentation records. This statement does
not assert either internal-Hom reduction or preservation of completeness.

Source: Stacks Tags 06YS, 06YU, 08J9, 08JA, 07A4 and 07A6;
blueprint order 2478, steps 2-3
(blueprint: lem-sf-integral-hom-models-exist).

Proof: Resolve both factors by flat-term K-flat complexes, using the independent
coefficient-universe resolution theorem. Localize their signed total tensor in
both variables. The K-flat cone criterion makes this independent of resolutions.
For a K-injective target, sectionwise currying identifies chain maps out of total
tensor with maps into the Hom complex. Hom out of the direct sums is the product
over the first degree. Its differential is the Hom differential, so this descends
to the tensor-Hom adjunction. In the order P tensor Hom(P,I), symmetry contributes
(-1)^(i*j). On K-flat test complexes, the localization comparison is homModelMap;
this proves the evaluation field. Apply the same construction over every finite
quotient. Ordinary scalar extension preserves K-flatness, by balanced tensor
associativity and exact restriction. Its total tensor comparison is the inverse
of the map sending s tensor (x tensor y) to (s tensor x) tensor (1 tensor y).
Multiplication of coefficient factors gives the inverse. The unit formula
x maps to 1 tensor x proves the displayed local normalization. Descend this
natural chain isomorphism by the left-derived universal property of reduction.
The defining counit square is exactly the remaining normalization equation.
Use the same source presentation for every n; no bound on either input is used. -/
theorem models_exist :
    ∃ a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl),
      ∀ n : ℕ, Nonempty (ReductionPresentation l E Y D hl a n) := by sorry

end WeilConjectures.IntegralHom
