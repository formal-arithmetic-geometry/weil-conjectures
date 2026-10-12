/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure

/-! # Tensor under the standard localization comparison

Source: Stacks Project, Tags 05RU and 06YH.
(blueprint: lem-pc-derived-localization-tensor-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- The inverse standard comparison respects the K-flat derived tensor.
Source: Stacks Project, Tags 05RU and 06YH.
(blueprint: lem-pc-derived-localization-tensor-comparison).

Proof: the comparison is the unique equivalence commuting with Qh. Compute each
of the two tensors using K-flat resolutions of its arguments. The resolutions and
termwise tensor are in the same homotopy category before either localization, so
Qh comparison identifies their images. The K-flat resolution counits are inverted
by both localizations, giving the displayed isomorphism for arbitrary unbounded
arguments. Equivalently, uncurry the derived tensor into a right Kan extension
along Qh times Qh; transport this universal property through the equivalences of
its domain and codomain and use uniqueness of right Kan extensions. No
quasi-coherence or Noetherian hypothesis is needed. For the empty scheme the
same comparisons apply to the zero category; for a standard input localization
they specialize to the canonical localization self-equivalence comparisons. -/
theorem derivedLocalization_tensorComparison (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (A B : @schemeDerivedCategory X (HasDerivedCategory.standard _)) :
    Nonempty ((schemeDerivedStandardEquivalence X).inverse.obj (A ⊗ B) ≅
      (schemeDerivedStandardEquivalence X).inverse.obj A ⊗
        (schemeDerivedStandardEquivalence X).inverse.obj B) := by sorry

end AlgebraicGeometry
