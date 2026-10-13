/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.LocalizationModelSemilinear
public import Mathlib.RingTheory.Localization.Basic

/-! # Denominators for localized derived tensor cohomology

Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-first-localization-cohomology-denominators).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A Aq B D : Type u)
  [CommRing R] [CommRing A] [CommRing Aq] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra A Aq] [Algebra R Aq]
  [IsScalarTower R A Aq]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- Every localized cohomology class has a denominator and a pre-localization numerator.
Source: Stacks Project, Tags 06Y6 and 0DJ8; exactness of localization.
(blueprint: lem-pc-first-localization-cohomology-denominators).

Proof: resolve B[0] by a K-flat R-complex F and compute with Q tensor_R F.
Exact extension from A to Aq commutes with the total-complex direct sums and
with cycles modulo boundaries. Thus every class of the localized complex is a
fraction of a class of the original complex. Explicitly write a cycle as a
fraction of a term, then multiply its numerator by a further denominator killing
its differential; the resulting numerator is a cycle and the product denominator
still belongs to S. The balanced derived bifunctor's naturality in B identifies
the commuting B-action; naturality in Q and universal-counit comparison transport
the fraction equation to L and K. Under cohomologyIso_smul the denominator acts
by includeLeft (algebraMap A Aq s), and the numerator map is localizationModelMap.
For zero in S the target is zero, and s=0 works; for identity localization the
inverse model comparison supplies the numerator with denominator one. -/
theorem localizationModelMap_denominators
    (S : Submonoid A) [IsLocalization S Aq] (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (uQ : (restrict R A).obj Q ⟶ (restrict R Aq).obj ((extend A Aq).obj Q))
    (huQ : ∀ (j : ℤ) (x : Q.X j), uQ.f j x = (1 : Aq) ⊗ₜ[A,algebraMap A Aq] x)
    (y : K.cohomology i) :
    ∃ (x : L.cohomology i) (s : S),
      (Algebra.TensorProduct.includeLeft (S := R) (algebraMap A Aq (s : A)) :
        Aq ⊗[R] B) • y = localizationModelMap R A Aq B D i Q L K uQ x := by sorry

end RingTensorCohomology
