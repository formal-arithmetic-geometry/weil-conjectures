/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.Algebra.Homology.RingTensorCohomology
import Mathlib.RingTheory.Localization.Basic

/-!
# Flat localization of the second derived tensor factor

Source: Stacks Project, More on Algebra, Tag 06Y6, flat cohomology base change and
comparison-map (blueprint: lem-pc-derived-tensor-flat-second-localization).
-/

set_option autoImplicit false

universe v

open CategoryTheory

namespace RingTensorCohomology

/-- Flat localization of the second factor, including naturality, both scalar actions,
and compatibility with the comparison map of Stacks Tag 06Y6.

The source and target use the models in `def-pc-ring-tensor-cohomology`. Extension of
scalars is written with C on the left of the tensor product, using the canonical symmetry
C tensor-over-B H = H tensor-over-B C. C-linearity is built into the morphism types;
the third clause is A-linearity for the A-action induced by multiplication on M. Together
these express linearity over A tensor-over-R C. The B-action is restriction of the C-action.

Proof, following the node: (1) Write C as the filtered colimit of copies of B indexed by
s in S, with a morphism t : s -> st acting by multiplication by t. This category is filtered:
use ss' as a common target, and multiply by s to equalize parallel arrows out of s.
The fractions b/s identify its colimit with C. Apply
`lem-pc-filtered-colimit-derived-tensor`, using the actions of
`lem-pc-balanced-derived-tensor-model` and the second-factor functor of
`lem-pc-derived-tensor-second-factor-functor`.
(2) Its cohomology colimit is H tensor-over-B C: x at stage s corresponds to x tensor 1/s.
Functoriality identifies the resulting isomorphism with x tensor c mapping to c times
H(M tensor-derived-over-R (B -> C))(x). It is C-linear and A-linear, and natural in M.
Flatness holds for every localization.
(3) By `lem-pc-derived-tensor-action-naturality`, comparison is induced on K-flat models
by the augmentation of the resolved second factor. The natural transformation from the
left derived functor to the ordinary tensor functor of
`lem-pc-derived-tensor-second-factor-functor` is natural for B -> C. The comparison square
therefore agrees on x tensor 1. Since these elements generate over C and all maps are
C-linear, the square commutes.
(blueprint: lem-pc-derived-tensor-flat-second-localization) -/
theorem derivedTensor_flat_second_localization
    (R A B C : Type v) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
    (S : Submonoid B) [IsLocalization S C] (hflat : (algebraMap B C).Flat) (i : ℤ) :
    (∀ M : CochainComplex (ModuleCat.{v} A) ℤ,
      IsIso (baseChangeMap R B C hflat ((resolution R).obj ((restrict R A).obj M)) i)) ∧
    (∀ (M N : CochainComplex (ModuleCat.{v} A) ℤ) (f : M ⟶ N),
      (ModuleCat.extendScalars (algebraMap B C)).map ((source R A B i).map f) ≫
          baseChangeMap R B C hflat ((resolution R).obj ((restrict R A).obj N)) i =
        baseChangeMap R B C hflat ((resolution R).obj ((restrict R A).obj M)) i ≫
          (source R A C i).map f) ∧
    (∀ (M : CochainComplex (ModuleCat.{v} A) ℤ) (a : A),
      (ModuleCat.extendScalars (algebraMap B C)).map
          ((source R A B i).map (a • 𝟙 M)) ≫
          baseChangeMap R B C hflat ((resolution R).obj ((restrict R A).obj M)) i =
        baseChangeMap R B C hflat ((resolution R).obj ((restrict R A).obj M)) i ≫
          (source R A C i).map (a • 𝟙 M)) ∧
    (∀ M : CochainComplex (ModuleCat.{v} A) ℤ,
      (ModuleCat.extendScalars (algebraMap B C)).map ((comparison R A B i).app M) ≫
          baseChangeMap R B C hflat ((restrict R A).obj ((resolution A).obj M)) i =
        baseChangeMap R B C hflat ((resolution R).obj ((restrict R A).obj M)) i ≫
          (comparison R A C i).app M) := by
  sorry

end RingTensorCohomology
