/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.Paper.ConstantKoszulQuotientAugmentation

/-! # Derived-limit invertibility of the normalized strict augmentation

Source: Stacks Project, proetale.tex, Tag 099M, and sites-modules.tex, Tag 093M.
(blueprint: lem-u4-constant-koszul-quotient-augmentation-is-iso).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

/-- A normalized strict augmentation becomes invertible after total derived inverse
limit on a flat-term K-flat complex. This concerns strict complexes, before descent
and independently of either chosen Koszul or quotient presentation.
Source: Stacks Project, Tag 099M (lemma-naive-completion), proof; Tag 093M
(lemma-completion-flat); More on Algebra, the sequence of Koszul complexes.
(blueprint: lem-u4-constant-koszul-quotient-augmentation-is-iso).

Proof: apply noetherian_koszul_augmentation_pro_zero to A and the ordered generators.
The exterior model identifies its negative complex and diagonal transitions with the
dual of the positive tensor Koszul system. Apply the exact constant-module realization
and then extend scalars to the coefficient sheaf. The extension is flat: it is the
identity for b=false, and flat_and_quotients gives flatness and the finite quotient
identifications for b=true. Tensor with P. The zero-summand and unit normalization
identify the resulting map with the supplied augmentation: the dual complex has no
positive degrees, its degree-zero term is the unit, and the tensor coproduct inclusions
jointly determine every component. Tensor commutes with cones using the sign (-1)^p
on the shifted-source summand in P-degree p. Thus flatConstantTensorProZeroCones makes
the cone tower pro-zero and makes total right derived inverse limit invert this map.
The right-derived universal property identifies that functor with the specified rlim.
The empty list generates I=0, when the coefficient augmentation is an isomorphism;
for the zero ring all complexes vanish. No exactness of products is used. -/
theorem koszulQuotientAugmentation_isIso [IsNoetherianRing A] (b : Bool) (r : ℕ)
    (a : Fin r → A) (ha : Ideal.span (Set.range a) = I)
    (α : ringedKoszulTensorTowerFunctor (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i)) ⟶
      (reductionTower J A I b).mapHomologicalComplex (.up ℤ))
    (hα : KoszulQuotientAugmentationLaws J A I b r a α)
    (P : Cx (coefficients J A I b)) (hP : P.IsAcyclicTensorKFlat)
    (hflat : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) :
    IsIso ((rlim (coefficients J A I b)).map
      ((TQ (coefficients J A I b)).map (α.app P))) := by sorry

end CategoryTheory.ConstantCompletion
