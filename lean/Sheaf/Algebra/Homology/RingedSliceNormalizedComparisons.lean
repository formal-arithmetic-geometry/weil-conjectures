/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Algebra.Homology.RingedSliceEvaluationModels

/-! # Existence of normalized slice comparisons

Source: Stacks Project, Tags 07A4, 08J9 and 08JB
(blueprint: lem-weil-pbc-ringed-slice-normalized-comparisons).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe c v u w w' a b x y

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures MonoidalCategory

namespace CategoryTheory

attribute [local instance 20000] siteAbelianHasSheafify siteAbelianWEqualsLocallyBijective

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
  CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

/-- The normalized tensor, Hom and Koszul comparisons for exact slice restriction exist.
Source: Stacks Project, Tags 07A4, 08JB, 03EL and the total-complex Koszul exchange
(blueprint: lem-weil-pbc-ringed-slice-normalized-comparisons).

Proof: restriction preserves K-flat complexes with flat terms by the identity-ring-map
case of 07A4. On a pair of such complexes, restrict each tensor summand using 03EL,
which sends x tensor y to x tensor y. Restriction commutes with sheafification and
coproducts, so these summand maps form a natural chain isomorphism of total complexes.
The K-flat presentation of the derived category descends it to rho and gives its
specified representative square. For Hom, use a K-injective representative I of the
target. Relocalization identifies the local families L^p to I^(p+n) on both sides;
the differentials d_I h - (-1)^n h d_L coincide. Restriction preserves K-injectivity,
so localization gives eta with its two-variable naturality. The augmentation to the
fixed K-injective replacement determines the isomorphisms kappa and kappa_U uniquely,
and naturality of augmentation gives the required Hom square. Finally exchange the
summands of total tensor with the sign (-1)^(pq). Its chain-map identity follows from
the total differential, and its inverse is the reverse signed exchange. Localizing
on K-flat representatives gives the two natural symmetry families, on the original
and the slice sites. Their model squares hold by construction. These four constructions
give all fields of the comparison datum and all four normalization predicates. -/
theorem ringedSlice_normalizedComparisons
    (U : C) [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU) :
    Nonempty {d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U) // RingedSliceEvaluationNormalized.{c, v, u, w, w'} J A U S T SU TU d} := by
  sorry

end CategoryTheory
