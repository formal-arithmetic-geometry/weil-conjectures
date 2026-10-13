/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.KoszulOpenSystem
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # The cone of the negative Koszul tail augmentation

Source: Stacks Project, Section 36.9, Tag 08CX, opening construction
(blueprint: lem-sc-koszul-open-cone-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The cone of the tail augmentation is the full Koszul complex, compatibly
with the inclusion of its degree-zero term.
Source: Stacks Project, Section 36.9, Tag 08CX, opening construction
(blueprint: lem-sc-koszul-open-cone-comparison).

Proof: Let u be the extended tail augmentation. The cone in degree n is
I^(n+1) ⊕ A[0]^n. For n < 0 the second summand is zero and the first is
K^n; for n = 0 the first summand is zero and the second is A. For n > 0
both summands are zero. Identify the nonzero summand with K^n, using the
inverse of exteriorPower.zeroEquiv in degree zero. The inverse uses the
appropriate biproduct inclusion. The cone differential on the first
summand is the negative of the tail differential, hence the original
Koszul differential. From degree -1 to degree zero the off-diagonal cone
differential is the augmentation, which becomes the Koszul boundary under
the degree-zero identification. All other off-diagonal components vanish.
Thus these degreewise inverse maps commute with differentials and define
an isomorphism of complexes. The right cone inclusion is zero off degree
zero and in degree zero becomes precisely koszulOpenKoszulInclusion,
which proves the asserted equality of chain maps. This also covers r = 0:
the tail is zero and the cone is A[0]. For the zero ring all terms are zero
and the same construction applies. -/
theorem koszulOpen_module_cone_comparison
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) :
    let u := HomologicalComplex.extendMap (koszulOpenAugmentation A r f e)
      ComplexShape.embeddingDownNat
    ∃ c : CochainComplex.mappingCone u ≅
        (ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ (e + 1))).extend
          ComplexShape.embeddingDownNat,
      CochainComplex.mappingCone.inr u ≫ c.hom =
        HomologicalComplex.extendMap (koszulOpenKoszulInclusion A r f e)
          ComplexShape.embeddingDownNat := by sorry

end AlgebraicGeometry
