/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PointTateFiberCanonicalComparisons

/-! # Common-stage coherence of the constructed signed Tate line maps

Source: coefficient comparison lemma, step 6.
(blueprint: lem-pur-point-tate-common-stage-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] AlgebraicGeometry.Scheme.residueLisseAlgebraHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings TensorProduct
namespace WeilConjectures.PointTateFiber

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]


/-- The comparison between two signed Tate presentations has its canonical
representative at every common finite coefficient stage, before applying the point fibre.

Source: coefficient comparison lemma, steps 3--6; the canonical tower formulas of
signed line scalar extension and the common-stage category definition.
(blueprint: lem-pur-point-tate-common-stage-coherence).

Proof: the normalized ordinary signed scalar maps compose along coefficient towers:
at degree zero use the coefficient map, at degree one keep the root tensor, and
for positive powers tensor the formula. For negative powers evaluate on the
positive generator; nondegeneracy gives the same composition identity.
The ordinary/completed model isomorphism preserves all pure tensors, so transports
this identity to canonicalSheaf. The completion comparison is natural and the
point-free completed scalar associator is its conjugate of the ordinary tensor
associator. Thus the completedLineComparison isomorphisms satisfy the same tower
identity. Restrict to constructible objects and rationalize; the specified object
equalities in rationalLineComparison and stageLineComparison transport this tower
identity to the recorded stage system. Transport the representative defining
twistPairComparison from L to a common stage M. The resulting composite is the
F-to-M line map followed by the inverse L-to-M map: the two copies of the
L-to-M image of the identity-stage comparison cancel, and the tower equation
combines the remaining F-to-L and L-to-M maps. The common-stage equivalence
relation identifies these representatives, proving the stated source morphism
equality. This also covers M=L and the identity extension. -/
theorem canonicalCommonStage (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (F L M : Padic.FiniteCoefficientFields l Ω) (hFL : F ≤ L)
    (hFM : F ≤ M) (hLM : L ≤ M) (m : ℤ) :
    twistPairComparison D l hl Ω F L hFL m (canonicalSheaf D l hl) =
      StageSystem.PairCategory.mkHom M hFM hLM
        ((stageLineComparison D l hl Ω F M hFM m (canonicalSheaf D l hl)).hom ≫
          (stageLineComparison D l hl Ω L M hLM m (canonicalSheaf D l hl)).inv) := by sorry

end WeilConjectures.PointTateFiber
