/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.SixFunctors.IntegralTensorShiftProperties

/-! # Addition of the completed tensor shifts on good representatives

Source: Stacks 011G, 014E and 0941; the representative calculation in
lem-pur-completed-tensor-prescribed-slot-shift-laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry

namespace WeilConjectures.IntegralSystemRealization

attribute [local irreducible] HasDerivedCategory.standard
  integralCompletedTensor
attribute [local instance 3000] integralTowerHasDerivedCategory
set_option backward.defeqAttrib.useBackward true

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Addition of normalized comparisons on pairs of flat-term K-flat complexes.
Only the representative component identities are asserted here: neither descent to
arbitrary derived objects nor the zero law is assumed.
Source: Stacks 011G (shifted cochain differentials), 014E (the cone differential)
and 0941; the good-model calculation in the parent node's proof.
(blueprint: lem-pur-completed-tensor-shift-add-on-good).

Proof: apply the hypotheses hsl and hsr at a, b and a+b.
Shifts preserve the good-model predicate. At each finite level, compare the direct
shift with the composite after the input shift-addition map. In the first slot
both maps are unsigned reindexing. In the second slot their coefficients on
first degree i are (-1)^((a+b)i) and (-1)^(ai)(-1)^(bi), which coincide for all
integers. Tensor generators determine the maps, and the transition squares in
the normalized tower comparisons make this an equality of tower maps. Projection
to each factor proves the corresponding equality of product maps. For the cone,
compare its two summands: the target summand has coefficient 1 and the source
summand has coefficients (-1)^(a+b) and (-1)^a(-1)^b. These agree, so cone
extensionality gives the equality before shifting by -1. The associativity and
commutation identities of integer shifts carry it through that final shift.
Localize the resulting chain identity and substitute the three representative
normalization squares. Naturality moves the input Q shift comparisons past the
tensor maps; coherence of Q.commShiftIso combines them. Cancel the invertible
input comparisons and shifted good-model comparisons. The resulting two
identities are exactly the displayed equations. This argument includes zero
and negative a,b and imposes no boundedness, nonemptiness, or invertibility
condition on the scheme. -/
theorem completedTensorShift_add_on_good (W : Scheme.{u})
    (sl : ∀ r : ℤ, tensorShiftFirst (Integral l E W) r ⋙ integralCompletedTensor l E W ≅
      integralCompletedTensor l E W ⋙ shiftFunctor (Integral l E W) r)
    (sr : ∀ r : ℤ, completedTensorShiftSecond (Integral l E W) r ⋙
      integralCompletedTensor l E W ≅
        integralCompletedTensor l E W ⋙ shiftFunctor (Integral l E W) r)
    (hsl : ∀ r : ℤ, integralTensorLeftProperty l E W r (sl r))
    (hsr : ∀ r : ℤ, integralCompletedTensorRightShiftProperty l E W r (sr r))
    (a b : ℤ) (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    let T := integralCompletedTensor l E W
    let M : Integral l E W := DerivedCategory.Q.obj P.obj
    let N : Integral l E W := DerivedCategory.Q.obj Q.obj
    ((sl (a + b)).hom.app (M, N) =
      T.map ((shiftFunctorAdd (Integral l E W) a b).hom.app M, 𝟙 N) ≫
        (sl b).hom.app (M⟦a⟧, N) ≫
        (shiftFunctor (Integral l E W) b).map ((sl a).hom.app (M, N)) ≫
        (shiftFunctorAdd (Integral l E W) a b).inv.app (T.obj (M, N))) ∧
    ((sr (a + b)).hom.app (M, N) =
      T.map (𝟙 M, (shiftFunctorAdd (Integral l E W) a b).hom.app N) ≫
        (sr b).hom.app (M, N⟦a⟧) ≫
        (shiftFunctor (Integral l E W) b).map ((sr a).hom.app (M, N)) ≫
        (shiftFunctorAdd (Integral l E W) a b).inv.app (T.obj (M, N))) := by sorry

end WeilConjectures.IntegralSystemRealization
