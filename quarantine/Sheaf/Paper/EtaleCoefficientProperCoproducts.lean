/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.Paper.EtaleCoefficientSystemAdjoint

public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Proper coproducts in the constant ring-sheaf coefficient presentation

Source: Stacks 0F0D; Zheng, Construction 4.1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry

/-- The proper finite-coefficient coproduct theorem is unchanged by the normalized
ringed-site presentation of a quotient coefficient level and the chosen derived models.
Source: Stacks 0F0D; Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-proper-coproducts).

Proof: identify modules over the constant quotient ring sheaf with sheaves of modules
in the quotient ring. The normalized inverse-image comparison identifies the level
inverse image with the usual étale inverse image under these equivalences. Adjoint
uniqueness identifies its ordinary right adjoint with the usual direct image,
compatibly with the adjunction counits. Exact equivalences induce equivalences of
unbounded derived categories. The normalized universal right-derived units then
identify D.direct with the conjugate of the usual total right derived direct image:
compute on K-injectives, or use uniqueness of total right derived functors. Apply
proper_rightDerivedLowerStar_preservesCoproducts with the finite quotient ring and
the given Noetherian quasi-compact schemes. Equivalences preserve coproducts, and
preservation of colimits is invariant under natural isomorphism. Transporting that
assertion gives the result, including the empty coproduct. -/
theorem etaleCoefficientProper_coproducts
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V T : Scheme.{u}} (g : V ⟶ T) [IsProper g]
    [IsLocallyNoetherian V] [CompactSpace V]
    [IsLocallyNoetherian T] [CompactSpace T]
    (A : StrictEtaleOrdinaryImage O t g) (n : ℕ)
    [Finite (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1))]
    (D : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) D.direct := by
  sorry

end AlgebraicGeometry
