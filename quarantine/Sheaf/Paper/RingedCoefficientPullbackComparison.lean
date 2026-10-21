/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.Paper.RingedCoefficientProjectionData

/-! # The canonical inverse-image coefficient comparison

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0G7E and 07A6
(blueprint: lem-pur-coefficient-pullback-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits
open WeilConjectures.SemilinearSections (Mod D)
namespace SheafOfModules.RingedCoefficientProjection

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}
  {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)
  {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := J) pY)
  (nX : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := K) pX)

/-- The canonical coefficient/inverse-image tensor square has normalized ordinary
and derived comparison isomorphisms.

Source: Stacks Project, Cohomology on Sites, Tag 0D6D
(lemma-derived-pullback-composition) and Tag 0G7E (lemma-pullback-K-flat);
Modules on Sites, Tags 03D2 and 03EL
(blueprint: lem-pur-coefficient-pullback-comparison).

Proof:
1. An algebraic inverse image preserves the balanced coequalizer for scalar
extension: inverse image preserves colimits, and its finite-product comparisons
transport addition and scalar multiplication. The ring naturality equation
identifies the two resulting coefficient actions. The inverse balanced pairing
gives an isomorphism of the ordinary functors. Both maps on scalar insertion
are the insertion of the inverse-image module, proving ordinary_insertion.
2. Choose a flat-term K-flat resolution. Coefficient inverse image preserves
K-flat complexes and flat terms by 0G7E. Ordinary scalar extension preserves the
appropriate acyclic K-flat comparisons. Therefore both composites are computed
on this same resolution. Localize the ordinary isomorphism, cancelling the
invertible K-flat computation counits, to obtain the derived isomorphism.
3. The localization equation is exactly Comparisons.representative: apply the
ordinary comparison to the resolved complex, and transport the two computation
counits through the canonical mapDerivedCategoryFactors isomorphisms. Naturality
in the complex and independence of resolution follow from localization
uniqueness. This is the comparison of the two factorizations in 0D6D, in the
changed coefficient category. No coefficient map is assumed flat. -/
theorem coefficientPullbackComparisons [PreservesFiniteLimits uInv] :
    Nonempty (Comparisons g nY nX) := by
  sorry

end SheafOfModules.RingedCoefficientProjection
