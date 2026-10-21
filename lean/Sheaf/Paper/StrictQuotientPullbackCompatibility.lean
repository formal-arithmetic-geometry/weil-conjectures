/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q6
-/
module

public import Sheaf.Paper.StrictQuotientScalarBalancingData

/-! # Pullback coherence for strict quotient scalar balancing

Source: strict coefficient supplement, steps 4--7; Stacks Tags 03EL, 07A4 and 06YY.
(blueprint: lem-weil-pbc-strict-quotient-pullback-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.StrictScalarBalancing
open CategoryTheory.ConstantCompletion
variable {A : Type (u + 1)} [CommRing A]

/-- Canonical pullback/tensor reassociation commutes with normalized scalar balancing
as a map of derived strict towers. This concerns pullback alone; no augmentation is used.

Source: completed-exchange-coherence, strict coefficient supplement, steps 4--7;
Stacks sites-modules, Tag 03EL; sites-cohomology, Tags 07A4, 06YY and 0G7D.
(blueprint: lem-weil-pbc-strict-quotient-pullback-compatibility).

Proof:
1. Transport preservation of the finite constant ring tower from the original
pro-etale sites through the AsSmall sheaf equivalences. Their pullback comparison
is the uniqueness isomorphism of left adjoints to the same transported pushforward.
For the chosen inverseData, ringUnderlying and ring_naturality give a natural
isomorphism between rings followed by forgetting and forgetting followed by inverse.
Ring-sheaf forgetting preserves and reflects limits. Consequently the chosen rings
functor preserves this tower too. The componentwise constant isomorphisms identify
its image diagram with the target finiteSystem. Its limit comparison is completedMap,
by their common projection formula, so completedMap is invertible. The constant
coefficient map is already invertible. Naturality of constants and limit.hom_ext
make the scalar square commute. Both module pullbacks are therefore exact: algebraic
inverse image is exact and extension along a ring isomorphism is an equivalence.
Apply them termwise to diagrams and localize to construct the two universal
PullModels and their factor isomorphisms.
2. The ordinary scalar comparison is ordinaryPullComparison inverted. Its defining
insertion equation makes it an isomorphism: the two insertion maps are invertible
along the coefficient isomorphisms, and the underlying-sheaf functor reflects
isomorphisms. This is the normalized flat ringed restriction comparison. Exact
localization of this square and its termwise diagram square gives a and p, with
the stated ordinary and diagram representative formulas.
3. Apply the ordinary inverse-image tensor comparison to each quotient coefficient.
The section formula sends the pulled quotient class to the same quotient class.
Naturality in quotient maps proves compatibility with every tower transition, giving
ordinaryCompleted and ordinaryConstant with their insertion normalizations.
4. A flat-term K-flat representative remains flat-term K-flat under these pullbacks
and under flat scalar restriction. Its constant diagram is K-flat on the diagram site,
since tensor and cohomology evaluate levelwise. Resolve the quotient diagram too;
K-flatness and exact inverse image invert that auxiliary resolution. Thus the ordinary
comparisons compute the two derived reassociations tau and constantReassociation,
including precisely their DerivedTowerComparisonFormula equations.
5. On a generalized pure tensor, each composite in equation pulls the same sections
and changes the balancing ring from completed to constant, yielding the same tensor.
Pure sections determine maps out of sheaf tensors. Naturality includes differentials
and transitions, so this is equality of strict chain maps. Site-derived tensor descent
extends the comparisons and this equality from flat-term K-flat representatives.
The computation conditions on rhoV and rhoU identify their components with those same
balancing maps. Every derived object admits such a representative, giving equation
on all ambient objects. This uses no faithfulness of derived evaluation. -/
theorem strictQuotientPullbackCompatibility {U V : Scheme.{u}} (f : U ⟶ V)
    (d : AdicCoefficientDatum A)
    (ρV : reduction V d true ⋙ tdres (scalar V d) ≅
      dres (scalar V d) ⋙ reduction V d false)
    (ρU : reduction U d true ⋙ tdres (scalar U d) ≅
      dres (scalar U d) ⋙ reduction U d false)
    (hV : BalancingComputes V d ρV) (hU : BalancingComputes U d ρU) :
    Nonempty (PullCompatibility f d ρV ρU) := by
  sorry

end AlgebraicGeometry.Scheme.StrictScalarBalancing
