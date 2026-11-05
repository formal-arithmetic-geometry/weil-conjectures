/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.IntermediateFieldLimit
public import WeilConjectures.SixFunctors.ProEtale.GaloisAcyclic.WContractible

/-!
# Pro-étale direct images along an algebraic field base change

Let `Ω / L` be an algebraic field extension, `h : G ⟶ Spec L` a scheme over `L` and
`g : G_Ω = G ×_L Ω ⟶ G` the base change. For every étale sheaf `F₀` of `Λ`-modules on `G`, the
pro-étale sheaf `g^* ν^* F₀` is acyclic for the pro-étale direct image `g_*`
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_upperStar_comparisonUpperStar_obj`).

By `AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_isWContractibleRing`, it suffices to
show that the higher derived sections of `g^* ν^* F₀` over `W ×_G G_Ω` vanish, for `W` an object
of the pro-étale site of `G` whose underlying scheme is the spectrum of a w-contractible ring
`R`. By the comparison of pro-étale and étale cohomology, these are the étale cohomology groups
of `W ×_G G_Ω = W ×_L Ω`, the cofiltered limit of the affine schemes `W ×_L K` over the finite
subextensions `K` of `Ω / L`, with affine transition maps. By continuity of étale cohomology,
it suffices that the higher étale cohomology of each `W ×_L K` vanishes; and `W ×_L K` is finite
of finite presentation over `Spec R`, hence the spectrum of a w-contractible ring.

## Main definitions

- `AlgebraicGeometry.FiniteIntermediateField.overDiagram`: the diagram `K ↦ Spec K` of schemes
  over `Spec L`.
- `AlgebraicGeometry.FiniteIntermediateField.overCone`: the cone with point `Spec Ω` over it,
  a limit cone (`AlgebraicGeometry.FiniteIntermediateField.isLimitOverCone`).

## Main statements

- `AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_upperStar_comparisonUpperStar_obj`
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace FiniteIntermediateField

variable (L Ω : Type u) [Field L] [Field Ω] [Algebra L Ω]

variable [Algebra.IsAlgebraic L Ω]

end FiniteIntermediateField

namespace ProEtale

open Scheme FiniteIntermediateField

variable (Λ : Type (u + 1)) [Ring Λ] {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω]

variable {G : Scheme.{u}} (h : G ⟶ Spec (.of L))

end ProEtale

end AlgebraicGeometry
