/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedPullbackLimitsAb

/-!
# The pullback of pro-étale sheaves preserves limits

For an arbitrary morphism of quasi-compact quasi-separated schemes `g : Z ⟶ Y`, the pullback
`g^*` of abelian pro-étale sheaves preserves all small limits
(`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_ab`).

The objects `V = Spec A` of `Z_proét` with `A` w-contractible cover `Z_proét`. Over such a `V`
(say `Y = Spec R` affine), the factorizations `V ⟶ W ⟶ Y` through weakly étale `Y`-schemes `W`
have an initial one, `W₀ = Spec H_R(A)` with `H_R(A) = colim B` the colimit of the étale
`R`-algebras `B` mapping to `A` (`Algebra.ClosedLift R A`): every map to an ind-étale `R`-algebra
factors uniquely through it, and every weakly étale `R`-algebra becomes ind-étale after a
faithfully flat ind-étale cover, which splits over the w-contractible `A`. Hence the presheaf
pullback (the left Kan extension along base change) takes the value `F(W₀)` on `V`, and so does
its sheafification, `V` having disjoint refinements. The sections over `V` of `g^* F` are thus
`F(W₀)`, which commutes with limits in `F`.

## References

- Bhatt–Scholze, *The pro-étale topology for schemes*, §2.2 and §4.2.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

/-- **The pullback of pro-étale sheaves preserves limits**: for a morphism `g : Z ⟶ Y` of
quasi-compact quasi-separated schemes, the pullback `g^*` of abelian pro-étale sheaves preserves
all small limits. -/
theorem preservesLimitsOfSize_upperStar_ab {Z Y : Scheme.{u}} (g : Z ⟶ Y) [CompactSpace Z]
    [QuasiSeparatedSpace Z] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    PreservesLimitsOfSize.{u + 1, u + 1} ((g)^*[Ab.{u + 1}]) :=
  sorry

end AlgebraicGeometry.ProEtale
