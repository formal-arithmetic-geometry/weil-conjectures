/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

/-!
# Topological invariance of the small pro-étale topos

Let `r : X ⟶ Y` be a universal homeomorphism of schemes. Base change `V ↦ V ×_Y X` along `r`
identifies the schemes weakly étale over `Y` with those weakly étale over `X`, preserving and
reflecting pro-étale coverings, because `r` and all its base changes are homeomorphisms. Hence
the pushforward `r_*` and the pullback `r^*` are mutually quasi-inverse equivalences of the
categories of pro-étale sheaves. This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`, where the
corresponding statement for the small étale site is [Stacks 04DZ].

## Main statements

- `AlgebraicGeometry.ProEtale.isEquivalence_lowerStar_of_isUniversalHomeomorphism`: the
  pushforward along a universal homeomorphism is an equivalence of categories of pro-étale
  sheaves.
- `AlgebraicGeometry.ProEtale.isEquivalence_upperStar_of_isUniversalHomeomorphism`: so is the
  pullback, being left adjoint to it.

## Implementation notes

`ProEtale.isEquivalence_lowerStar_of_isUniversalHomeomorphism` is the only input of this file
that is not formal, and it is still `sorry`: the equivalence of the small pro-étale sites,
which for the small étale site is `AlgebraicGeometry.Scheme.Hom.isEquivalence_etale`, is not
available for weakly étale morphisms yet.
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}} (r : X ⟶ Y) [IsUniversalHomeomorphism r]

/-- **Topological invariance of the small pro-étale topos**: for a universal homeomorphism
`r : X ⟶ Y`, the pushforward `r_*`, restriction along base change `V ↦ V ×_Y X`, is an
equivalence between the categories of `A`-valued pro-étale sheaves on `X` and on `Y`. Base
change is an equivalence of the small pro-étale sites which preserves and reflects
coverings, since `r` and every base change of `r` is a homeomorphism
(blueprint: `sk-i-topology`). -/
theorem isEquivalence_lowerStar_of_isUniversalHomeomorphism : ((r)_*[A]).IsEquivalence :=
  sorry

/-- **Topological invariance of the small pro-étale topos**: for a universal homeomorphism
`r : X ⟶ Y`, the pullback `r^*` is an equivalence between the categories of `A`-valued
pro-étale sheaves on `Y` and on `X`, being left adjoint to the equivalence `r_*`
(blueprint: `sk-i-topology`). -/
theorem isEquivalence_upperStar_of_isUniversalHomeomorphism : ((r)^*[A]).IsEquivalence :=
  have := isEquivalence_lowerStar_of_isUniversalHomeomorphism A r
  (upperStarLowerStarAdjunction A r).isEquivalence_left_of_isEquivalence_right

end AlgebraicGeometry.ProEtale
