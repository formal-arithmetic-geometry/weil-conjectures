/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Yoneda
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Local finite presentation and directed affine limit tests

Source: Stacks Project, Limits, Tag 01ZC, Proposition
`proposition-characterize-locally-finite-presentation`, equivalence (1) and (2).
(blueprint: lem-sfb-scheme-affine-limit-lfp-criterion)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Local finite presentation is characterized by bijectivity of the canonical map from
stage morphisms to morphisms out of a directed affine limit, all over the given base.
No quasi-compactness or quasi-separatedness of the source or base is required.

The diagram `D` consists of schemes over `B`; its underlying schemes are affine.
The functor `D.rightOp ⋙ yoneda.obj (Over.mk g)` sends a stage to its set of
`B`-morphisms into `U`, with transition maps given by precomposition. Applying this
Yoneda functor to `coconeRightOpOfCone c` gives the cocone whose legs are precomposition
with the limit projections. Thus `colimit.desc` below is the canonical map, not a chosen
bijection. The category `I` is filtered because it is nonempty and directed.

Source: Stacks Project, Limits, Tag 01ZC, equivalence (1) and (2).
(blueprint: lem-sfb-scheme-affine-limit-lfp-criterion)

Proof plan from the six steps of the node:
1. Local finite presentation implies local finite type: a finite polynomial presentation
supplies finitely many algebra generators on every affine chart
[def-sbc-locally-finite-presentation, def-weil-finite-type-morphism].
2. Affine stages are quasi-compact and quasi-separated; their transitions are affine by
writing them as spectrum maps. The finite-presentation limit factorization lemma therefore
represents every limit morphism by a morphism at a stage
[lem-weil-pbc-affine-scheme-qcqs, def-weil-affine-spectrum,
lem-weil-pbc-spec-colimit-limit, lem-weil-pbc-finite-presentation-map-limit-factorization].
3. Two representatives become comparable at a common stage by directedness. The
locally-finite-type limit equality lemma makes them equal at a later stage. Hence the
colimit class of a representative is independent of choices, and defines an inverse to
the canonical map, with the identities checked on stage coprojections
[lem-weil-pbc-locally-finite-type-limit-map-equality, def-weil-pbc-category-colimit].
4. Conversely, fix affine opens `W = Spec C` in `U` and `V = Spec R` in `B`, with
`g(W)` contained in `V`. A map from `C` to a directed colimit of `R`-algebras gives a
map from the corresponding affine limit to `W`. Surjectivity of the assumed test map
represents its composite into `U` at some stage
[def-weil-affine-spectrum, lem-weil-pbc-spec-colimit-limit].
5. The inverse image of `W` at this stage pulls back to the entire limit. Eventual open
containment makes it the whole of a later stage. Restrict the resulting morphism into `W`;
monicity of the open immersions identifies it over `V` and its pullback with the original
map. The spectrum correspondence gives an `R`-algebra map to that stage
[lem-weil-pbc-limit-image-contained-in-open, lem-weil-pbc-affine-scheme-qcqs,
def-weil-open-immersion, def-weil-affine-spectrum].
6. The algebra directed-Hom criterion makes `C` finitely presented over `R`. Every point
has affine neighbourhoods `W` and `V` as above, so these charts establish local finite
presentation [lem-sfb-algebra-directed-hom-finite-presentation,
def-sbc-locally-finite-presentation]. -/
theorem locallyOfFinitePresentation_iff_affine_limit_hom_bijective
    {B U : Scheme.{u}} (g : U ⟶ B) :
    LocallyOfFinitePresentation g ↔
      ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
        (D : Iᵒᵖ ⥤ Over B),
        (∀ i : Iᵒᵖ, IsAffine (D.obj i).left) →
        ∀ c : Cone D, IsLimit c →
          Function.Bijective
            (colimit.desc (D.rightOp ⋙ yoneda.obj (Over.mk g))
              ((yoneda.obj (Over.mk g)).mapCocone (coconeRightOpOfCone c))) := by
  sorry

end AlgebraicGeometry
