module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Yoneda
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Sheaf.RingTheory.FinitePresentationOfDirectedColimitFactorization

/-!
# Local finite presentation from surjectivity on affine limit points

Source: Stacks Project, Limits, Tag 0CM0, Lemma `lemma-surjection-is-enough`.
(blueprint: lem-sfb-scheme-surjective-affine-limit-criterion)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A scheme morphism is locally of finite presentation if the canonical comparison from
stage morphisms into its source to morphisms out of each directed affine limit is
surjective. The stage schemes, limit, and morphisms are all over the given base.

The functor `D.rightOp ⋙ yoneda.obj (Over.mk g)` is the diagram of sets of
`B`-morphisms from the stages to `U`. Its cocone obtained from
`coconeRightOpOfCone c` has legs given by precomposition with the limit projections.
Consequently the displayed `colimit.desc` is precisely the canonical comparison map.

Source: Stacks Project, Limits, Tag 0CM0, Lemma `lemma-surjection-is-enough`.
(blueprint: lem-sfb-scheme-surjective-affine-limit-criterion)

Proof plan:
1. Fix affine opens `W = Spec C` in `U` and `V = Spec R` in `B` with `g(W)`
contained in `V`. For a directed system of `R`-algebras `A_i` with colimit `A`, an
`R`-algebra map `C → A` gives a `V`-map `Spec A → W`. The spectrum-colimit theorem
identifies `Spec A` with the limit of the affine schemes `Spec A_i`, whose maps to
`V` also make them schemes over `B`
[def-weil-affine-spectrum, lem-weil-pbc-spec-colimit-limit].
2. Compose into `U` and apply the surjectivity hypothesis. Every set-colimit element
has a stage representative, so some `B`-map `b_i : Spec A_i → U` pulls back to the
given map into `U` [lem-weil-pbc-filtered-colimit-sets-elementwise].
3. The inverse image of `W` under `b_i` pulls back to the whole limit. Affine stages
are quasi-compact and transitions are affine. Eventual open containment therefore
makes this inverse image the whole of some later stage; the open itself need not be
quasi-compact [lem-weil-pbc-affine-scheme-qcqs,
lem-weil-pbc-limit-image-contained-in-open].
4. Restrict the later-stage map into `W`. Monicity of `V → B` makes it a `V`-map,
and monicity of `W → U` identifies its limit pullback with the original map. The
spectrum correspondence gives an `R`-algebra map `C → A_j` factoring `C → A`
[def-weil-open-immersion, def-weil-affine-spectrum].
5. The directed-Hom algebra criterion makes `C` finitely presented over `R`.
Choose such affine neighbourhoods at every point of `U` to conclude that `g` is
locally of finite presentation [lem-sfb-algebra-directed-hom-finite-presentation,
def-sbc-locally-finite-presentation, def-pc-scheme]. -/
theorem locallyOfFinitePresentation_of_affine_limit_hom_surjective
    {B U : Scheme.{u}} (g : U ⟶ B)
    (hsurj : ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
      (D : Iᵒᵖ ⥤ Over B),
      (∀ i : Iᵒᵖ, IsAffine (D.obj i).left) →
      ∀ c : Cone D, IsLimit c →
        Function.Surjective
          (colimit.desc (D.rightOp ⋙ yoneda.obj (Over.mk g))
            ((yoneda.obj (Over.mk g)).mapCocone (coconeRightOpOfCone c)))) :
    LocallyOfFinitePresentation g := by
  sorry

end AlgebraicGeometry
