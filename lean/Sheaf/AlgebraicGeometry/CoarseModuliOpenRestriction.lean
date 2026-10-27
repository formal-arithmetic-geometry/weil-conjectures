module

public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Restriction of a coarse moduli scheme to an open substack

Source: Stacks Project, Tags 0DUT and 0DUV, with Tag 06FJ for open substacks
(blueprint: lem-sfb-coarse-moduli-open-restriction).

The equivalence is over the original stack, and the restricted coarse morphism
is its composite with the actual second projection of the 2-fibre product.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- An open of the coarse scheme, with its inherited structure map to the base.
Source: Stacks, Tags 0DUT and 06FJ
(blueprint: lem-sfb-coarse-moduli-open-restriction). -/
def coarseOpenOver {S : Scheme.{u}} (Q : Over S) (V : Q.left.Opens) : Over S :=
  Over.mk (V.ι ≫ Q.hom)

/-- The canonical inclusion of the open coarse subscheme over the original base.
Source: Stacks, Tags 0DUT and 06FJ
(blueprint: lem-sfb-coarse-moduli-open-restriction). -/
def coarseOpenInclusion {S : Scheme.{u}} (Q : Over S) (V : Q.left.Opens) :
    coarseOpenOver Q V ⟶ Q :=
  Over.homMk V.ι rfl

/-- A finite-type DM stack with finite diagonal and a coarse scheme has a unique
open coarse subscheme pulling back to the specified open substack. Its second
projection is coarse, including the categorical and geometric-point clauses.
Source: Stacks, Tags 0DUT, 0DUV and 06FJ
(blueprint: lem-sfb-coarse-moduli-open-restriction).

Proof: (1) lem-sfb-keel-mori-uniform-topological-moduli gives an algebraic-space
uniform categorical quotient and a universal homeomorphism, using the finite diagonal.
(2) The categorical properties of this quotient and of the given coarse scheme give
mutually inverse maps between them: their composites are identities by uniqueness.
Thus the given coarse map is uniform categorical and a homeomorphism on points.
(3) By lem-sfb-stack-topology-open-substacks, the image of the open substack is an open
V of Q. Its inverse image is precisely the specified open substack. Classification
of open substacks gives the equivalence over X; bijectivity on points gives uniqueness
of V. (4) The inclusion V → Q is flat, since its local ring maps are isomorphisms.
Uniform categoricity therefore gives unique factorization to every algebraic space
for the second projection. (5) For every algebraically closed extension Ω/k, the
geometric isomorphism classes in the pullback are precisely those classes whose image
in Q(Ω) lies in V(Ω). Restrict the original coarse bijection to these subsets.
Together (4) and (5) give IsCoarseModuliScheme for the specified restriction. -/
theorem coarseModuli_open_restriction (k : Type u) [Field k]
    (X : BasedCategory.{v₁, w₁} (Over (Spec (.of k))))
    (hX : IsDeligneMumfordModuliStack X) (hft : HasFiniteTypeEtaleModuliAtlas X)
    (hdiag : HasFiniteModuliDiagonal X)
    (Q : Over (Spec (.of k))) (q : BasedFunctor X (discreteModuli (yoneda.obj Q)))
    (hq : IsCoarseModuliScheme X Q q) (U : OpenModuliSubstack X) :
    ∃! V : Q.left.Opens,
      ∃ e : BasedFunctor U.category
          (moduliTwoFiberProduct q (discreteModuliMap (yoneda.map (coarseOpenInclusion Q V)))),
        e.toFunctor.IsEquivalence ∧
          Nonempty (ModuliTwoIso
            (e.comp (moduliTwoFiberFst q
              (discreteModuliMap (yoneda.map (coarseOpenInclusion Q V)))))
            (fullModuliInclusion X U.property)) ∧
          IsCoarseModuliScheme U.category (coarseOpenOver Q V)
            (e.comp (moduliTwoFiberSnd q
              (discreteModuliMap (yoneda.map (coarseOpenInclusion Q V))))) := by
  sorry

end CategoryTheory
