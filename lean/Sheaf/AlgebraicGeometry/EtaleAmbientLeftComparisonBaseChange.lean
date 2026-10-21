/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange

/-! # Base change of the etale compact-support composition comparison

The comparison below concerns the left adjoints, before taking a mate or evaluating at
coefficients. It uses the actual graph-normalized sum-extension comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Inverse compact-support exchange preserves the etale composition comparison.
Source: Stacks Project, Tags 0F7J and 0F7L, together with Tag 03S6
(blueprint: lem-amb-etale-left-comparison-base-change).

Proof: write the etale left comparison as the graph-normalized comparison from sum
extension to the compact-support candidate, followed by the compact-support composition
map and independence of compactification. The composition/base-change equation of
`unboundedEtaleCompactSupport_baseChange_composition` identifies the two ways to move
compact-support exchange through this composite. The graph-normalization base-change
identity identifies the remaining exchange for the etale factor with inverse sum exchange.
To identify this inverse sum exchange with the displayed inverse mate, transpose under
sum extension/restriction on both sides. Its definition as the conjugate of ordinary
inverse-image/direct-image exchange, naturality, and the two adjunction triangle identities
give exactly the canonical inverse-image square. This calculation holds on sheaves, descends
termwise to complexes, and then to the whole unbounded derived categories. Transport exact
inverse image to its canonical left-derived realization. Cancel the invertible composition
comparisons and exchanges; the resulting component equation is the displayed one.

More explicitly, refinement normalization and `N.refinement` imply
`I(d,c).hom ≫ (N.comparison u c).hom = (N.comparison u d).hom` for a proper
refinement from `c` to `d`. A common refinement and the comparison cocycle give this
identity for any two compactifications. Hence the etale left comparison can be computed
using the chosen compactification of `u`, with its graph comparison inserted before the
canonical compact-support compositor. The compositor/exchange equation then gives
`xi_uf ≫ v*(alpha.inv) = alpha'.inv ≫ F'(xi_u) ≫ xi_f(E(-))`, initially with
`xi_u` the inverse sum-exchange map. An arbitrary Cartesian square is transported to the
chosen fibre product by its unique pullback isomorphism; the inverse-image compositors
supply exactly the `J` in the statement.

To check the remaining identification of `xi_u`, let `ev` denote the sum-extension
counit. The mate counit equation to prove is
`E'(J_M) ≫ ev' = xi_u(u*M) ≫ r*(ev_M)`.
On sheaves, transpose both sides under the composite adjunction of sum extension with
inverse image. By the defining conjugate formula, the transpose of the right side is
ordinary exchange followed by the composite unit and pulled-back evaluation. Naturality
of ordinary exchange and `u*(ev) ≫ unit = id` reduce it to ordinary exchange followed
by the inverse-image unit. Expand ordinary exchange as the transpose of the commuting
inverse-image square. Naturality of that square and the inverse-image triangle identity
reduce the result to `r1_*(J_M) ≫ unit_r1`. Transposing the left side gives the same
map by the sum-extension triangle identity. Thus the adjunction bijection proves the
counit equation. Exactness and termwise derivation preserve this equation; injectivity
of the mates correspondence identifies this `xi_u` with the inverse mate displayed below.
No smoothness, section, fibre parameter, or dualizing complex enters this calculation. -/
theorem etaleAmbientLeftComparison_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X B U' X' B' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian B]
    [IsNoetherian U'] [IsNoetherian X'] [IsNoetherian B']
    (u : U ⟶ X) (f : X ⟶ B) (u' : U' ⟶ X') (f' : X' ⟶ B')
    [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    [Etale u'] [IsSeparated u'] [LocallyOfFiniteType u'] [QuasiCompact u']
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f']
    [HasCompactification (u ≫ f)] [HasCompactification (u' ≫ f')]
    [QuasiCompact f'] [QuasiCompact (u' ≫ f')]
    (v : B' ⟶ B) (r : X' ⟶ X) (r₁ : U' ⟶ U)
    (sq : IsPullback r f' f v) (sqU : IsPullback r₁ u' u r)
    (sq₁ : IsPullback r₁ (u' ≫ f') (u ≫ f) v)
    (M : DerivedCategoryModule A U) :
    letI := isIso_rightDerivedLowerShriekBaseChangeMap A sq
    letI := isIso_rightDerivedLowerShriekBaseChangeMap A sq₁
    (inv (rightDerivedLowerShriekBaseChangeMap A sq₁)).app M ≫
        (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.map
          ((etaleAmbientLeftComparison A N u f
            (HasCompactification.compactification f)
            (HasCompactification.compactification (u ≫ f))).inv.app M) =
      (etaleAmbientLeftComparison A N u' f'
        (HasCompactification.compactification f')
        (HasCompactification.compactification (u' ≫ f'))).inv.app
          ((upperStar (ModuleCat.{u + 1} A) r₁).leftDerivedFunctor.obj M) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').map
        (((mateEquiv
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) u inferInstance).ofNatIsoRight
              (leftDerivedUpperStarIsoMapDerivedCategory
                (ModuleCat.{u + 1} A) u).symm)
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) u' inferInstance).ofNatIsoRight
              (leftDerivedUpperStarIsoMapDerivedCategory
                (ModuleCat.{u + 1} A) u').symm)).symm
          (TwoSquare.mk _ _ _ _
            (((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r₁ u).symm ≪≫
              leftDerivedUpperStarComp (ModuleCat.{u + 1} A) u' r (r₁ ≫ u)
                sqU.w).hom))).natTrans.app M) ≫
      (inv (rightDerivedLowerShriekBaseChangeMap A sq)).app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).mapDerivedCategory.obj M) := by
  sorry

end AlgebraicGeometry.Etale
