/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.CategoryTheory.CondensedActionModule
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-! # Exact inflation and normalized invariants of profinite condensed-group actions

Source: blueprint direct-image stability, paragraph (3), categorical input below the
partial Kummer boundary-unit calculation
(blueprint: lem-sfb-condensed-product-action-inflation).

The action categories use internal modules over the given arbitrary condensed ring.
The invariant inclusions and adjunction transposes are specified on every profinite test
object. Thus the comparison identifies the same fixed-section subsheaf.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite.CondensedAction

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

variable (G H : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- Grothendieck abelianness, exact additive inflation and normalized invariants for both
factors and their product, including the identity normalization of the conjugate comparison.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-action-inflation).

Proof:
1. Use `sk-def-sfb-sheaf-tensor` and
   `def-weil-pbc-internal-abelian-sheaf-module-equivalence` to pass from internal modules
   to sectionwise modules without changing the underlying sheaves, sections or maps.
2. The action-site presentation `lem-sfb-internal-action-site-presentation` identifies each
   action category additively with module sheaves on a small ringed site. It creates
   kernels and cokernels, and detects zero. Apply
   `lem-pur-ringed-site-grothendieck-abelian` and transport the generator, colimits and
   exact filtered colimits across this equivalence, including the trivial-group case.
3. Inflation precomposes each action with the projection and leaves the module and map
   unchanged. It is additive and preserves the preceding kernel and cokernel formulas,
   hence is exact.
4. Define fixed sections by requiring fixedness after every profinite base change. Linearity
   makes these submodules; the quantified condition gives restriction stability. Glue them
   in the original sheaf and test fixedness on the pulled-back cover to prove the sheaf
   condition. The first-factor action preserves second-factor invariants because the two
   factors commute. Restrict equivariant maps; this is an additive functor.
5. An equivariant map from an inflated object has fixed image, so restrict its codomain.
   Conversely compose a map to invariants with the inclusion. These operations are inverse
   and natural. In the product case use `(g,h)=(g,1)(1,h)` for equivariance and `(g,1)` for
   the residual action. These are exactly the transpose formulas in the specifications.
6. Direct and successive trivial inflation have the same module, action and maps. Being
   fixed by all pairs is equivalent, on every base change, to being fixed by both factors.
   Both successive and direct transposes retain the same section maps, so their conjugate
   right-adjoint comparison is the identity under the invariant inclusions. The unit law
   handles either trivial factor, and the zero ring forces every section module to be zero.
-/
theorem product_action_inflation :
    ∃ (aG : Abelian (ActionModule R G)) (aH : Abelian (ActionModule R H))
      (aGH : Abelian (ActionModule R (G × H))),
    aG.toPreadditive = actionPreadditive ∧
    aH.toPreadditive = actionPreadditive ∧
    aGH.toPreadditive = actionPreadditive ∧
    IsGrothendieckAbelian.{u + 1} (Modules R) ∧
    @IsGrothendieckAbelian.{u + 1} (ActionModule R G) _ aG ∧
    @IsGrothendieckAbelian.{u + 1} (ActionModule R H) _ aH ∧
    @IsGrothendieckAbelian.{u + 1} (ActionModule R (G × H)) _ aGH ∧
    (trivial (R := R) (P := G)).Additive ∧
    PreservesFiniteLimits (trivial (R := R) (P := G)) ∧
    PreservesFiniteColimits (trivial (R := R) (P := G)) ∧
    (trivial (R := R) (P := H)).Additive ∧
    PreservesFiniteLimits (trivial (R := R) (P := H)) ∧
    PreservesFiniteColimits (trivial (R := R) (P := H)) ∧
    (inflate (R := R) (ContinuousMonoidHom.fst G H)).Additive ∧
    PreservesFiniteLimits (inflate (R := R) (ContinuousMonoidHom.fst G H)) ∧
    PreservesFiniteColimits (inflate (R := R) (ContinuousMonoidHom.fst G H)) ∧
    ∃ (dG : Invariants R G) (dH : Invariants R H) (dGH : Invariants R (G × H))
      (dHG : ProductInvariants R G H)
      (h : trivial (R := R) (P := G × H) =
        trivial (R := R) (P := G) ⋙ inflate (R := R) (ContinuousMonoidHom.fst G H)),
      ∀ (M : ActionModule R (G × H)) (S : Profinite.{u})
        (x : sectionModule R (dGH.functor.obj M) S),
        (((dG.inclusion.app (dHG.functor.obj M)) ≫ dHG.inclusion.app M).hom.hom.app
          (op S)).hom
          (((((conjugateIsoEquiv dGH.adjunction
            (dG.adjunction.comp dHG.adjunction)) (eqToIso h.symm)).hom.app M).hom.hom.app
              (op S)).hom x) =
          ((dGH.inclusion.app M).hom.hom.app (op S)).hom x := by
  sorry

end Profinite.CondensedAction
