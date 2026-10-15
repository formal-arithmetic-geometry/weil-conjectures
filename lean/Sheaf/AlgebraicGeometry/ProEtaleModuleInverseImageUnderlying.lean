/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

/-!
# Underlying abelian sheaf of the small-model module inverse image

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3,
`sites-modules.tex`, labels `lemma-pullback-module` and `lemma-adjoint-push-pull-modules`.
(blueprint: lem-weil-pbc-proetale-module-inverse-image-underlying).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Forgetting the action on the model-site module pullback gives model-site abelian inverse image.

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3,
`sites-modules.tex`, labels `lemma-pullback-module` and `lemma-adjoint-push-pull-modules`.
(blueprint: lem-weil-pbc-proetale-module-inverse-image-underlying).

Proof:
1. Work first on the equivalent sites `proEtaleSiteModel Y` and `proEtaleSiteModel X`.
   Set inverse image preserves finite products: base change preserves finite limits,
   its opposite has filtered comma categories, and sheafification preserves finite limits.
   Transport addition and scalar multiplication by the inverse-product comparisons.
   Applying the functor to associativity, unit and distributivity equations gives a module
   over the inverse-image ring. Its underlying abelian sheaf is abelian inverse image:
   the transported additive operations give the abelian adjunction, so uniqueness of
   left adjoints identifies it with the constructed abelian sheaf pullback. The same
   argument for ring operations identifies its ring with the commutative-ring pullback.
   The down/up site equivalences identify that ring pullback with the down transport of
   the original ring pullback by uniqueness of left adjoints. Their unit equation identifies
   the structural ring map with the original unit precomposed with `AsSmall.down.op`.
2. Let alpha be an abelian morphism from this inverse-image module to a target module,
   and let beta be its adjunct. The mates of alpha after the inverse-image source action
   and of the target action after (identity, alpha) are respectively beta after the
   source action and direct image of the target action after (the ring unit, beta).
   Naturality of the adjunction unit on the source action and its compatibility with
   products give these identities. Injectivity of the adjunction bijection proves
   linearity in both directions. This constructs a module adjunction whose right functor
   is sectionwise direct image with scalars restricted along the ring adjunction unit.
3. Mathlib's `SheafOfModules.pullback (proEtaleModelRingUnit f R)` is also left adjoint
   to that same right functor. Uniqueness of left adjoints therefore identifies it
   naturally with the action construction from step 1. The ring map is precisely
   `proEtaleModelRingUnit f R`, since both maps are the original ring unit precomposed
   with `AsSmall.down.op`; no other structural map is introduced.
4. Forget the module comparison from step 3 and compose it with the underlying-abelian
   comparison from step 1. This gives the displayed natural isomorphism on the model sites.
   The argument uses no nonzero coefficient, nonempty scheme or flat scheme morphism. -/
theorem proEtaleModelModuleInverseImage_underlying {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    let A := (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
    let B := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
    let A' := ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj A
    let B' := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj B
    Nonempty (SheafOfModules.pullback.{u + 1} (proEtaleModelRingUnit f R) ⋙
      SheafOfModules.toSheaf B' ≅
      SheafOfModules.toSheaf A' ⋙
        Functor.sheafPullbackConstruction.sheafPullback (proEtaleModelBaseChange f)
          AddCommGrpCat.{u + 1} (proEtaleModelTopology Y) (proEtaleModelTopology X)) := by
  sorry

end AlgebraicGeometry.Scheme
