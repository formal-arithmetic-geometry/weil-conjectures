/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.FiniteEtaleTrace
import Sheaf.AlgebraicGeometry.FiniteEtaleTraceExists
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# The trace composite on a split étale-site object

Source: Stacks Project, Tag 03SH (section-trace-method), paragraph after
Definition 03SE.
(blueprint: lem-weil-pbc-finite-etale-trace-split-component).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- On a site object whose pulled-back cover has a given finite clopen splitting,
trace after restriction is the sum of one identity per piece. No degree or connectedness
hypothesis is used. Source: Stacks Project, Tag 03SH (section-trace-method), paragraph
following Definition 03SE.
(blueprint: lem-weil-pbc-finite-etale-trace-split-component).

Proof:
1. Identify inverse image with localization restriction using
   `upperStarIsoLocalizationRestriction`. Under this isomorphism the adjunction unit
   on `W` is restriction along the projection `W ×_X Y → W`.
2. Use property (1), localization compatibility, of `existsUnique_finiteEtaleTrace`
   for `W.hom`. Pullback symmetry and pasting identify its site-object fibre product
   with `Y ×_X W`; transport the supplied clopen splitting across this identification.
3. Invert the isomorphisms `i j ≫ pullback.snd f W.hom` to obtain sections of the
   projection. Property (2), the split formula, of the same trace characterization
   expresses trace as the sum of restriction along these sections.
4. Each section composed with the projection is the identity. Contravariant
   functoriality therefore makes the composite of restriction with each summand the
   identity of `F(W)`. Distribute composition over the finite sum and use
   `Finset.sum_const` to obtain `Fintype.card J` times the identity. Transport back
   through the localization isomorphisms, which cancel by their inverse laws.
   This includes an empty index set: the empty sum is zero, agreeing with `0 • id`.
   An empty `W` also causes no difficulty, since the empty covering forces `F(W)=0`. -/
theorem finiteEtaleTrace_comp_restriction_app_of_split
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Etale f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : X.Etale)
    (J : Type u) [Fintype J] (D : J → Scheme.{u})
    (i : ∀ j, D j ⟶ pullback f W.hom)
    (_ : Nonempty (IsColimit (Cofan.mk (pullback f W.hom) i)))
    (_ : ∀ j, IsOpenImmersion (i j) ∧ IsClosedImmersion (i j))
    (_ : ∀ j, IsIso (i j ≫ pullback.snd f W.hom)) :
    (finiteEtaleRestriction f F ≫ finiteEtaleTrace f F).hom.app (op W) =
      Fintype.card J • 𝟙 (F.obj.obj (op W)) := by sorry

end AlgebraicGeometry.Etale
