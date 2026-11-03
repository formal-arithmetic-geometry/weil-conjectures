/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleNormalizedMatesCompositionPasting
import all WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumRightAdjointCoherenceSupplement

/-! # Invertibility of the ordinary étale exceptional exchange

Source: the lisse paragraph of prop-trf-exceptional-kunneth.proof.md, expanded
base-change step, using the normalized sum/restriction adjunction.
(blueprint: lem-sf-etale-ordinary-right-exchange-invertible)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The specified ordinary exceptional exchange is invertible at every input.
This concerns arbitrary finite coefficients and arbitrary Cartesian base changes.
It does not assume an exceptional base-change isomorphism.

Source: lisse paragraph, expanded base-change step; the normalized right-mate
calculation in lem-pur-etale-sum-right-adjoint-coherence.
(blueprint: lem-sf-etale-ordinary-right-exchange-invertible)

Proof: the graph-normalized support-to-sum comparisons conjugate the given
exceptional adjoints to exact restriction. The normalized square identifies the
exchange followed by the target comparison with the source comparison followed
by the inverse ordinary pullback square. The latter two maps are isomorphisms.
Cancel the target comparison to obtain an isomorphism at every complex. The
componentwise criterion gives invertibility of the natural transformation.
-/
theorem etaleNormalizedRightExchange_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {w : X' ⟶ X} {w' : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e']
    (sq : IsPullback w' e' e w) (c : Compactification e) (d : Compactification e')
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G' : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ G') :
    IsIso (etaleNormalizedRightExchange A sq c d G G' adj adj') := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  have hs := normalized_square A sq c d G G' adj adj' K
  let ρ := (EtaleSupportExchange.rightAdjointIso A e' d G' adj').hom.app
    ((upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.obj K)
  have : IsIso ((etaleNormalizedRightExchange A sq c d G G' adj adj').app K ≫ ρ) := by
    rw [hs]
    infer_instance
  exact IsIso.of_isIso_comp_right
    ((etaleNormalizedRightExchange A sq c d G G' adj adj').app K) ρ

end AlgebraicGeometry.Etale
