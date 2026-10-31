/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.ClosedTestDerivedExchangeMaps
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.CondensedExchangeOpenRestrictionVertex
import WeilConjectures.AlgebraicGeometry.CondensedExchangeOpenRestrictionComparison

/-! # Restriction of the internal-module exchange to one base open

Source: Stacks Project, Tags 0D6F and 07A7, and ringed open restriction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Choose the published structures so derived-functor arguments share the same data.
attribute [local instance 4000]
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  CategoryTheory.Mod.instAbelian
attribute [local instance 5000] AlgebraicGeometry.ProEtale.sheafMonoidalCategory

attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  condensedAmbientExchange moduleObjectDerivedPushforward moduleObjectDerivedPullback
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ClosedTestDerivedExchangeModel.pull ClosedTestDerivedExchangeModel.exchange

/-- On a single open of the base, the restricted ambient mate is invertible exactly
when the localized exact-pullback mate is invertible. This compares two actual maps,
for an arbitrary derived input and arbitrary Cartesian presentations.

Source: Stacks Project, Tags 0D6F and 07A7; ringed open restriction, transported through
internal_module_operations_transport
(blueprint: lem-sfb-condensed-exchange-one-open-restriction).

Proof: Form the missing vertex map t : XU' → X' from the three supplied
pullback squares by their universal properties. Pasting and cancellation make the
remaining two faces Cartesian. The maps a, b and t are open immersions by base change.
Pass to section modules using the canonical exact internal/section equivalences.
The upper and lower comparisons preserve the specified adjunction units and counits.
Exact equivalences preserve K-injectives: their inverse equivalences are exact left
adjoints. Thus on K-injective representatives the lower comparisons induce the
right-derived comparisons, normalized by the same ordinary comparisons. The exact
upper comparisons descend termwise. Their unit and counit equations descend as well,
so they identify the derived mates, including their pullback-composition comparison.
Compare total left pullback with exact pullback by its canonical derived comparison;
the adjunctions correspond because both are derived from the same ordinary adjunction.

For exact pullback, write α : b* g* ≅ gU* v*, β : b* Rf'_* ≅ RfU'_* t*,
γ : v* Rf_* ≅ RfU_* a*, and δ : t* g'* ≅ hU* a* for the canonical comparisons.
Ringed open_restriction gives, on K, the equation
b*(Ex_K); β; RfU'_*(δ) = α; gU*(γ); Ex_U(a*K).
This follows by taking the local fU'-adjoint transpose: open localization preserves
the f-counit, while the intermediate unit/counit pair cancels by its triangle
identity. The coefficient identifications agree by pullback composition from Λ.
All four comparisons are isomorphisms; the direct-image comparisons β and γ are
isomorphisms by ringed open_comparison. Cancel these isomorphisms in the displayed
equation. Finally the exact equivalences reflect isomorphisms, so transport the
result back to internal modules and through the total-left/exact comparison.
No affine, closed, proper, boundedness or constructibility hypothesis is used.
The same comparison equations apply to empty opens. -/
theorem condensed_exchange_one_open_restriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y U XU YU' XU' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (v : U ⟶ Y) [IsOpenImmersion v]
    (a : XU ⟶ X) (fU : XU ⟶ U)
    (b : YU' ⟶ Y') (gU : YU' ⟶ U)
    (hU : XU' ⟶ XU) (fU' : XU' ⟶ YU')
    (wf : IsPullback a fU f v) (wg : IsPullback b gU g v)
    (w : IsPullback hU fU' fU gU)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    IsIso ((upperStar Λ b).mapDerivedCategory.map ((condensedAmbientExchange Λ sq).app K)) ↔
      IsIso ((ClosedTestDerivedExchangeModel.exchange Λ w.toCommSq).app
        ((upperStar Λ a).mapDerivedCategory.obj K)) := by
  obtain ⟨t, htg, htf⟩ :=
    condensed_exchange_one_open_restriction_vertex Λ sq v a fU b gU hU fU' wf wg w
  obtain ⟨e⟩ :=
    condensed_exchange_one_open_restriction_comparison_square Λ sq v a fU b gU hU fU'
      wf wg w t htg htf K
  exact CategoryTheory.Arrow.isIso_iff_isIso_of_isIso e.hom

end AlgebraicGeometry.ProEtale.CondensedRing
