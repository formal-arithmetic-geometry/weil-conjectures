/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.WeilObject.BoundedConstructible.Defs

/-!

# The derived pullback and pushforward of Weil objects

Let `f : X ⟶ Y` be a morphism of schemes and `e_X : X ≅ X`, `e_Y : Y ≅ Y` automorphisms
compatible with `f`, that is `e_X ≫ f = f ≫ e_Y` (`hf`). Write `Φ_X = Le_X^*` and
`Φ_Y = Le_Y^*` for the Frobenius pullbacks on the bounded constructible derived categories
`Dᵇc(-)⟦ℚ̲̄_ℓ⟧` of `ℚ̄_ℓ`-sheaves (`WeilConjectures.WeilObject.BoundedConstructible.Defs`). For a
functor `G` between these categories with a commutation isomorphism `b_G`, the Weil structure of
`G K` is the composite

```
φ_{GK} : Φ (G K) --b_G(K)--> G (Φ K) --G(φ_K)--> G K,
```

which is `CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso b_G`. This file supplies `b_G` for
the derived pullback and the derived pushforward.

* **Pullback.** The comparison `b^* : Lf^* ⋙ Φ_X ≅ Φ_Y ⋙ Lf^*` (that is `Φ_X Lf^* ≅ Lf^* Φ_Y`) is
  the pullback comparison `boundedConstructiblePullbackSquareComparison` of the Frobenius square
  `e_X ≫ f = f ≫ e_Y`, built from the composition isomorphisms of the derived pullback. No base
  change theorem is needed (`ProEtale.CondensedRing.weilUpperStarComparison`,
  `ProEtale.CondensedRing.weilUpperStar`).
* **Pushforward.** The comparison `b_* : Rf_* ⋙ Φ_Y ⟶ Φ_X ⋙ Rf_*` (that is
  `Φ_Y Rf_* ⟶ Rf_* Φ_X`) is the base-change morphism `boundedConstructibleBaseChange` of the
  Frobenius square (`ProEtale.CondensedRing.weilLowerStarComparison`). It is invertible since the
  horizontal maps of the square are isomorphisms
  (`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isIso`); no properness of `f`
  is needed. This gives the Weil pushforward `ProEtale.CondensedRing.weilLowerStar`.

## Sorried input

- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isIso`: the base-change
  morphism of a commutative square whose horizontal maps `g` and `g'` are isomorphisms is an
  isomorphism. This is formal: the derived pullbacks along `g` and `g'` are then equivalences,
  with inverses the pullbacks along `g⁻¹` and `g'⁻¹`, and the mate of an isomorphism between
  equivalences is an isomorphism. Making it precise needs the identity isomorphism
  `L(𝟙 X)^* ≅ 𝟭` of the derived pullback on module objects, which is not yet available. For `f`
  proper, it is also a consequence of proper base change
  (`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl`).

## Main definitions

- `ProEtale.CondensedRing.weilUpperStar`: the derived pullback
  `WeilBoundedConstructible ℓ k e_Y ⥤ WeilBoundedConstructible ℓ k e_X` of Weil objects.
- `ProEtale.CondensedRing.weilLowerStar`: the derived pushforward
  `WeilBoundedConstructible ℓ k e_X ⥤ WeilBoundedConstructible ℓ k e_Y` of Weil objects.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section BaseChangeOfIsIso

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} [f.IsOver (Spec (.of k))]
  [g.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- Base change along isomorphisms: for a commutative square `g' ≫ f = f' ≫ g` of schemes whose
horizontal maps `g` and `g'` are isomorphisms, the base-change morphism
`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` on bounded constructible `ℚ̄_ℓ`-sheaves is an isomorphism.
No properness of `f` is needed. See the module docstring for the argument. -/
theorem isIso_boundedConstructibleBaseChange_of_isIso [IsIso g] [IsIso g']
    (sq : CommSq g' f' f g) :
    IsIso (boundedConstructibleBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ k sq) :=
  sorry

end BaseChangeOfIsIso

variable {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  (eX : X ≅ X) (eY : Y ≅ Y) [eX.hom.IsOver (Spec (.of k))] [eY.hom.IsOver (Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (hf : eX.hom ≫ f = f ≫ eY.hom)

/-! ### The pullback -/

section UpperStar

/-- The Frobenius comparison `b^* : Lf^* ⋙ Le_X^* ≅ Le_Y^* ⋙ Lf^*` of the derived pullback, that
is `Φ_X Lf^* ≅ Lf^* Φ_Y`: the pullback comparison of the Frobenius square
`e_X ≫ f = f ≫ e_Y`. -/
noncomputable def weilUpperStarComparison :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k f ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k eX.hom ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k eY.hom ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k f :=
  (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ k
    (CommSq.mk hf)).symm

/-- The derived pullback `Lf^*` of Weil objects: a Weil object `(K, φ_K)` for `e_Y` is sent to
`Lf^* K` with the structure isomorphism
`Φ_X Lf^* K ≅ Lf^* Φ_Y K ≅ Lf^* K` given by `weilUpperStarComparison` and `Lf^* φ_K`. -/
noncomputable def weilUpperStar :
    WeilBoundedConstructible ℓ k eY ⥤ WeilBoundedConstructible ℓ k eX :=
  IsoAlgebra.mapOfNatIso (weilUpperStarComparison ℓ k eX eY f hf)

@[simp]
lemma weilUpperStar_obj_carrier (K : WeilBoundedConstructible ℓ k eY) :
    ((weilUpperStar ℓ k eX eY f hf).obj K).carrier =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k f).obj K.carrier :=
  rfl

lemma weilUpperStar_obj_str (K : WeilBoundedConstructible ℓ k eY) :
    ((weilUpperStar ℓ k eX eY f hf).obj K).str =
      (weilUpperStarComparison ℓ k eX eY f hf).app K.carrier ≪≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k f).mapIso K.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ K

/-- The derived pullback of Weil objects lifts the derived pullback on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` along the
forgetful functors. -/
lemma weilUpperStar_comp_forget :
    weilUpperStar ℓ k eX eY f hf ⋙ WeilBoundedConstructible.forget ℓ k eX =
      WeilBoundedConstructible.forget ℓ k eY ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k f :=
  rfl

end UpperStar

/-! ### The pushforward -/

section LowerStar

/-- The Frobenius comparison `b_* : Rf_* ⋙ Le_Y^* ⟶ Le_X^* ⋙ Rf_*` of the derived pushforward,
that is `Φ_Y Rf_* ⟶ Rf_* Φ_X`: the base-change morphism of the Frobenius square
`e_X ≫ f = f ≫ e_Y`. -/
noncomputable def weilLowerStarComparison :
    boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k f ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k eY.hom ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k eX.hom ⋙
        boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k f :=
  boundedConstructibleBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ k (CommSq.mk hf)

/-- The Frobenius comparison of the derived pushforward is an isomorphism, the Frobenius
automorphisms being isomorphisms. -/
instance isIso_weilLowerStarComparison : IsIso (weilLowerStarComparison ℓ k eX eY f hf) :=
  isIso_boundedConstructibleBaseChange_of_isIso ℓ k _

/-- The derived pushforward `Rf_*` of Weil objects: a Weil object `(K, φ_K)` for `e_X` is sent to
`Rf_* K` with the structure isomorphism `Φ_Y Rf_* K ≅ Rf_* Φ_X K ≅ Rf_* K` given by the inverted
`weilLowerStarComparison` and `Rf_* φ_K`. -/
noncomputable def weilLowerStar :
    WeilBoundedConstructible ℓ k eX ⥤ WeilBoundedConstructible ℓ k eY :=
  IsoAlgebra.mapOfNatIso (asIso (weilLowerStarComparison ℓ k eX eY f hf))

@[simp]
lemma weilLowerStar_obj_carrier (K : WeilBoundedConstructible ℓ k eX) :
    ((weilLowerStar ℓ k eX eY f hf).obj K).carrier =
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k f).obj K.carrier :=
  rfl

lemma weilLowerStar_obj_str (K : WeilBoundedConstructible ℓ k eX) :
    ((weilLowerStar ℓ k eX eY f hf).obj K).str =
      (asIso (weilLowerStarComparison ℓ k eX eY f hf)).app K.carrier ≪≫
        (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k f).mapIso K.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ K

/-- The derived pushforward of Weil objects lifts the derived pushforward on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` along
the forgetful functors. -/
lemma weilLowerStar_comp_forget :
    weilLowerStar ℓ k eX eY f hf ⋙ WeilBoundedConstructible.forget ℓ k eY =
      WeilBoundedConstructible.forget ℓ k eX ⋙
        boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k f :=
  rfl

end LowerStar

end AlgebraicGeometry.ProEtale.CondensedRing
