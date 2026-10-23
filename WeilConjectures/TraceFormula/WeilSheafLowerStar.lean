/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.TraceFormula.ShriekTraceFunction

/-!

# The pushforward of Weil sheaves

Let `f : X ⟶ Y` be a morphism of schemes over `Spec k` and `e_X`, `e_Y` automorphisms with
`e_X ≫ f = f ≫ e_Y`. The pushforward `f_*` of module objects over `ℚ̲̄_ℓ` sends Weil sheaves for
`e_X` to Weil sheaves for `e_Y` (`ProEtale.CondensedRing.weilSheafLowerStar`): the structure
isomorphism of `f_* F` is `e_Y^* f_* F ≅ f_* e_X^* F ≅ f_* F`, through the base-change morphism of
the square `e_X ≫ f = f ≫ e_Y` (`ProEtale.CondensedRing.lowerStarBaseChange`), an isomorphism
since `e_X` and `e_Y` are.

The base-change morphism `g^* f_* ⟶ f'_* g'^*` of a commutative square `g' ≫ f = f' ≫ g` is the
exchange morphism `CategoryTheory.Adjunction.exchangeRight` of the composition isomorphisms of the
pullbacks (`ProEtale.CondensedRing.upperStarSquareComparison`), as for the bounded constructible
base-change morphism `ProEtale.CondensedRing.boundedConstructibleBaseChange`.

## Main definitions

- `ProEtale.CondensedRing.lowerStarBaseChange`: the base-change morphism on module objects.
- `ProEtale.CondensedRing.weilSheafLowerStar`: the pushforward of Weil sheaves.

## Main results

- `ProEtale.CondensedRing.nonempty_powSucc_weilSheafLowerStar_iso`: the pushforward commutes with
  the iterated Weil structures, `(f_* F)^{(n+1)} ≅ f_* F^{(n+1)}` as Weil sheaves for `e_Y^{n+1}`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section BaseChange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The comparison `g^* ⋙ f'^* ≅ f^* ⋙ g'^*` of pullbacks of module objects along a commutative
square `g' ≫ f = f' ≫ g`, through the composition isomorphisms `upperStarComp`. -/
noncomputable def upperStarSquareComparison (sq : CommSq g' f' f g) :
    (g)^*⟦Λ⟧ ⋙ (f')^*⟦Λ⟧ ≅ (f)^*⟦Λ⟧ ⋙ (g')^*⟦Λ⟧ :=
  (upperStarComp Λ f' g).symm ≪≫ eqToIso (by rw [sq.w]) ≪≫ upperStarComp Λ g' f

/-- The base-change morphism `g^* f_* ⟶ f'_* g'^*` on module objects of a commutative square
`g' ≫ f = f' ≫ g`: the exchange morphism of `upperStarSquareComparison` under the adjunctions
`f^* ⊣ f_*` and `f'^* ⊣ f'_*`. -/
noncomputable def lowerStarBaseChange (sq : CommSq g' f' f g) :
    (f)_*⟦Λ⟧ ⋙ (g)^*⟦Λ⟧ ⟶ (g')^*⟦Λ⟧ ⋙ (f')_*⟦Λ⟧ :=
  Adjunction.exchangeRight (upperStarLowerStarAdjunction Λ f) (upperStarLowerStarAdjunction Λ f')
    (upperStarSquareComparison Λ sq)

/-- The base-change morphism of a square whose horizontal maps are isomorphisms is an
isomorphism. -/
instance isIso_lowerStarBaseChange_of_isIso (sq : CommSq g' f' f g) [IsIso g] [IsIso g'] :
    IsIso (lowerStarBaseChange Λ sq) :=
  sorry

end BaseChange

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
  (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)

include hf in
lemma commSq_left_of_comp_eq : CommSq eX.hom.left f.left f.left eY.hom.left :=
  ⟨by rw [← Over.comp_left, hf, Over.comp_left]⟩

/-- The Frobenius comparison `f_* ⋙ e_Y^* ≅ e_X^* ⋙ f_*` of the pushforward of module objects:
the base-change morphism of the square `e_X ≫ f = f ≫ e_Y`, an isomorphism since `e_X` and `e_Y`
are. -/
noncomputable def weilSheafLowerStarComparison :
    (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙ (eY.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅
      (eX.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙
        (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  asIso (lowerStarBaseChange _ (commSq_left_of_comp_eq eX eY hf))

/-- The pushforward `f_*` of Weil sheaves along `f : X ⟶ Y` with `e_X ≫ f = f ≫ e_Y`: a Weil
sheaf `(F, φ_F)` for `e_X` is sent to `f_* F` with the structure isomorphism
`e_Y^* f_* F ≅ f_* e_X^* F ≅ f_* F` given by `weilSheafLowerStarComparison` and `f_* φ_F`. -/
noncomputable def weilSheafLowerStar : WeilSheaf ℓ eX ⥤ WeilSheaf ℓ eY :=
  IsoAlgebra.mapOfNatIso (weilSheafLowerStarComparison ℓ eX eY hf)

@[simp]
lemma weilSheafLowerStar_obj_carrier (F : WeilSheaf ℓ eX) :
    ((weilSheafLowerStar ℓ eX eY hf).obj F).carrier =
      (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧.obj F.carrier :=
  rfl

lemma weilSheafLowerStar_obj_str (F : WeilSheaf ℓ eX) :
    ((weilSheafLowerStar ℓ eX eY hf).obj F).str =
      (weilSheafLowerStarComparison ℓ eX eY hf).app F.carrier ≪≫
        (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧.mapIso F.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ F

/-- **The pushforward commutes with the iterated Weil structures**: for a Weil sheaf `F` for
`e_X`, the Weil sheaf `(f_* F)^{(n+1)}` for `e_Y^{n+1}` is the pushforward of the Weil sheaf
`F^{(n+1)}` for `e_X^{n+1}`. The iterated comparison is the base-change morphism of the pasted
squares, by the pasting law of exchange morphisms. -/
theorem nonempty_powSucc_weilSheafLowerStar_iso (F : WeilSheaf ℓ eX) (n : ℕ) :
    Nonempty (WeilSheaf.powSucc ℓ ((weilSheafLowerStar ℓ eX eY hf).obj F) n ≅
      (weilSheafLowerStar ℓ (eX.powSucc n) (eY.powSucc n)
        (Iso.powSucc_hom_comp_eq_comp_powSucc_hom eX eY hf n)).obj
        (WeilSheaf.powSucc ℓ F n)) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
