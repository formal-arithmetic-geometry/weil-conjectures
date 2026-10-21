module

public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.WeilObject.BoundedConstructible.Defs
public import Sheaf.CategoryTheory.MateIsoAlongEquivalences
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback

/-! Declarations of ours that lived in the upstream file `WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar` (moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-!

# The derived pullback and pushforward of Weil objects

Let `f : X ⟶ Y` be a morphism of schemes and `Φ_X : X ⟶ X`, `Φ_Y : Y ⟶ Y` endomorphisms
compatible with `f`, that is `Φ_X ≫ f = f ≫ Φ_Y` (`hf`). Write `Φ_X` and `Φ_Y` also for the
Frobenius pullbacks `LΦ_X^*` and `LΦ_Y^*` on the bounded constructible derived categories
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
  `Φ_X ≫ f = f ≫ Φ_Y`, built from the composition isomorphisms of the derived pullback. No base
  change theorem is needed, and `Φ_X`, `Φ_Y` need not be isomorphisms
  (`ProEtale.CondensedRing.weilUpperStarComparison`, `ProEtale.CondensedRing.weilUpperStar`).
  For `f = x` a rational point fixed by `Φ_X`, this is the stalk of a Weil object
  (`WeilConjectures.TraceFormula.Stalk`).
* **Pushforward.** For automorphisms `Φ_X = e_X.hom` and `Φ_Y = e_Y.hom`, the comparison
  `b_* : Rf_* ⋙ Φ_Y ⟶ Φ_X ⋙ Rf_*` (that is
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
  `WeilBoundedConstructible ℓ Φ_Y ⥤ WeilBoundedConstructible ℓ Φ_X` of Weil objects.
- `ProEtale.CondensedRing.weilLowerStar`: the derived pushforward
  `WeilBoundedConstructible ℓ e_X.hom ⥤ WeilBoundedConstructible ℓ e_Y.hom` of Weil objects, for
  automorphisms `e_X` and `e_Y`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

private lemma exchangeRight_eq_mate
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {G : C ⥤ C'} {H : D ⥤ D'} (a : L ⊣ R) (b : L' ⊣ R')
    (θ : G ⋙ L' ≅ L ⋙ H) :
    Adjunction.exchangeRight a b θ = (mateEquiv a b θ.hom).natTrans := by
  ext K
  simp [Adjunction.exchangeRight_app, mateEquiv]

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section BaseChangeOfIsIso

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}


private theorem upperStar_isEquivalence {U V : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (h : U ⟶ V) [IsIso h] :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).IsEquivalence := by
  let Λ := Profinite.padicAlgClRingObj ℓ
  apply Functor.IsEquivalence.mk'
    (G := boundedConstructibleUpperStar Λ ℓ (inv h))
  · exact (boundedConstructibleUpperStarId Λ ℓ V).symm ≪≫
      eqToIso (by simp) ≪≫ boundedConstructibleUpperStarComp Λ ℓ (inv h) h
  · exact (boundedConstructibleUpperStarComp Λ ℓ h (inv h)).symm ≪≫
      eqToIso (by simp) ≪≫ boundedConstructibleUpperStarId Λ ℓ U


end BaseChangeOfIsIso

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-! ### The pullback -/

section UpperStar

variable (ΦX : X ⟶ X) (ΦY : Y ⟶ Y) (f : X ⟶ Y) (hf : ΦX ≫ f = f ≫ ΦY)

end UpperStar

/-! ### The pushforward -/

section LowerStar

variable (eX : X ≅ X) (eY : Y ≅ Y) (f : X ⟶ Y) (hf : eX.hom ≫ f = f ≫ eY.hom)

end LowerStar

end AlgebraicGeometry.ProEtale.CondensedRing
