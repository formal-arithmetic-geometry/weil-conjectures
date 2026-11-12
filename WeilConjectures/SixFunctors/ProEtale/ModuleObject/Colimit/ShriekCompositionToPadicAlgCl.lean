/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ConjugateIsoComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ShriekCompositionPushforwardData

/-!
# The coefficient comparisons for `Rf_!` and `f^!` and the composition of morphisms

For the extension of scalars `T : Dᵇc(-)⟦E⟧ ⥤ Dᵇc(-)⟦ℚ̄_ℓ⟧` and composable morphisms
`f : X ⟶ Y`, `g : Y ⟶ S` of separated schemes of finite type over `k`:

* the (Shriek) comparisons `Rf_! ⋙ T ≅ T ⋙ Rf_!`
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekToPadicAlgClIso`) are compatible with
  the composition isomorphisms `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`
  (`ProEtale.CondensedRing.squareCompatible_boundedConstructibleLowerShriekComp_toPadicAlgCl`);
* consequently, the comparisons `f^! ⋙ T ⟶ T ⋙ f^!`
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekToPadicAlgCl`), the mates of the
  inverses of (Shriek), are compatible with the composition isomorphisms
  `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!`, the conjugates of the former
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekComp_toPadicAlgCl`). This is the formal
  argument `CategoryTheory.mateEquiv_inv_app_comp_conjugateIsoEquiv`.

The first statement is the instance, for the coefficient change
`ProEtale.CondensedRing.toPadicAlgClCoefficientChange`, of the general compatibility
`ProEtale.CondensedRing.BoundedConstructibleCoefficientChange.squareCompatible_lowerShriekComp`,
once both composition isomorphisms are identified with the general construction
`ProEtale.CondensedRing.BoundedConstructiblePushforwardData.lowerShriekComp`. For `ℚ̄_ℓ` this is
`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl_eq_lowerShriekComp`. For
`E` it is `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_eq_lowerShriekComp`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ) {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom] (f : X ⟶ Y) (g : Y ⟶ S)

/-- Blueprint `proposition-six-operations-change-coefficients--16`: **the (Shriek) comparison is
compatible with the composition of morphisms.** For the extension of scalars `T` along
`E ⟶ ℚ̄_ℓ`, the comparison `R(f ≫ g)_! ⋙ T ≅ T ⋙ R(f ≫ g)_!` corresponds, under the composition
isomorphisms `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` over `E` and over `ℚ̄_ℓ`, to the comparison pasted from
those for `f` and for `g`. -/
theorem squareCompatible_boundedConstructibleLowerShriekComp_toPadicAlgCl :
    NatTrans.SquareCompatible (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E (f ≫ g))
      (Functor.pasteSquareIso (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f)
        (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E g))
      (boundedConstructibleLowerShriekComp ℓ E f g).hom
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom := by
  have H := (toPadicAlgClCoefficientChange ℓ E k).squareCompatible_lowerShriekComp
    (isIsoRefinementPushforward_continuousMapPushforwardData ℓ k E)
    (isIsoExchange_continuousMapPushforwardData ℓ E k)
    (isIsoRefinementPushforward_padicAlgClPushforwardData ℓ k)
    (isIsoExchange_padicAlgClPushforwardData ℓ k) f g
  refine NatTrans.SquareCompatible.of_eq_natTrans (NatTrans.SquareCompatible.of_eq H
    (boundedConstructibleLowerShriekToPadicAlgClIso_eq_shriekOfCompactification ℓ E k (f ≫ g)).symm
    ?_) (congrArg Iso.hom (boundedConstructibleLowerShriekComp_eq_lowerShriekComp ℓ E f g).symm)
    (congrArg Iso.hom
      (boundedConstructibleLowerShriekComp_padicAlgCl_eq_lowerShriekComp ℓ f g).symm)
  rw [boundedConstructibleLowerShriekToPadicAlgClIso_eq_shriekOfCompactification ℓ E k f,
    boundedConstructibleLowerShriekToPadicAlgClIso_eq_shriekOfCompactification ℓ E k g]

/-- Blueprint `proposition-six-operations-change-coefficients--17`: **the `f^!` comparison is
compatible with the composition of morphisms.** For the extension of scalars `T` along
`E ⟶ ℚ̄_ℓ`, the comparison `R(f ≫ g)^! ⋙ T ⟶ T ⋙ R(f ≫ g)^!` followed by the composition
isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` over `ℚ̄_ℓ` equals the composition isomorphism over `E`
followed by the comparisons for `g` and for `f`. It is the formal consequence of
`squareCompatible_boundedConstructibleLowerShriekComp_toPadicAlgCl`, the comparisons for `f^!`
being the mates of the inverses of those for `Rf_!` and the composition isomorphisms for `f^!`
the conjugates of those for `Rf_!`. -/
theorem boundedConstructibleUpperShriekComp_toPadicAlgCl
    (K : Dᵇc(S.left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleToPadicAlgCl X.left ℓ E).map
        ((boundedConstructibleUpperShriekComp ℓ E f g).hom.app K) ≫
      (boundedConstructibleUpperShriekToPadicAlgCl ℓ E f).app
        ((ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E g).obj K) ≫
      (boundedConstructibleUpperShriek ℓ f).map
        ((boundedConstructibleUpperShriekToPadicAlgCl ℓ E g).app K) =
    (boundedConstructibleUpperShriekToPadicAlgCl ℓ E (f ≫ g)).app K ≫
      (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f g).hom.app
        ((boundedConstructibleToPadicAlgCl S.left ℓ E).obj K) :=
  mateEquiv_inv_app_comp_conjugateIsoEquiv'
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E g)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E (f ≫ g))
    (boundedConstructibleUpperShriekAdjunction ℓ f) (boundedConstructibleUpperShriekAdjunction ℓ g)
    (boundedConstructibleUpperShriekAdjunction ℓ (f ≫ g))
    (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f)
    (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E g)
    (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E (f ≫ g))
    (boundedConstructibleLowerShriekComp ℓ E f g)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g)
    (squareCompatible_boundedConstructibleLowerShriekComp_toPadicAlgCl ℓ E f g)
    (boundedConstructibleUpperShriekToPadicAlgCl_eq_mateEquiv ℓ E f)
    (boundedConstructibleUpperShriekToPadicAlgCl_eq_mateEquiv ℓ E g)
    (boundedConstructibleUpperShriekToPadicAlgCl_eq_mateEquiv ℓ E (f ≫ g)) rfl rfl K

end AlgebraicGeometry.ProEtale.CondensedRing
