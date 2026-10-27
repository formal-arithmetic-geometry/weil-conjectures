/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeResidue
public import WeilConjectures.Tactic.NormalizeInstanceProofs

/-!
# The derived reduction of the integral base-change morphism, on the ambient derived categories

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and residue field
`𝔽_E`. For a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

and a bounded below complex `K` of `𝒪_{E,X}`-modules on `X_proét`, the first derived reduction
`K ↦ K ⊗ᴸ_{𝒪_E} 𝔽_E` (`ProEtale.derivedReduction`) of the base-change morphism
`Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` of module objects over `𝒪_E` and the derived base change map of
pro-étale sheaves of `𝔽_E`-modules at the first derived reduction of `K` are isomorphic arrows
(`ProEtale.CondensedRing.nonempty_arrowIso_derivedReduction_exchangeRight`).

This is the composite of the transfer of exchange morphisms along the non-flat coefficient change
`𝒪_E ⟶ 𝔽_E`
(`ProEtale.CondensedRing.nonempty_arrowIso_map_exchangeRight_derivedExtendScalars_of_nonFlat'`),
whose (Push) comparisons are invertible on bounded below complexes
(`ProEtale.CondensedRing.isIso_derivedUpperStarExtendScalarsPushHom_residueField_app`), and of the
transport along residue field module sheaves
(`ProEtale.nonempty_arrowIso_map_exchangeRight_residueField_derivedBaseChangeMap`).

## Implementation notes

The two isomorphisms are elaborated with different proofs of `Precoherent Profinite` inside the
`MonObj` instances of the condensed ring `𝔽̲_E` (one of them the auxiliary proof constant of
`ProEtale.pointLowerStar`). Composing them directly makes the unifier and the kernel unfold the
surrounding definitions; `normalize_instance_proofs` first replaces all these proofs by the
instance found by instance search.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The derived reduction of the integral base-change morphism.** For a commutative square
`sq` of schemes and a bounded below complex `K` of `𝒪_{E,X}`-modules, the first derived reduction
of the base-change morphism `Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` of module objects over `𝒪_E` and the
derived base change map of pro-étale sheaves of `𝔽_E`-modules at the first derived reduction of
`K` are isomorphic arrows. -/
theorem nonempty_arrowIso_derivedReduction_exchangeRight (sq : CommSq g' f' f g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) [K.IsGE n] :
    Nonempty (Arrow.mk ((derivedReduction Y' ℓ E).map ((Adjunction.exchangeRight
        (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) f)
        (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) f')
        (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1) sq)).app K)) ≅
      Arrow.mk ((ProEtale.derivedBaseChangeMap
        (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) sq).app
        ((derivedReduction X ℓ E).obj K))) := by
  have h₁ : IsIso ((derivedUpperStarExtendScalarsPushHom
      (Profinite.padicIntegersRingObjToResidueField ℓ E.1) f).app K) :=
    isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E f K n
  have : ((g')^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.leftDerivedFunctor.obj K).IsGE n :=
    isGE_leftDerivedUpperStar_obj _ g' K n
  have h₂ : IsIso ((derivedUpperStarExtendScalarsPushHom
      (Profinite.padicIntegersRingObjToResidueField ℓ E.1) f').app
      ((g')^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.leftDerivedFunctor.obj K)) :=
    isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E f'
      ((g')^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.leftDerivedFunctor.obj K) n
  have k₂ := nonempty_arrowIso_map_exchangeRight_derivedExtendScalars_of_nonFlat'
    (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
    (derivedUpperStarExtendScalarsIsoCompCoherence
      (Profinite.padicIntegersRingObjToResidueField ℓ E.1)) sq K h₁ h₂
  have k₃ := nonempty_arrowIso_map_exchangeRight_residueField_derivedBaseChangeMap sq
    ((Mod.extendScalars (coefficientMap
      (Profinite.padicIntegersRingObjToResidueField ℓ E.1) X)).leftDerivedFunctor.obj K)
  obtain ⟨e₂⟩ := k₂
  obtain ⟨e₃⟩ := k₃
  normalize_instance_proofs Precoherent Profinite.{u} at e₂ e₃ ⊢
  exact ⟨(residueFieldModuleSheaf Y' ℓ E).mapDerivedCategory.mapArrow.mapIso e₂ ≪≫ e₃⟩

end AlgebraicGeometry.ProEtale.CondensedRing
