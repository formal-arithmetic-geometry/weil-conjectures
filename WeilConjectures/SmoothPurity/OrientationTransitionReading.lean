/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReduction
public import WeilConjectures.SmoothPurity.OrientationFinite

/-!
# Reductions of morphisms of reductions, read on the étale site

Let `K`, `L` be bounded constructible `𝒪_E`-complexes, `t' : red_{n+1} K ⟶ red_{n+1} L` and
`t : red_n K ⟶ red_n L` morphisms of their reductions. This file gives a criterion, read on the
small étale site, for the condensed reduction `(𝒪_E ⧸ ℓⁿ) ⊗ᴸ_{𝒪_E ⧸ ℓⁿ⁺¹} t'`
(`Mod.derivedExtendScalarsReduction`) of `t'` to be `t`: through the isomorphisms
`β : Ψ(red_{n+1} -) ≅ red_n -` (`ProEtale.CondensedRing.etaleReductionExtendScalarsIso`), the
derived extension of scalars `Ψ` of the étale reading of `t'` is the étale reading of `t`
(`ProEtale.CondensedRing.derivedExtendScalarsReduction_derivedReductionMap_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

section Condensed

variable (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]

/-- The condensed transition isomorphism `(𝒪_E ⧸ ℓⁿ) ⊗ᴸ red_{n+1} - ≅ red_n -`
(`boundedConstructibleIntegersModPowReductionTransitionIso`) intertwines the derived extension of
scalars of a morphism `t' : red_{n+1} K ⟶ red_{n+1} L` and its condensed reduction
(`Mod.derivedExtendScalarsReduction`). -/
lemma boundedConstructibleIntegersModPowReductionTransitionIso_hom_app_comp
    {K L : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E⟧}
    (t' : (boundedConstructibleIntegersModPowReduction X ℓ E (n + 1)).obj K ⟶
      (boundedConstructibleIntegersModPowReduction X ℓ E (n + 1)).obj L) :
    (boundedConstructibleIntegersModPowReductionTransitionIso ℓ E n X).hom.app K ≫
        (boundedConstructibleIntegersModPowReductionCompatibility X ℓ E n).hom.app K ≫
        Mod.derivedExtendScalarsReduction _ (integersModPowTransition X ℓ E n) _
          (integersModPowReduction_comp_integersModPowTransition X ℓ E n)
          (derivedReductionMap ℓ E (n + 1) X t') ≫
        (boundedConstructibleIntegersModPowReductionCompatibility X ℓ E n).inv.app L =
      (Mod.extendScalars (integersModPowTransition X ℓ E n)).leftDerivedFunctor.map
          ((boundedConstructible _).ι.map t') ≫
        (boundedConstructibleIntegersModPowReductionTransitionIso ℓ E n X).hom.app L := by
  simp only [boundedConstructibleIntegersModPowReductionTransitionIso_hom_app,
    Mod.derivedExtendScalarsReduction, derivedReductionMap, Category.assoc, Iso.app_inv,
    Iso.app_hom, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.map_comp]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Category.id_comp]

end Condensed

end AlgebraicGeometry.ProEtale.CondensedRing
