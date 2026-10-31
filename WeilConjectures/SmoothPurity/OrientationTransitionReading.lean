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
    Iso.app_hom, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]

end Condensed

section Reading

variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- An elementary transport: if `s ≫ μ₂ = μ₁ ≫ G g` and `ω₁ ≫ u = g ≫ ω₂`, then
`s ≫ μ₂ ≫ G ω₂ = (μ₁ ≫ G ω₁) ≫ G u`. -/
lemma _root_.CategoryTheory.Functor.comp_comp_map_eq_comp_map_comp_map {C D : Type*} [Category C]
    [Category D] (G : C ⥤ D) {x₁ x₂ : D} {a₁ a₂ b₁ b₂ : C} {μ₁ : x₁ ⟶ G.obj a₁}
    {μ₂ : x₂ ⟶ G.obj a₂} {ω₁ : a₁ ⟶ b₁} {ω₂ : a₂ ⟶ b₂} {s : x₁ ⟶ x₂} (g : a₁ ⟶ a₂) {u : b₁ ⟶ b₂}
    (hnat : s ≫ μ₂ = μ₁ ≫ G.map g) (hA : ω₁ ≫ u = g ≫ ω₂) :
    s ≫ μ₂ ≫ G.map ω₂ = (μ₁ ≫ G.map ω₁) ≫ G.map u := by
  rw [reassoc_of% hnat, ← G.map_comp, ← hA, G.map_comp, Category.assoc]

/-- Blueprint `det-sp-purity-coefficient-change` (lifting criterion). **The condensed reduction
of a morphism `t' : red_{n+1} K ⟶ red_{n+1} L` is a given `t : red_n K ⟶ red_n L` as soon as this
holds on the étale site**: if, through the isomorphisms `β : Ψ(red_{n+1} -) ≅ red_n -`
(`etaleReductionExtendScalarsIsoApp`, the components of `etaleReductionExtendScalarsIso`), `Ψ` of
the étale reading of `t'` is the étale reading of `t`, then
`(𝒪_E ⧸ ℓⁿ) ⊗ᴸ_{𝒪_E ⧸ ℓⁿ⁺¹} t' = t` in the ambient derived category. Indeed `β` is natural and
built from the condensed transition, and the étale reading is faithful. -/
theorem derivedExtendScalarsReduction_derivedReductionMap_eq_of_comp
    {K L : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧}
    (t' : (boundedConstructibleIntegersModPowReduction X.left ℓ E (n + 1)).obj K ⟶
      (boundedConstructibleIntegersModPowReduction X.left ℓ E (n + 1)).obj L)
    (t : (boundedConstructibleIntegersModPowReduction X.left ℓ E n).obj K ⟶
      (boundedConstructibleIntegersModPowReduction X.left ℓ E n).obj L)
    (h : (integersModPowDerivedExtendScalars ℓ E n X.left).map
          ((finiteEtaleReading ℓ E (n + 1) X).map t') ≫
        (etaleReductionExtendScalarsIsoApp ℓ E n X L).hom =
      (etaleReductionExtendScalarsIsoApp ℓ E n X K).hom ≫ (finiteEtaleReading ℓ E n X).map t) :
    Mod.derivedExtendScalarsReduction _ (integersModPowTransition X.left ℓ E n) _
        (integersModPowReduction_comp_integersModPowTransition X.left ℓ E n)
        (derivedReductionMap ℓ E (n + 1) X.left t') =
      derivedReductionMap ℓ E n X.left t := by
  -- `u : red_n K ⟶ red_n L`, the condensed reduction of `t'` read between the reductions
  let u := (boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).hom.app K ≫
    Mod.derivedExtendScalarsReduction _ (integersModPowTransition X.left ℓ E n) _
      (integersModPowReduction_comp_integersModPowTransition X.left ℓ E n)
      (derivedReductionMap ℓ E (n + 1) X.left t') ≫
    (boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).inv.app L
  let t₀ := (ObjectProperty.fullyFaithfulι _).preimage u
  have ht₀ : (boundedConstructible _).ι.map t₀ = u :=
    (ObjectProperty.fullyFaithfulι _).map_preimage u
  have key :=
    ((finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).functor ⋙
      R(ν_*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])
      ).comp_comp_map_eq_comp_map_comp_map
    ((Mod.extendScalars (integersModPowTransition X.left ℓ E n)).leftDerivedFunctor.map
      ((boundedConstructible _).ι.map t'))
    ((finiteEtaleReadingExtendScalarsMap ℓ E n X).naturality t')
    (boundedConstructibleIntegersModPowReductionTransitionIso_hom_app_comp ℓ E n X.left t')
  have key₂ : (etaleReductionExtendScalarsIsoApp ℓ E n X K).hom ≫
      ((finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).functor ⋙
        R(ν_*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])).map u =
      (etaleReductionExtendScalarsIsoApp ℓ E n X K).hom ≫ (finiteEtaleReading ℓ E n X).map t :=
    calc _ = _ := by rw [etaleReductionExtendScalarsIsoApp_hom ℓ E n X K]
      _ = _ := key.symm
      _ = (integersModPowDerivedExtendScalars ℓ E n X.left).map
            ((finiteEtaleReading ℓ E (n + 1) X).map t') ≫
          (etaleReductionExtendScalarsIsoApp ℓ E n X L).hom := by
        rw [etaleReductionExtendScalarsIsoApp_hom ℓ E n X L]
        rfl
      _ = _ := h
  have key₃ : (etaleReductionExtendScalarsIsoApp ℓ E n X K).hom ≫
      (finiteEtaleReading ℓ E n X).map t₀ =
      (etaleReductionExtendScalarsIsoApp ℓ E n X K).hom ≫ (finiteEtaleReading ℓ E n X).map t :=
    (congrArg (fun g ↦ (etaleReductionExtendScalarsIsoApp ℓ E n X K).hom ≫
      ((finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).functor ⋙
        R(ν_*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])).map g) ht₀).trans key₂
  have ht : t₀ = t :=
    (finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E n X)).map_injective
      ((cancel_epi (etaleReductionExtendScalarsIsoApp ℓ E n X K).hom).1 key₃)
  calc _ = ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app K).inv ≫
        u ≫
          ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app L).hom := by
        simp only [u, Iso.app_inv, Iso.app_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
          Iso.inv_hom_id_app]
        exact (Category.comp_id _).symm
    _ = ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app K).inv ≫
        (boundedConstructible _).ι.map t₀ ≫
          ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app L).hom :=
        congrArg (fun g ↦
          ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app K).inv ≫
            g ≫ ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app
              L).hom) ht₀.symm
    _ = _ :=
        congrArg (fun g ↦
          ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app K).inv ≫
            (boundedConstructible _).ι.map g ≫
            ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app L).hom) ht

end Reading

end AlgebraicGeometry.ProEtale.CondensedRing
