/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionNakayama
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.UpperStarPreservesLimits

/-!
# Derived complete `𝒪_E`-complexes in the condensed formalism

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and residue field
`𝔽_E`. A complex `K` of `𝒪_{E,X}`-module objects on `X_proét` is *derived complete*
(`ProEtale.derivedCompleteIntegers`) if every morphism to `K` from a complex `Z` whose first
derived reduction `Z ⊗ᴸ 𝔽_E` vanishes, i.e. on which a uniformizer acts invertibly, is zero
(Bhatt–Scholze, §3.4 and §6.5; Stacks, Tag 091N).

## Main results

- `ProEtale.isZero_of_derivedCompleteIntegers_of_isZero_derivedReduction`: **derived
  Nakayama**, a derived complete complex with vanishing first derived reduction is zero.
- `ProEtale.derivedCompleteIntegers_ext₂`: derived complete complexes are closed under
  extensions.
- `ProEtale.derivedCompleteIntegers_rightDerivedLowerStar_obj`: `Rf_*` preserves derived
  complete complexes.
- `ProEtale.derivedCompleteIntegers_leftDerivedUpperStar_obj`: `Lf^*` preserves derived
  complete complexes, for a morphism of quasi-compact quasi-separated schemes. The pullback
  commutes with derived limits, since it preserves countable products
  (`ProEtale.preservesLimitsOfSize_upperStar_ab`), and `K` is derived complete if and only if
  the derived limit of `⋯ --ϖ--> K --ϖ--> K` vanishes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

/-- A complex `K` of `𝒪_{E,X}`-module objects is **derived complete** if every morphism to `K`
from a complex `Z` with vanishing first derived reduction `Z ⊗ᴸ 𝔽_E` is zero. -/
def derivedCompleteIntegers (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) :=
  fun K ↦ ∀ ⦃Z⦄, IsZero ((derivedReduction X ℓ E).obj Z) → ∀ f : Z ⟶ K, f = 0

variable {ℓ E}

/-- **Derived Nakayama**: a derived complete complex whose first derived reduction vanishes is
zero. -/
theorem isZero_of_derivedCompleteIntegers_of_isZero_derivedReduction {X : Scheme.{u}}
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK : derivedCompleteIntegers ℓ E X K) (h : IsZero ((derivedReduction X ℓ E).obj K)) :
    IsZero K :=
  (IsZero.iff_id_eq_zero K).2 (hK h (𝟙 K))

/-- The first derived reduction of a complex vanishes if and only if its derived extension of
scalars along `𝒪_{E,X} ⟶ 𝔽_{E,X}` vanishes. -/
lemma isZero_derivedReduction_iff {X : Scheme.{u}}
    (Z : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) :
    IsZero ((derivedReduction X ℓ E).obj Z) ↔
      IsZero ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj Z) := by
  refine ⟨fun h ↦ ?_, fun h ↦ (residueFieldModuleSheaf X ℓ E).mapDerivedCategory.map_isZero h⟩
  have h0 : IsZero ((derivedReduction X ℓ E).obj 0) :=
    (derivedReduction X ℓ E).map_isZero (isZero_zero _)
  have := isIso_leftDerivedFunctor_map_of_isIso_derivedReduction_map X ℓ E (0 : Z ⟶ 0)
    (isIso_of_source_target_iso_zero _ h.isoZero h0.isoZero)
  exact ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map_isZero
    (isZero_zero _)).of_iso (asIso
      ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map (0 : Z ⟶ 0)))

/-- Complexes with vanishing first derived reduction are closed under shifts. -/
lemma isZero_derivedReduction_shift {X : Scheme.{u}}
    {Z : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hZ : IsZero ((derivedReduction X ℓ E).obj Z)) (n : ℤ) :
    IsZero ((derivedReduction X ℓ E).obj (Z⟦n⟧)) := by
  rw [isZero_derivedReduction_iff] at hZ ⊢
  exact ((shiftFunctor _ n).map_isZero hZ).of_iso
    (((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.commShiftIso
      n).app Z)

/-- Derived complete complexes are closed under extensions: in a distinguished triangle whose
first and third objects are derived complete, so is the second. -/
theorem derivedCompleteIntegers_ext₂ {X : Scheme.{u}}
    (T : Triangle (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))))
    (hT : T ∈ distTriang _) (h₁ : derivedCompleteIntegers ℓ E X T.obj₁)
    (h₃ : derivedCompleteIntegers ℓ E X T.obj₃) : derivedCompleteIntegers ℓ E X T.obj₂ := by
  intro Z hZ f
  obtain ⟨g, rfl⟩ := Triangle.coyoneda_exact₂ T hT f (h₃ hZ _)
  rw [h₁ hZ g, zero_comp]

/-- Derived complete complexes are closed under shifts. -/
theorem derivedCompleteIntegers_shift {X : Scheme.{u}}
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK : derivedCompleteIntegers ℓ E X K) (n : ℤ) :
    derivedCompleteIntegers ℓ E X (K⟦n⟧) := by
  intro Z hZ f
  have h := hK (isZero_derivedReduction_shift hZ (-n)) (f⟦-n⟧' ≫
    (shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).hom.app K)
  rw [← cancel_mono ((shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).inv.app K),
    Category.assoc, Iso.hom_inv_id_app, Category.comp_id, zero_comp] at h
  exact (shiftFunctor _ (-n)).map_injective (by rw [h, Functor.map_zero])

/-- **Derived Nakayama for morphisms**: a morphism of derived complete complexes whose first
derived reduction is an isomorphism is an isomorphism (blueprint `sk-lem-pe-derived-nakayama`):
its cone is derived complete, with vanishing first derived reduction. -/
theorem isIso_of_derivedCompleteIntegers_of_isIso_derivedReduction_map {X : Scheme.{u}}
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))} (φ : K ⟶ L)
    (hK : derivedCompleteIntegers ℓ E X K) (hL : derivedCompleteIntegers ℓ E X L)
    (h : IsIso ((derivedReduction X ℓ E).map φ)) : IsIso φ := by
  obtain ⟨C, g, δ, hT⟩ := distinguished_cocone_triangle φ
  have hF := (Mod.extendScalars
    (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map_distinguished _ hT
  have := isIso_leftDerivedFunctor_map_of_isIso_derivedReduction_map X ℓ E _ h
  have hC : derivedCompleteIntegers ℓ E X C :=
    derivedCompleteIntegers_ext₂ _ (rot_of_distTriang _ hT) hL (derivedCompleteIntegers_shift hK 1)
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_derivedCompleteIntegers_of_isZero_derivedReduction hC ?_)
  rw [isZero_derivedReduction_iff]
  exact (Triangle.isZero₃_iff_isIso₁ _ hF).2 this

/-- The derived pushforward `Rf_*` preserves derived complete complexes: it is right adjoint to
`Lf^*`, which commutes with the first derived reduction. -/
theorem derivedCompleteIntegers_rightDerivedLowerStar_obj {W X : Scheme.{u}} (f : W ⟶ X)
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) W))}
    (hK : derivedCompleteIntegers ℓ E W K) :
    derivedCompleteIntegers ℓ E X
      ((R((f)_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K) := by
  intro Z hZ g
  have hZ' : IsZero ((derivedReduction W ℓ E).obj
      ((L((f)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj Z)) := by
    rw [isZero_derivedReduction_iff] at hZ ⊢
    exact ((L((f)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map_isZero hZ).of_iso
      ((CondensedRing.derivedUpperStarExtendScalarsIso
        (Profinite.padicIntegersRingObjToResidueField ℓ E.1) f).app Z)
  have := hK hZ' (((derivedUpperStarLowerStarAdjunction _ f).homEquiv _ _).symm g)
  rwa [Equiv.symm_apply_eq, Adjunction.homEquiv_apply, Functor.map_zero, comp_zero] at this

/-- The derived pullback `Lf^*` along a morphism of quasi-compact quasi-separated schemes
preserves derived complete complexes: it commutes with the derived limit of
`⋯ --ϖ--> K --ϖ--> K`, whose vanishing characterizes derived complete complexes. -/
theorem derivedCompleteIntegers_leftDerivedUpperStar_obj {W X : Scheme.{u}} (f : W ⟶ X)
    [CompactSpace W] [QuasiSeparatedSpace W] [CompactSpace X] [QuasiSeparatedSpace X]
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK : derivedCompleteIntegers ℓ E X K) :
    derivedCompleteIntegers ℓ E W
      ((L((f)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K) :=
  sorry

end AlgebraicGeometry.ProEtale
