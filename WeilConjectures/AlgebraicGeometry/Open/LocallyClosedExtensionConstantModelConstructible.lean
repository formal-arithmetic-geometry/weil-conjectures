/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import all WeilConjectures.AlgebraicGeometry.Open.OpenExtensionConstantModelConstructible
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback

/-!
# Extension by zero from a locally closed subscheme and finite constant models

Let `X` be a noetherian scheme, `i : Z ⟶ X` a closed immersion and `j : T ⟶ Z` an open
immersion. If a module `M` on `T` has a finite constant local model, then `i_* j_! M` is
constructible with finite constant scalar models: it is stratified by the three locally closed
strata `T`, `Z \ T` and `X \ Z`, on which its pullback is `M`, `0` and `0` respectively.

We also record that locally free modules of finite rank have finite constant local models.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A property of three morphisms into `X` holds for every member of the family
`![Over.mk a, Over.mk b, Over.mk c]`. -/
private lemma forall_fin_three_over {X A B C : Scheme.{u}}
    (P : (Y : Scheme.{u}) → (Y ⟶ X) → Prop) (a : A ⟶ X) (b : B ⟶ X) (c : C ⟶ X)
    (ha : P A a) (hb : P B b) (hc : P C c) (k : Fin 3) :
    P (![Over.mk a, Over.mk b, Over.mk c] k).left (![Over.mk a, Over.mk b, Over.mk c] k).hom := by
  fin_cases k
  · exact ha
  · exact hb
  · exact hc

/-- On a noetherian scheme, three immersions with pairwise disjoint images covering `X` form a
stratification; a property of all three of them holds for every stratum. -/
private lemma exists_stratification_of_three {X A B C : Scheme.{u}} [IsNoetherian X]
    (P : (Y : Scheme.{u}) → (Y ⟶ X) → Prop)
    (a : A ⟶ X) (b : B ⟶ X) (c : C ⟶ X) [IsImmersion a] [IsImmersion b] [IsImmersion c]
    (hcover : ∀ x, x ∈ Set.range a ∨ x ∈ Set.range b ∨ x ∈ Set.range c)
    (hab : Disjoint (Set.range a) (Set.range b)) (hac : Disjoint (Set.range a) (Set.range c))
    (hbc : Disjoint (Set.range b) (Set.range c))
    (ha : P A a) (hb : P B b) (hc : P C c) :
    ∃ R : Scheme.Stratification X, ∀ k, P (R.domain k) (R.immersion k) := by
  let S : Fin 3 → Over X := ![Over.mk a, Over.mk b, Over.mk c]
  have himm (k : Fin 3) : IsImmersion (S k).hom := by
    fin_cases k
    · exact inferInstanceAs (IsImmersion a)
    · exact inferInstanceAs (IsImmersion b)
    · exact inferInstanceAs (IsImmersion c)
  refine ⟨Scheme.Stratification.ofNoetherianSpace 3 (fun k ↦ Set.range (S k).hom)
    (fun k ↦ (S k).hom.isLocallyClosed_range) ?_ ?_ (fun k ↦ (S k).left)
    (fun k ↦ (S k).hom) himm (fun _ ↦ rfl), forall_fin_three_over P a b c ha hb hc⟩
  · refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ?_
    rcases hcover x with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · intro k l hkl
    fin_cases k <;> fin_cases l
    all_goals first
      | exact absurd rfl hkl
      | exact hab | exact hac | exact hbc
      | exact hab.symm | exact hac.symm | exact hbc.symm

/-- If `X` is noetherian, `i : Z ⟶ X` is a closed immersion, `j : T ⟶ Z` is an open immersion
and `M` has a finite constant local model on `T`, then `i_* j_! M` is constructible with finite
constant scalar models. It is stratified by `T`, `Z \ T` and `X \ Z`, on which its pullbacks
are `M`, `0` and `0`. -/
theorem isConstantModelConstructible_lowerStar_openImmersionLowerShriek
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Z T : Scheme.{u}} [IsNoetherian X] (i : Z ⟶ X) (j : T ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hM : HasFiniteConstantLocalModel Λ T M) :
    IsConstantModelConstructible Λ X ((CondensedRing.lowerStar Λ i).obj
      ((CondensedRing.openImmersionLowerShriek Λ j).obj M)) := by
  let N := (CondensedRing.openImmersionLowerShriek Λ j).obj M
  let U : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hc := CondensedRing.moduleCounitOfAbelian Λ i (abelian_closed_counit i)
  let eZ : (CondensedRing.upperStar Λ i).obj ((CondensedRing.lowerStar Λ i).obj N) ≅ N :=
    asIso ((CondensedRing.upperStarLowerStarAdjunction Λ i).counit.app N)
  have hu := CondensedRing.open_unit_isIso Λ j
  let eT : (CondensedRing.upperStar Λ j).obj N ≅ M :=
    (asIso ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).unit.app M)).symm
  refine constant_constructible_of_models Λ _
    (exists_stratification_of_three (X := X) (fun Y f ↦ HasFiniteConstantLocalModel Λ Y
      ((CondensedRing.upperStar Λ f).obj ((CondensedRing.lowerStar Λ i).obj N)))
      (j ≫ i) (j.closedComplement ≫ i) U.ι
      ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · intro x
    by_cases hx : x ∈ Set.range i
    · obtain ⟨z, rfl⟩ := hx
      by_cases hz : z ∈ Set.range j
      · obtain ⟨t, rfl⟩ := hz
        exact Or.inl ⟨t, rfl⟩
      · rw [← Set.mem_compl_iff, ← j.range_closedComplement] at hz
        obtain ⟨w, rfl⟩ := hz
        exact Or.inr (Or.inl ⟨w, rfl⟩)
    · exact Or.inr (Or.inr (by simpa [U] using hx))
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨t, rfl⟩ ⟨w, hw⟩
    have hjc : j.closedComplement w ∈ Set.range j.closedComplement.base := ⟨w, rfl⟩
    rw [j.range_closedComplement] at hjc
    exact hjc ⟨t, (i.isClosedEmbedding.injective (by simpa using hw)).symm⟩
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨t, rfl⟩ hx
    simp only [U, Scheme.Opens.range_ι] at hx
    exact hx ⟨j t, rfl⟩
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨w, rfl⟩ hx
    simp only [U, Scheme.Opens.range_ι] at hx
    exact hx ⟨j.closedComplement w, rfl⟩
  · exact constant_model_of_iso Λ
      ((CondensedRing.upperStarComp Λ j i).app _ ≪≫
        (CondensedRing.upperStar Λ j).mapIso eZ ≪≫ eT) hM
  · refine constant_model_of_isZero Λ _ ?_
    refine (module_pullback_lowerShriek_isZero Λ j j.closedComplement ?_ M).of_iso
      ((CondensedRing.upperStarComp Λ j.closedComplement i).app _ ≪≫
        (CondensedRing.upperStar Λ j.closedComplement).mapIso eZ)
    rw [j.range_closedComplement]
    exact Set.inter_compl_self _
  · exact constant_model_of_isZero Λ _
      (CondensedRing.openRestrictionPushforwardZero Λ i U.ι (by simp [U]) N)

/-- A locally free module of finite rank over `Λ_T` has a finite constant local model: on each
member of the trivializing cover it is `Λ^n`, the pullback from the point of the finitely
presented module `Λ^n`. -/
theorem IsLocallyFree.hasFiniteConstantLocalModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {T : Scheme.{u}} {M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (hM : IsLocallyFree (condensedRingObj Λ T) M) : HasFiniteConstantLocalModel Λ T M := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰, fun k ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := h𝒰 k
  have : PreservesColimitsOfSize.{u + 1, u + 1} (upperStarFromPoint (𝒰.X k)) :=
    (pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ (𝒰.X k)))).leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts (upperStarFromPoint (𝒰.X k)) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint (𝒰.X k)).Additive := Functor.additive_of_preservesBinaryBiproducts _
  let α := condensedPullbackHom Λ (𝒰.f k)
  refine ⟨Mod.finiteFree Λ n,
    ⟨n, 0, 0, ⟨(cokernelZeroIsoTarget (X := Mod.finiteFree Λ 0)).symm⟩⟩, ⟨?_⟩⟩
  exact (Mod.extendScalarsIsoComapInv α).app _ ≪≫ (Mod.comap (inv α)).mapIso e ≪≫
    finiteFree_comap (inv α) n ≪≫ (finiteFree_mapMod (upperStarFromPoint (𝒰.X k)) n).symm

end AlgebraicGeometry.ProEtale
