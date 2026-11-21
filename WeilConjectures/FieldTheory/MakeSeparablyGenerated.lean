/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.FieldTheory.InseparableDegreeDrop
import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.FinTrdeg

/-!
# Making a finitely generated field extension separably generated

Source: Stacks Project, Algebra, Lemma Tag 04KM.

## Main statements

* `FieldExtension.exists_finitePurelyInseparable_separablyGenerated`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace FieldExtension

/-- A finitely generated field extension becomes separably generated after finite purely
inseparable extensions of the base and the extension: for `K/k` finitely generated there are
finite purely inseparable extensions `k'/k` and `K'/K` and a compatible map `k' → K'` making
`K'/k'` separably generated.
Source: Stacks Project, Algebra, Lemma Tag 04KM. -/
theorem exists_finitePurelyInseparable_separablyGenerated
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) :
    ∃ (k' : Type (max u v)) (hk' : Field k') (akk' : Algebra k k')
      (K' : Type (max u v)) (hK' : Field K') (aKK' : Algebra K K') (akK' : Algebra k' K'),
      letI := hk'
      letI := akk'
      letI := hK'
      letI := aKK'
      letI := akK'
      Module.Finite k k' ∧ IsPurelyInseparable k k' ∧
      Module.Finite K K' ∧ IsPurelyInseparable K K' ∧
      Algebra.IsSeparablyGenerated k' K' ∧
      (algebraMap k' K').comp (algebraMap k k') =
        (algebraMap K K').comp (algebraMap k K) := by
  classical
  have induction : ∀ n : ℕ, ∀ (l L : Type (max u v))
      [Field l] [Field L] [Algebra l L],
      (⊤ : IntermediateField l L).FG → ∀ s : Finset L,
      IsTranscendenceBasis l ((↑) : s → L) →
      ∀ (_ : Module.Finite (IntermediateField.adjoin l (s : Set L)) L),
      Field.finInsepDegree (IntermediateField.adjoin l (s : Set L)) L = n →
      ∃ (l' : Type (max u v)) (hl' : Field l') (all' : Algebra l l')
        (L' : Type (max u v)) (hL' : Field L') (aLL' : Algebra L L')
        (alL' : Algebra l' L') (al0L' : Algebra l L')
        (htl : IsScalarTower l l' L') (htL : IsScalarTower l L L'),
        Module.Finite l l' ∧ IsPurelyInseparable l l' ∧
        Module.Finite L L' ∧ IsPurelyInseparable L L' ∧
        Algebra.IsSeparablyGenerated l' L' := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l L hl hL alL hfgL s hs hfin hn
      by_cases hsep : Field.finInsepDegree (IntermediateField.adjoin l (s : Set L)) L = 1
      · have hseparable : Algebra.IsSeparable (IntermediateField.adjoin l (s : Set L)) L :=
          (isSeparable_iff_finInsepDegree_eq_one _ _).mpr hsep
        exact ⟨l, hl, inferInstance, L, hL, inferInstance, alL, alL,
          inferInstance, inferInstance, inferInstance, inferInstance,
          inferInstance, inferInstance, (s : Set L), hs, hseparable⟩
      · obtain ⟨l₁, hl₁, all₁, L₁, hL₁, aLL₁, al₁L₁, alL₁, htl₁, htL₁,
          hfinl₁, hpurel₁, hfinL₁, hpureL₁, hfg₁, t, ht, hfint, hdrop⟩ :=
          exists_inseparableDegree_drop l L hfgL s hs hsep
        have hlt : Field.finInsepDegree (IntermediateField.adjoin l₁ (t : Set L₁)) L₁ < n :=
          hdrop.trans_eq hn
        obtain ⟨l₂, hl₂, al₁l₂, L₂, hL₂, aL₁L₂, al₂L₂, al₁L₂, ht₁₂, htL₁₂,
          hfinl₂, hpurel₂, hfinL₂, hpureL₂, hgen⟩ :=
          ih _ hlt l₁ L₁ hfg₁ t ht hfint rfl
        let all₂ : Algebra l l₂ := ((algebraMap l₁ l₂).comp (algebraMap l l₁)).toAlgebra
        let aLL₂ : Algebra L L₂ := ((algebraMap L₁ L₂).comp (algebraMap L L₁)).toAlgebra
        let alL₂ : Algebra l L₂ := ((algebraMap l₁ L₂).comp (algebraMap l l₁)).toAlgebra
        have : IsScalarTower l l₁ l₂ := IsScalarTower.of_algebraMap_eq' rfl
        have : IsScalarTower L L₁ L₂ := IsScalarTower.of_algebraMap_eq' rfl
        have : IsScalarTower l l₁ L₂ := IsScalarTower.of_algebraMap_eq' rfl
        have towerl : IsScalarTower l l₂ L₂ := by
          apply IsScalarTower.of_algebraMap_eq'
          ext x
          exact congrArg (fun f : l₁ →+* L₂ ↦ f (algebraMap l l₁ x)) ht₁₂.algebraMap_eq
        have towerL : IsScalarTower l L L₂ := by
          apply IsScalarTower.of_algebraMap_eq'
          ext x
          change algebraMap l₁ L₂ (algebraMap l l₁ x) =
            algebraMap L₁ L₂ (algebraMap L L₁ (algebraMap l L x))
          rw [← IsScalarTower.algebraMap_apply l L L₁,
            IsScalarTower.algebraMap_apply l l₁ L₁,
            ← IsScalarTower.algebraMap_apply l₁ L₁ L₂]
        exact ⟨l₂, hl₂, all₂, L₂, hL₂, aLL₂, al₂L₂, alL₂, towerl, towerL,
          Module.Finite.trans l₁ l₂, IsPurelyInseparable.trans l l₁ l₂,
          Module.Finite.trans L₁ L₂, IsPurelyInseparable.trans L L₁ L₂, hgen⟩
  let k₀ := ULift.{v} k
  let K₀ := ULift.{u} K
  let : Algebra k₀ k := ULift.algebra' _ _
  let : Algebra k₀ K := ULift.algebra' _ _
  let : Algebra k₀ K₀ := ULift.algebra' _ _
  have : IsScalarTower k₀ k K₀ := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp hfg
  have : Algebra.EssFiniteType k K₀ :=
    Algebra.EssFiniteType.of_surjective (ULift.algEquiv (R := k)).symm.toAlgHom
      (ULift.algEquiv (R := k)).symm.surjective
  have : Algebra.EssFiniteType k₀ k :=
    Algebra.EssFiniteType.of_surjective (IsScalarTower.toAlgHom k₀ k₀ k)
      ULift.down_surjective
  have : Algebra.EssFiniteType k₀ K₀ := Algebra.EssFiniteType.comp k₀ k K₀
  have hfg₀ : (⊤ : IntermediateField k₀ K₀).FG := IntermediateField.fg_top_iff.mpr
    (inferInstance : Algebra.EssFiniteType k₀ K₀)
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis k₀ K₀
  have : Algebra.IsAlgebraic (IntermediateField.adjoin k₀ (s : Set K₀)) K₀ := by
    convert! hs.isAlgebraic_field <;> simp
  have : Algebra.EssFiniteType (IntermediateField.adjoin k₀ (s : Set K₀)) K₀ :=
    Algebra.EssFiniteType.of_comp k₀ _ K₀
  have : Module.Finite (IntermediateField.adjoin k₀ (s : Set K₀)) K₀ :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  obtain ⟨k', hk', a₀k', K', hK', a₀K', akK', a₀K0', htk, htK,
      hfin, hpure, hfinK, hpureK, hgen⟩ := induction _ k₀ K₀ hfg₀ s hs inferInstance rfl
  let : Module k₀ k' := @Algebra.toModule k₀ k' _ _ a₀k'
  let : Module K₀ K' := @Algebra.toModule K₀ K' _ _ a₀K'
  let : SMul k₀ k' := a₀k'.toSMul
  let : SMul K₀ K' := a₀K'.toSMul
  let : SMul k₀ K' := a₀K0'.toSMul
  let akk' : Algebra k k' := ((algebraMap k₀ k').comp (algebraMap k k₀)).toAlgebra
  let aKK' : Algebra K K' := ((algebraMap K₀ K').comp (algebraMap K K₀)).toAlgebra
  let akK0' : Algebra k K' := ((algebraMap k₀ K').comp (algebraMap k k₀)).toAlgebra
  have : IsScalarTower k k₀ k' :=
    IsScalarTower.of_algebraMap_eq' (R := k) (S := k₀) (A := k') rfl
  have : IsScalarTower K K₀ K' :=
    IsScalarTower.of_algebraMap_eq' (R := K) (S := K₀) (A := K') rfl
  have : Module.Finite k k₀ := Module.Finite.of_surjective
    (ULift.algEquiv (R := k)).symm.toLinearMap (ULift.algEquiv (R := k)).symm.surjective
  have : Module.Finite K K₀ := Module.Finite.of_surjective
    (ULift.algEquiv (R := K)).symm.toLinearMap (ULift.algEquiv (R := K)).symm.surjective
  have : IsPurelyInseparable k k₀ := (ULift.algEquiv (R := k)).symm.isPurelyInseparable
  have : IsPurelyInseparable K K₀ := (ULift.algEquiv (R := K)).symm.isPurelyInseparable
  have : Module.Finite k₀ k' := hfin
  have : Module.Finite K₀ K' := hfinK
  refine ⟨k', hk', akk', K', hK', aKK', akK', Module.Finite.trans k₀ k',
    IsPurelyInseparable.trans k k₀ k', Module.Finite.trans K₀ K',
    IsPurelyInseparable.trans K K₀ K', hgen, ?_⟩
  ext x
  change algebraMap k' K' (algebraMap k₀ k' (ULift.up x)) =
    algebraMap K₀ K' (ULift.up (algebraMap k K x))
  rw [← IsScalarTower.algebraMap_apply k₀ k' K',
    IsScalarTower.algebraMap_apply k₀ K₀ K']
  rfl

end FieldExtension
