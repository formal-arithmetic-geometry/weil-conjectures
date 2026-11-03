/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Direct.DirectImageFinitenessInput
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeDirectImageConstructibility
import WeilConjectures.AlgebraicGeometry.SmoothPurity.SeparablyClosedTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeTorsionCohomologicalDimension

/-! # The direct-image finiteness input holds

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/
`thm-exc-direct-image-input-holds` (blueprint: thm-exc-direct-image-input-holds).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Over a separably closed field and with an integer invertible in the field, the two
clauses of the direct-image finiteness input hold.

Proof:
1. Replace the signed annihilator `N` by its positive absolute value: invertibility
in the field excludes zero, and changing sign preserves invertibility and annihilation.
Use the induced unit in the global sections of `Spec k` to obtain the coefficient
convention required by `thm-dg-finite-type-constructibility`.
Apply `AlgebraicGeometry.Etale.isBoundedConstructible_rightDerivedLowerStar_of_
finiteType_over_field`
to a finite-type morphism and a constructible sheaf in degree zero.  The definition
of bounded constructibility gives constructibility of every higher direct image.
2. For clause (2), let `K` be separably closed and `W` finite type over `K` of
dimension at most `d`. If `W` is empty, all its positive cohomology vanishes.
Otherwise its dimension is a natural number `e` with `e ≤ d`. Apply
`hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed` to `K` and then
`hasTorsionEtaleCohomologicalDimensionLE_of_finiteType` with `c = 0` and exact
dimension `e`, obtaining the bound `2 * e`. Since `2 * e ≤ 2 * d`, the defining
vanishing condition of `HasTorsionEtaleCohomologicalDimensionLE` gives vanishing
for every locally torsion abelian étale sheaf in every degree above `2 * d`.
Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/`
`thm-exc-direct-image-input-holds.md`
(blueprint: thm-exc-direct-image-input-holds). -/
theorem hasDirectImageFinitenessInput_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k] (N : ℤ) (hN : IsUnit (N : k))
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : ∀ a : Λ, N • a = 0) :
    HasDirectImageFinitenessInput k N hN Λ hΛ := by
  have hpos : 0 < N.natAbs := by
    apply Int.natAbs_pos.mpr
    intro h
    apply hN.ne_zero
    simp [h]
  have hcast : (N : Λ) = 0 := by
    simpa only [zsmul_eq_mul, mul_one] using hΛ 1
  have habs : (N.natAbs : Λ) = 0 ∧ IsUnit (N.natAbs : k) := by
    rcases Int.natAbs_eq N with h | h
    · rw [h] at hcast hN
      exact ⟨by simpa using hcast, by simpa using hN⟩
    · rw [h] at hcast hN
      exact ⟨by simpa using hcast, by simpa using hN⟩
  have hcoeff : Etale.IsSmoothBaseChangeCoefficients N.natAbs Λ (Spec (.of k)) := by
    refine ⟨hpos, inferInstance, habs.1, ?_⟩
    simpa using habs.2.map (ΓSpecIso (.of k)).inv.hom
  constructor
  · intro S T aS aT _ _ _ _ uST _ _ hu F hF q
    have : IsConstructibleSheaf F :=
      (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).1 hF
    have hs := Etale.DerivedCategory.boundedConstructible_singleFunctor_obj F 0
    have hsingle : Etale.DerivedCategory.isBoundedConstructible Λ S
        ((DerivedCategory.singleFunctor _ 0).obj F) := by
      refine ⟨fun i ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hs.2 i),
        0, 0, le_rfl, fun i hi ↦ ?_⟩
      rcases hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE _ 0 i hi
      · exact DerivedCategory.isZero_of_isLE _ 0 i hi
    exact (Etale.isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field
      k Λ N.natAbs hcoeff aS aT uST hu _ hsingle).1 (q : ℤ)
  · intro d K _ _ _ W aW _ _ hd
    let : W.Over (Spec (.of K)) := ⟨aW⟩
    have : LocallyOfFiniteType (W ↘ Spec (.of K)) :=
      inferInstanceAs (LocallyOfFiniteType aW)
    have : QuasiCompact (W ↘ Spec (.of K)) := inferInstanceAs (QuasiCompact aW)
    cases isEmpty_or_nonempty W with
    | inl hW =>
      intro F _ q _
      have : (Etale.rightDerivedGlobalSections AddCommGrpCat.{u + 1} W).Additive :=
        inferInstanceAs ((Sheaf.Γ W.smallEtaleTopology
          AddCommGrpCat.{u + 1}).rightDerivedFunctor.Additive)
      have : (Etale.cohomology AddCommGrpCat.{u + 1} W q).Additive :=
        inferInstanceAs ((_ ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1}
          (q : ℤ)).Additive)
      apply AddCommGrpCat.isZero_iff_subsingleton.mp
      exact (Etale.cohomology AddCommGrpCat.{u + 1} W q).map_isZero
        ((DerivedCategory.singleFunctor _ 0).map_isZero
          (Scheme.Etale.isZero_sheaf_of_isEmpty F))
    | inr hW =>
      have hbot : topologicalKrullDim W ≠ ⊥ := by
        rw [topologicalKrullDim, Ne, Order.krullDim_eq_bot_iff, not_isEmpty_iff]
        obtain ⟨x⟩ := hW
        exact ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
      obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hbot
      have hmle : m ≤ (d : ℕ∞) := by exact_mod_cast hm.trans_le hd
      have hmtop : m ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) hmle
      obtain ⟨e, rfl⟩ := ENat.ne_top_iff_exists.mp hmtop
      have he : e ≤ d := by exact_mod_cast hmle
      have hbound := hasTorsionEtaleCohomologicalDimensionLE_of_finiteType K 0 e
        (hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed K) W hm.symm
      intro F hF q hq
      exact hbound F hF q (by omega)

end AlgebraicGeometry.Scheme

end
